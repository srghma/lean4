// Lean compiler output
// Module: Init.Data.Array.Basic
// Imports: Init.Control.Do Init.GetElem Init.Data.List.ToArrayImpl Init.Data.List.ToArrayImpl Init.Data.Array.Set Init.Data.Array.Set Init.WF Init.MetaTypes Init.WFTactics
use crate::r#gen::Init::Control::Do::{
    initialize_Init_Control_Do, runtime_initialize_Init_Control_Do,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Set::{
    initialize_Init_Data_Array_Set, runtime_initialize_Init_Data_Array_Set,
};
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_fill, l_Std_Format_joinSep___redArg};
use crate::r#gen::Init::Data::List::ToArrayImpl::{
    initialize_Init_Data_List_ToArrayImpl, runtime_initialize_Init_Data_List_ToArrayImpl,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_repr};
use crate::r#gen::Init::GetElem::{initialize_Init_GetElem, runtime_initialize_Init_GetElem};
use crate::r#gen::Init::MetaTypes::{initialize_Init_MetaTypes, meta_initialize_Init_MetaTypes};
use crate::r#gen::Init::Prelude::{
    l_Array_appendCore___redArg, l_Array_extract___redArg, l_Array_mkArray0, l_Lean_Name_mkStr1,
    l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_addMacroScope, l_Lean_mkAtom, l_String_toRawSubstring_x27,
    l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::WF::{initialize_Init_WF, runtime_initialize_Init_WF};
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{
    lean_string_append, lean_string_length,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_box_usize, lean_closure_set,
    lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l_term_x23_x5b___x2c_x5d___closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 101, 114, 109, 35, 91, 95, 44, 93, 0],
};
static mut l_term_x23_x5b___x2c_x5d___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__0_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__0_value) as *mut LeanObject,
        17856333342802343749 as *mut LeanObject,
    ],
};
static mut l_term_x23_x5b___x2c_x5d___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__1_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [97, 110, 100, 116, 104, 101, 110, 0],
};
static mut l_term_x23_x5b___x2c_x5d___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__2_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__2_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_term_x23_x5b___x2c_x5d___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__3_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__4_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [35, 91, 0],
};
static mut l_term_x23_x5b___x2c_x5d___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__4_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__4_value) as *mut LeanObject],
};
static mut l_term_x23_x5b___x2c_x5d___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__5_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__6_value: LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        119, 105, 116, 104, 111, 117, 116, 80, 111, 115, 105, 116, 105, 111, 110, 0,
    ],
};
static mut l_term_x23_x5b___x2c_x5d___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__6_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__6_value) as *mut LeanObject,
        1164644006045091397 as *mut LeanObject,
    ],
};
static mut l_term_x23_x5b___x2c_x5d___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__7_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__8_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 101, 114, 109, 0],
};
static mut l_term_x23_x5b___x2c_x5d___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__8_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__8_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_term_x23_x5b___x2c_x5d___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__9_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__9_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_term_x23_x5b___x2c_x5d___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__10_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__11_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [44, 0],
};
static mut l_term_x23_x5b___x2c_x5d___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__11_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__12_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [44, 32, 0],
};
static mut l_term_x23_x5b___x2c_x5d___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__12_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__13_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__12_value) as *mut LeanObject],
};
static mut l_term_x23_x5b___x2c_x5d___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__13_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__14_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 10,
    },
    m_objs: [
        core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__11_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__13_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_term_x23_x5b___x2c_x5d___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__14_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__15_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_term_x23_x5b___x2c_x5d___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__15_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__15_value) as *mut LeanObject,
    ],
};
static mut l_term_x23_x5b___x2c_x5d___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__16_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__17_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [93, 0],
};
static mut l_term_x23_x5b___x2c_x5d___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__17_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__18_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__17_value) as *mut LeanObject],
};
static mut l_term_x23_x5b___x2c_x5d___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__18_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__19_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__16_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__18_value) as *mut LeanObject,
    ],
};
static mut l_term_x23_x5b___x2c_x5d___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__19_value) as *mut LeanObject;
pub static l_term_x23_x5b___x2c_x5d___closed__20_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__19_value) as *mut LeanObject,
    ],
};
static mut l_term_x23_x5b___x2c_x5d___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__20_value) as *mut LeanObject;
pub static mut l_term_x23_x5b___x2c_x5d: *mut LeanObject =
    core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__20_value) as *mut LeanObject;
pub static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__0_value) as *mut LeanObject;
pub static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1_value) as *mut LeanObject;
pub static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__2_value) as *mut LeanObject;
pub static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__3_value) as *mut LeanObject;
static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__3_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4_value) as *mut LeanObject;
pub static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__5_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 105, 115, 116, 46, 116, 111, 65, 114, 114, 97, 121, 0]};
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__5_value) as *mut LeanObject;
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__7_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 105, 115, 116, 0]};
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__7_value) as *mut LeanObject;
pub static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__8_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 111, 65, 114, 114, 97, 121, 0]};
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__8_value) as *mut LeanObject;
static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__7_value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
pub static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__8_value) as *mut LeanObject,8414467900391110369 as *mut LeanObject] };
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9_value) as *mut LeanObject;
pub static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__10_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__10_value) as *mut LeanObject;
pub static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__10_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__11_value) as *mut LeanObject;
pub static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__12_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__12_value) as *mut LeanObject;
pub static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__12_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13_value) as *mut LeanObject;
pub static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__14_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 91, 95, 93, 0]};
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__14_value) as *mut LeanObject;
pub static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__14_value) as *mut LeanObject,11666683425613976406 as *mut LeanObject] };
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__15_value) as *mut LeanObject;
pub static l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__16_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__16_value) as *mut LeanObject;
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_swap___auto__1___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Array_swap___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_swap___auto__1___closed__0_value) as *mut LeanObject;
pub static l_Array_swap___auto__1___closed__1_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Array_swap___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_swap___auto__1___closed__1_value) as *mut LeanObject;
static l_Array_swap___auto__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Array_swap___auto__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_swap___auto__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Array_swap___auto__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_swap___auto__1___closed__2_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_swap___auto__1___closed__0_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Array_swap___auto__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_swap___auto__1___closed__2_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_swap___auto__1___closed__1_value) as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_Array_swap___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Array_swap___auto__1___closed__2_value) as *mut LeanObject;
pub static l_Array_swap___auto__1___closed__3_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Array_swap___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Array_swap___auto__1___closed__3_value) as *mut LeanObject;
pub static l_Array_swap___auto__1___closed__4_value: LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Array_swap___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Array_swap___auto__1___closed__4_value) as *mut LeanObject;
static l_Array_swap___auto__1___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Array_swap___auto__1___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_swap___auto__1___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Array_swap___auto__1___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_swap___auto__1___closed__5_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_swap___auto__1___closed__0_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Array_swap___auto__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_swap___auto__1___closed__5_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_swap___auto__1___closed__4_value) as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l_Array_swap___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Array_swap___auto__1___closed__5_value) as *mut LeanObject;
pub static l_Array_swap___auto__1___closed__6_value: LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        116, 97, 99, 116, 105, 99, 71, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105,
        99, 0,
    ],
};
static mut l_Array_swap___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Array_swap___auto__1___closed__6_value) as *mut LeanObject;
pub static l_Array_swap___auto__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_swap___auto__1___closed__6_value) as *mut LeanObject,
        3731765604234633101 as *mut LeanObject,
    ],
};
static mut l_Array_swap___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Array_swap___auto__1___closed__7_value) as *mut LeanObject;
pub static l_Array_swap___auto__1___closed__8_value: LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        103, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105, 99, 0,
    ],
};
static mut l_Array_swap___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Array_swap___auto__1___closed__8_value) as *mut LeanObject;
static mut l_Array_swap___auto__1___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_swap___auto__1___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_swap___auto__1___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_swap___auto__1___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_swap___auto__1___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_swap___auto__1___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_swap___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_swap___auto__1___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_swap___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_swap___auto__1___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_swap___auto__1___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_swap___auto__1___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_swap___auto__1___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_swap___auto__1___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_swap___auto__1___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_swap___auto__1___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_swap___auto__1___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_swap___auto__1___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Array_swap___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Array_swap___auto__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_instGetElemUSizeLtNatToNatSize___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_instGetElemUSizeLtNatToNatSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_instGetElemUSizeLtNatToNatSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_instGetElemUSizeLtNatToNatSize___closed__0_value)
        as *mut LeanObject;
pub static l_Array_instEmptyCollection___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Array_instEmptyCollection___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_instEmptyCollection___closed__0_value) as *mut LeanObject;
pub static l_Array_range___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_range___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_range___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_range___closed__0_value) as *mut LeanObject;
pub static mut l_Array_back___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Array_swapAt___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_swapAt_x21___redArg___closed__0_value: LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 65, 114, 114, 97, 121, 46, 66, 97, 115, 105,
        99, 0,
    ],
};
static mut l_Array_swapAt_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_swapAt_x21___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_swapAt_x21___redArg___closed__1_value: LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [65, 114, 114, 97, 121, 46, 115, 119, 97, 112, 65, 116, 33, 0],
};
static mut l_Array_swapAt_x21___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_swapAt_x21___redArg___closed__1_value) as *mut LeanObject;
pub static l_Array_swapAt_x21___redArg___closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [105, 110, 100, 101, 120, 32, 0],
};
static mut l_Array_swapAt_x21___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Array_swapAt_x21___redArg___closed__2_value) as *mut LeanObject;
pub static l_Array_swapAt_x21___redArg___closed__3_value: LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        32, 111, 117, 116, 32, 111, 102, 32, 98, 111, 117, 110, 100, 115, 0,
    ],
};
static mut l_Array_swapAt_x21___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Array_swapAt_x21___redArg___closed__3_value) as *mut LeanObject;
pub static l_Array_findSomeM_x3f___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Array_findSomeM_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_findSomeM_x3f___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_findIdxM_x3f___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Array_findIdxM_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_findIdxM_x3f___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_foldl___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_foldl___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_foldl___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_foldl___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_foldl___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_foldl___redArg___closed__1_value) as *mut LeanObject;
pub static l_Array_foldl___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_foldl___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Array_foldl___redArg___closed__2_value) as *mut LeanObject;
pub static l_Array_foldl___redArg___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_foldl___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Array_foldl___redArg___closed__3_value) as *mut LeanObject;
pub static l_Array_foldl___redArg___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_foldl___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Array_foldl___redArg___closed__4_value) as *mut LeanObject;
pub static l_Array_foldl___redArg___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_foldl___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Array_foldl___redArg___closed__5_value) as *mut LeanObject;
pub static l_Array_foldl___redArg___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_foldl___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Array_foldl___redArg___closed__6_value) as *mut LeanObject;
pub static l_Array_foldl___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_foldl___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_foldl___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Array_foldl___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Array_foldl___redArg___closed__7_value) as *mut LeanObject;
pub static l_Array_foldl___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_foldl___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_foldl___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_foldl___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_foldl___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_foldl___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Array_foldl___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Array_foldl___redArg___closed__8_value) as *mut LeanObject;
pub static l_Array_foldl___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_foldl___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_foldl___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Array_foldl___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Array_foldl___redArg___closed__9_value) as *mut LeanObject;
pub static l_Array_instFunctor___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_instFunctor___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_instFunctor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_instFunctor___closed__0_value) as *mut LeanObject;
pub static l_Array_instFunctor___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_map as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_instFunctor___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_instFunctor___closed__1_value) as *mut LeanObject;
pub static l_Array_instFunctor___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_instFunctor___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_instFunctor___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Array_instFunctor___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Array_instFunctor___closed__2_value) as *mut LeanObject;
pub static mut l_Array_instFunctor: *mut LeanObject =
    core::ptr::addr_of!(l_Array_instFunctor___closed__2_value) as *mut LeanObject;
pub static l_Array_findSome_x21___redArg___closed__0_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            65, 114, 114, 97, 121, 46, 102, 105, 110, 100, 83, 111, 109, 101, 33, 0,
        ],
    };
static mut l_Array_findSome_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_findSome_x21___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_findSome_x21___redArg___closed__1_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 105, 110, 100, 32, 101, 108, 101,
            109, 101, 110, 116, 0,
        ],
    };
static mut l_Array_findSome_x21___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_findSome_x21___redArg___closed__1_value) as *mut LeanObject;
static mut l_Array_findSome_x21___redArg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_findSome_x21___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_toListAppend___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_toListAppend___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_toListAppend___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toListAppend___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_instAppend___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_append___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Array_instAppend___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_instAppend___closed__0_value) as *mut LeanObject;
pub static l_Array_instHAppendList___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_appendList as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Array_instHAppendList___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_instHAppendList___closed__0_value) as *mut LeanObject;
pub static l_Array_flatten___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_append___redArg___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_flatten___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_flatten___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_filter___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Array_filter___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_filter___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_filterRevM___redArg___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_reverse as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Array_filterRevM___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_filterRevM___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_partition___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_filter___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_filter___redArg___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Array_partition___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_partition___redArg___closed__0_value) as *mut LeanObject;
pub static mut l_Array_eraseIdx___auto__1: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Array_eraseIdx_x21___redArg___closed__0_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            65, 114, 114, 97, 121, 46, 101, 114, 97, 115, 101, 73, 100, 120, 33, 0,
        ],
    };
static mut l_Array_eraseIdx_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_eraseIdx_x21___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_eraseIdx_x21___redArg___closed__1_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 105, 110, 100, 101, 120, 0,
        ],
    };
static mut l_Array_eraseIdx_x21___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_eraseIdx_x21___redArg___closed__1_value) as *mut LeanObject;
static mut l_Array_eraseIdx_x21___redArg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_eraseIdx_x21___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Array_insertIdx___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_insertIdx_x21___redArg___closed__0_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            65, 114, 114, 97, 121, 46, 105, 110, 115, 101, 114, 116, 73, 100, 120, 33, 0,
        ],
    };
static mut l_Array_insertIdx_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_insertIdx_x21___redArg___closed__0_value) as *mut LeanObject;
static mut l_Array_insertIdx_x21___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_insertIdx_x21___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_zip___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Array_zip___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_zip___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_reduceOption___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_reduceOption___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_reduceOption___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_reduceOption___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_repr___redArg___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__11_value) as *mut LeanObject],
};
static mut l_Array_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_repr___redArg___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_repr___redArg___closed__0_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Array_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___redArg___closed__1_value) as *mut LeanObject;
static mut l_Array_repr___redArg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_repr___redArg___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_repr___redArg___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__4_value) as *mut LeanObject],
};
static mut l_Array_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___redArg___closed__4_value) as *mut LeanObject;
pub static l_Array_repr___redArg___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_term_x23_x5b___x2c_x5d___closed__17_value) as *mut LeanObject],
};
static mut l_Array_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___redArg___closed__5_value) as *mut LeanObject;
pub static l_Array_repr___redArg___closed__6_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [35, 91, 93, 0],
};
static mut l_Array_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___redArg___closed__6_value) as *mut LeanObject;
pub static l_Array_repr___redArg___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Array_repr___redArg___closed__6_value) as *mut LeanObject],
};
static mut l_Array_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___redArg___closed__7_value) as *mut LeanObject;
pub unsafe fn _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6()
-> *mut LeanObject {
    let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut LeanObject = core::ptr::null_mut();
    v___x_4970_ =
        l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__5;
    v___x_4971_ = l_String_toRawSubstring_x27(v___x_4970_);
    return v___x_4971_;
}
pub unsafe fn _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17()
-> *mut LeanObject {
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    v___x_4990_ = l_Array_mkArray0(lean_box(0));
    return v___x_4990_;
}
pub unsafe fn l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1(
    mut v_x_4991_: *mut LeanObject,
    mut v_a_4992_: *mut LeanObject,
    mut v_a_4993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: u8 = 0;
    v___x_4994_ = l_term_x23_x5b___x2c_x5d___closed__1;
    lean_inc(v_x_4991_);
    v___x_4995_ = l_Lean_Syntax_isOfKind(v_x_4991_, v___x_4994_);
    if v___x_4995_ == 0 {
        let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4991_);
        v___x_4996_ = lean_box(1);
        v___x_4997_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4997_, 0, v___x_4996_);
        lean_ctor_set(v___x_4997_, 1, v_a_4993_);
        return v___x_4997_;
    } else {
        let mut v_quotContext_4998_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4999_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_5000_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5004_: u8 = 0;
        let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5007_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5009_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5016_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_4998_ = lean_ctor_get(v_a_4992_, 1);
        v_currMacroScope_4999_ = lean_ctor_get(v_a_4992_, 2);
        v_ref_5000_ = lean_ctor_get(v_a_4992_, 5);
        v___x_5001_ = lean_unsigned_to_nat(1);
        v___x_5002_ = l_Lean_Syntax_getArg(v_x_4991_, v___x_5001_);
        lean_dec(v_x_4991_);
        v___x_5003_ = l_Lean_Syntax_getArgs(v___x_5002_);
        lean_dec(v___x_5002_);
        v___x_5004_ = 0;
        v___x_5005_ = l_Lean_SourceInfo_fromRef(v_ref_5000_, v___x_5004_);
        v___x_5006_ = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4;
        v___x_5007_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6), core::ptr::addr_of_mut!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6_once), _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6);
        v___x_5008_ = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9;
        lean_inc(v_currMacroScope_4999_);
        lean_inc(v_quotContext_4998_);
        v___x_5009_ =
            l_Lean_addMacroScope(v_quotContext_4998_, v___x_5008_, v_currMacroScope_4999_);
        v___x_5010_ = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__11;
        lean_inc_n(v___x_5005_, 6);
        v___x_5011_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_5011_, 0, v___x_5005_);
        lean_ctor_set(v___x_5011_, 1, v___x_5007_);
        lean_ctor_set(v___x_5011_, 2, v___x_5009_);
        lean_ctor_set(v___x_5011_, 3, v___x_5010_);
        v___x_5012_ = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13;
        v___x_5013_ = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__15;
        v___x_5014_ = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__16;
        v___x_5015_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5015_, 0, v___x_5005_);
        lean_ctor_set(v___x_5015_, 1, v___x_5014_);
        v___x_5016_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17), core::ptr::addr_of_mut!(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17_once), _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17);
        v___x_5017_ = l_Array_appendCore___redArg(v___x_5016_, v___x_5003_);
        lean_dec_ref(v___x_5003_);
        v___x_5018_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_5018_, 0, v___x_5005_);
        lean_ctor_set(v___x_5018_, 1, v___x_5012_);
        lean_ctor_set(v___x_5018_, 2, v___x_5017_);
        v___x_5019_ = l_term_x23_x5b___x2c_x5d___closed__17;
        v___x_5020_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5020_, 0, v___x_5005_);
        lean_ctor_set(v___x_5020_, 1, v___x_5019_);
        v___x_5021_ = l_Lean_Syntax_node3(
            v___x_5005_,
            v___x_5013_,
            v___x_5015_,
            v___x_5018_,
            v___x_5020_,
        );
        v___x_5022_ = l_Lean_Syntax_node1(v___x_5005_, v___x_5012_, v___x_5021_);
        v___x_5023_ = l_Lean_Syntax_node2(v___x_5005_, v___x_5006_, v___x_5011_, v___x_5022_);
        v___x_5024_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5024_, 0, v___x_5023_);
        lean_ctor_set(v___x_5024_, 1, v_a_4993_);
        return v___x_5024_;
    }
}
pub unsafe fn l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___boxed(
    mut v_x_5025_: *mut LeanObject,
    mut v_a_5026_: *mut LeanObject,
    mut v_a_5027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5028_: *mut LeanObject = core::ptr::null_mut();
    v_res_5028_ = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1(
        v_x_5025_, v_a_5026_, v_a_5027_,
    );
    lean_dec_ref(v_a_5026_);
    return v_res_5028_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__List_toArrayAux_match__1_splitter___redArg(
    mut v_x_5029_: *mut LeanObject,
    mut v_x_5030_: *mut LeanObject,
    mut v_h__1_5031_: *mut LeanObject,
    mut v_h__2_5032_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5029_) == 0 {
        let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5032_);
        v___x_5033_ = lean_apply_1(v_h__1_5031_, v_x_5030_);
        return v___x_5033_;
    } else {
        let mut v_head_5034_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_5035_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5036_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5031_);
        v_head_5034_ = lean_ctor_get(v_x_5029_, 0);
        lean_inc(v_head_5034_);
        v_tail_5035_ = lean_ctor_get(v_x_5029_, 1);
        lean_inc(v_tail_5035_);
        lean_dec_ref_known(v_x_5029_, 2);
        v___x_5036_ = lean_apply_3(v_h__2_5032_, v_head_5034_, v_tail_5035_, v_x_5030_);
        return v___x_5036_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__List_toArrayAux_match__1_splitter(
    mut v_00_u03b1_5037_: *mut LeanObject,
    mut v_motive_5038_: *mut LeanObject,
    mut v_x_5039_: *mut LeanObject,
    mut v_x_5040_: *mut LeanObject,
    mut v_h__1_5041_: *mut LeanObject,
    mut v_h__2_5042_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5039_) == 0 {
        let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5042_);
        v___x_5043_ = lean_apply_1(v_h__1_5041_, v_x_5040_);
        return v___x_5043_;
    } else {
        let mut v_head_5044_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_5045_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5041_);
        v_head_5044_ = lean_ctor_get(v_x_5039_, 0);
        lean_inc(v_head_5044_);
        v_tail_5045_ = lean_ctor_get(v_x_5039_, 1);
        lean_inc(v_tail_5045_);
        lean_dec_ref_known(v_x_5039_, 2);
        v___x_5046_ = lean_apply_3(v_h__2_5042_, v_head_5044_, v_tail_5045_, v_x_5040_);
        return v___x_5046_;
    }
}
pub unsafe fn l_Array_instMembership(mut v_00_u03b1_5047_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5048_: *mut LeanObject = core::ptr::null_mut();
    v___x_5048_ = lean_box(0);
    return v___x_5048_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter___redArg(
    mut v_x_5049_: *mut LeanObject,
    mut v_h__1_5050_: *mut LeanObject,
    mut v_h__2_5051_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5049_) == 0 {
        let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5053_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5050_);
        v___x_5052_ = lean_box(0);
        v___x_5053_ = lean_apply_1(v_h__2_5051_, v___x_5052_);
        return v___x_5053_;
    } else {
        let mut v_val_5054_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5051_);
        v_val_5054_ = lean_ctor_get(v_x_5049_, 0);
        lean_inc(v_val_5054_);
        lean_dec_ref_known(v_x_5049_, 1);
        v___x_5055_ = lean_apply_1(v_h__1_5050_, v_val_5054_);
        return v___x_5055_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter(
    mut v_elem_5056_: *mut LeanObject,
    mut v_motive_5057_: *mut LeanObject,
    mut v_x_5058_: *mut LeanObject,
    mut v_h__1_5059_: *mut LeanObject,
    mut v_h__2_5060_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5058_) == 0 {
        let mut v___x_5061_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5059_);
        v___x_5061_ = lean_box(0);
        v___x_5062_ = lean_apply_1(v_h__2_5060_, v___x_5061_);
        return v___x_5062_;
    } else {
        let mut v_val_5063_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5060_);
        v_val_5063_ = lean_ctor_get(v_x_5058_, 0);
        lean_inc(v_val_5063_);
        lean_dec_ref_known(v_x_5058_, 1);
        v___x_5064_ = lean_apply_1(v_h__1_5059_, v_val_5063_);
        return v___x_5064_;
    }
}
pub unsafe fn l_Array_usize___boxed(
    mut v_00_u03b1_5067_: *mut LeanObject,
    mut v_xs_5068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5069_: usize = 0;
    let mut v_r_5070_: *mut LeanObject = core::ptr::null_mut();
    v_res_5069_ = lean_array_size(v_xs_5068_);
    lean_dec_ref(v_xs_5068_);
    v_r_5070_ = lean_box_usize(v_res_5069_);
    return v_r_5070_;
}
pub unsafe fn l_Array_uget___boxed(
    mut v_00_u03b1_5075_: *mut LeanObject,
    mut v_xs_5076_: *mut LeanObject,
    mut v_i_5077_: *mut LeanObject,
    mut v_h_5078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5079_: usize = 0;
    let mut v_res_5080_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5079_ = lean_unbox_usize(v_i_5077_);
    lean_dec(v_i_5077_);
    v_res_5080_ = lean_array_uget(v_xs_5076_, v_i_boxed_5079_);
    lean_dec_ref(v_xs_5076_);
    return v_res_5080_;
}
pub unsafe fn l_Array_ugetBorrowed___boxed(
    mut v_00_u03b1_5085_: *mut LeanObject,
    mut v_xs_5086_: *mut LeanObject,
    mut v_i_5087_: *mut LeanObject,
    mut v_h_5088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5089_: usize = 0;
    let mut v_res_5090_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5089_ = lean_unbox_usize(v_i_5087_);
    lean_dec(v_i_5087_);
    v_res_5090_ = lean_array_uget_borrowed(v_xs_5086_, v_i_boxed_5089_);
    lean_dec_ref(v_xs_5086_);
    return v_res_5090_;
}
pub unsafe fn l_Array_uset___boxed(
    mut v_00_u03b1_5096_: *mut LeanObject,
    mut v_xs_5097_: *mut LeanObject,
    mut v_i_5098_: *mut LeanObject,
    mut v_v_5099_: *mut LeanObject,
    mut v_h_5100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5101_: usize = 0;
    let mut v_res_5102_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5101_ = lean_unbox_usize(v_i_5098_);
    lean_dec(v_i_5098_);
    v_res_5102_ = lean_array_uset(v_xs_5097_, v_i_boxed_5101_, v_v_5099_);
    return v_res_5102_;
}
pub unsafe fn l_Array_pop___boxed(
    mut v_00_u03b1_5105_: *mut LeanObject,
    mut v_xs_5106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5107_: *mut LeanObject = core::ptr::null_mut();
    v_res_5107_ = lean_array_pop(v_xs_5106_);
    return v_res_5107_;
}
pub unsafe fn l_Array_replicate___boxed(
    mut v_00_u03b1_5111_: *mut LeanObject,
    mut v_n_5112_: *mut LeanObject,
    mut v_v_5113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5114_: *mut LeanObject = core::ptr::null_mut();
    v_res_5114_ = lean_mk_array(v_n_5112_, v_v_5113_);
    return v_res_5114_;
}
pub unsafe fn _init_l_Array_swap___auto__1___closed__9() -> *mut LeanObject {
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    v___x_5134_ = l_Array_swap___auto__1___closed__8;
    v___x_5135_ = l_Lean_mkAtom(v___x_5134_);
    return v___x_5135_;
}
pub unsafe fn _init_l_Array_swap___auto__1___closed__10() -> *mut LeanObject {
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    v___x_5136_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__9),
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__9_once),
        _init_l_Array_swap___auto__1___closed__9,
    );
    v___x_5137_ = l_Array_swap___auto__1___closed__3;
    v___x_5138_ = lean_array_push(v___x_5137_, v___x_5136_);
    return v___x_5138_;
}
pub unsafe fn _init_l_Array_swap___auto__1___closed__11() -> *mut LeanObject {
    let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut LeanObject = core::ptr::null_mut();
    v___x_5139_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__10),
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__10_once),
        _init_l_Array_swap___auto__1___closed__10,
    );
    v___x_5140_ = l_Array_swap___auto__1___closed__7;
    v___x_5141_ = lean_box(2);
    v___x_5142_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_5142_, 0, v___x_5141_);
    lean_ctor_set(v___x_5142_, 1, v___x_5140_);
    lean_ctor_set(v___x_5142_, 2, v___x_5139_);
    return v___x_5142_;
}
pub unsafe fn _init_l_Array_swap___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    v___x_5143_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__11),
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__11_once),
        _init_l_Array_swap___auto__1___closed__11,
    );
    v___x_5144_ = l_Array_swap___auto__1___closed__3;
    v___x_5145_ = lean_array_push(v___x_5144_, v___x_5143_);
    return v___x_5145_;
}
pub unsafe fn _init_l_Array_swap___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    v___x_5146_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__12_once),
        _init_l_Array_swap___auto__1___closed__12,
    );
    v___x_5147_ =
        l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13;
    v___x_5148_ = lean_box(2);
    v___x_5149_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_5149_, 0, v___x_5148_);
    lean_ctor_set(v___x_5149_, 1, v___x_5147_);
    lean_ctor_set(v___x_5149_, 2, v___x_5146_);
    return v___x_5149_;
}
pub unsafe fn _init_l_Array_swap___auto__1___closed__14() -> *mut LeanObject {
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
    v___x_5150_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__13_once),
        _init_l_Array_swap___auto__1___closed__13,
    );
    v___x_5151_ = l_Array_swap___auto__1___closed__3;
    v___x_5152_ = lean_array_push(v___x_5151_, v___x_5150_);
    return v___x_5152_;
}
pub unsafe fn _init_l_Array_swap___auto__1___closed__15() -> *mut LeanObject {
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
    v___x_5153_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__14),
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__14_once),
        _init_l_Array_swap___auto__1___closed__14,
    );
    v___x_5154_ = l_Array_swap___auto__1___closed__5;
    v___x_5155_ = lean_box(2);
    v___x_5156_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_5156_, 0, v___x_5155_);
    lean_ctor_set(v___x_5156_, 1, v___x_5154_);
    lean_ctor_set(v___x_5156_, 2, v___x_5153_);
    return v___x_5156_;
}
pub unsafe fn _init_l_Array_swap___auto__1___closed__16() -> *mut LeanObject {
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
    v___x_5157_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__15_once),
        _init_l_Array_swap___auto__1___closed__15,
    );
    v___x_5158_ = l_Array_swap___auto__1___closed__3;
    v___x_5159_ = lean_array_push(v___x_5158_, v___x_5157_);
    return v___x_5159_;
}
pub unsafe fn _init_l_Array_swap___auto__1___closed__17() -> *mut LeanObject {
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    v___x_5160_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__16_once),
        _init_l_Array_swap___auto__1___closed__16,
    );
    v___x_5161_ = l_Array_swap___auto__1___closed__2;
    v___x_5162_ = lean_box(2);
    v___x_5163_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_5163_, 0, v___x_5162_);
    lean_ctor_set(v___x_5163_, 1, v___x_5161_);
    lean_ctor_set(v___x_5163_, 2, v___x_5160_);
    return v___x_5163_;
}
pub unsafe fn _init_l_Array_swap___auto__1() -> *mut LeanObject {
    let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
    v___x_5164_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__17_once),
        _init_l_Array_swap___auto__1___closed__17,
    );
    return v___x_5164_;
}
pub unsafe fn _init_l_Array_swap___auto__3() -> *mut LeanObject {
    let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
    v___x_5165_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__17_once),
        _init_l_Array_swap___auto__1___closed__17,
    );
    return v___x_5165_;
}
pub unsafe fn l_Array_swap___boxed(
    mut v_00_u03b1_5172_: *mut LeanObject,
    mut v_xs_5173_: *mut LeanObject,
    mut v_i_5174_: *mut LeanObject,
    mut v_j_5175_: *mut LeanObject,
    mut v_hi_5176_: *mut LeanObject,
    mut v_hj_5177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5178_: *mut LeanObject = core::ptr::null_mut();
    v_res_5178_ = lean_array_fswap(v_xs_5173_, v_i_5174_, v_j_5175_);
    lean_dec(v_j_5175_);
    lean_dec(v_i_5174_);
    return v_res_5178_;
}
pub unsafe fn l_Array_swapIfInBounds___boxed(
    mut v_00_u03b1_5183_: *mut LeanObject,
    mut v_xs_5184_: *mut LeanObject,
    mut v_i_5185_: *mut LeanObject,
    mut v_j_5186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5187_: *mut LeanObject = core::ptr::null_mut();
    v_res_5187_ = lean_array_swap(v_xs_5184_, v_i_5185_, v_j_5186_);
    lean_dec(v_j_5186_);
    lean_dec(v_i_5185_);
    return v_res_5187_;
}
pub unsafe fn l_Array_instGetElemUSizeLtNatToNatSize___lam__0(
    mut v_xs_5188_: *mut LeanObject,
    mut v_i_5189_: usize,
    mut v_h_5190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    v___x_5191_ = lean_array_uget_borrowed(v_xs_5188_, v_i_5189_);
    lean_inc(v___x_5191_);
    return v___x_5191_;
}
pub unsafe fn l_Array_instGetElemUSizeLtNatToNatSize___lam__0___boxed(
    mut v_xs_5192_: *mut LeanObject,
    mut v_i_5193_: *mut LeanObject,
    mut v_h_5194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5195_: usize = 0;
    let mut v_res_5196_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5195_ = lean_unbox_usize(v_i_5193_);
    lean_dec(v_i_5193_);
    v_res_5196_ =
        l_Array_instGetElemUSizeLtNatToNatSize___lam__0(v_xs_5192_, v_i_boxed_5195_, v_h_5194_);
    lean_dec_ref(v_xs_5192_);
    return v_res_5196_;
}
pub unsafe fn l_Array_instGetElemUSizeLtNatToNatSize(
    mut v_00_u03b1_5198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5199_: *mut LeanObject = core::ptr::null_mut();
    v___f_5199_ = l_Array_instGetElemUSizeLtNatToNatSize___closed__0;
    return v___f_5199_;
}
pub unsafe fn l_Array_instEmptyCollection(
    mut v_00_u03b1_5202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5203_: *mut LeanObject = core::ptr::null_mut();
    v___x_5203_ = l_Array_instEmptyCollection___closed__0;
    return v___x_5203_;
}
pub unsafe fn l_Array_instInhabited(mut v_00_u03b1_5204_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5205_: *mut LeanObject = core::ptr::null_mut();
    v___x_5205_ = l_Array_instEmptyCollection___closed__0;
    return v___x_5205_;
}
pub unsafe fn l_Array_isEmpty___redArg(mut v_xs_5206_: *mut LeanObject) -> u8 {
    let mut v___x_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: u8 = 0;
    v___x_5207_ = lean_array_get_size(v_xs_5206_);
    v___x_5208_ = lean_unsigned_to_nat(0);
    v___x_5209_ = lean_nat_dec_eq(v___x_5207_, v___x_5208_);
    return v___x_5209_;
}
pub unsafe fn l_Array_isEmpty___redArg___boxed(mut v_xs_5210_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5211_: u8 = 0;
    let mut v_r_5212_: *mut LeanObject = core::ptr::null_mut();
    v_res_5211_ = l_Array_isEmpty___redArg(v_xs_5210_);
    lean_dec_ref(v_xs_5210_);
    v_r_5212_ = lean_box((v_res_5211_) as usize);
    return v_r_5212_;
}
pub unsafe fn l_Array_isEmpty(
    mut v_00_u03b1_5213_: *mut LeanObject,
    mut v_xs_5214_: *mut LeanObject,
) -> u8 {
    let mut v___x_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: u8 = 0;
    v___x_5215_ = lean_array_get_size(v_xs_5214_);
    v___x_5216_ = lean_unsigned_to_nat(0);
    v___x_5217_ = lean_nat_dec_eq(v___x_5215_, v___x_5216_);
    return v___x_5217_;
}
pub unsafe fn l_Array_isEmpty___boxed(
    mut v_00_u03b1_5218_: *mut LeanObject,
    mut v_xs_5219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5220_: u8 = 0;
    let mut v_r_5221_: *mut LeanObject = core::ptr::null_mut();
    v_res_5220_ = l_Array_isEmpty(v_00_u03b1_5218_, v_xs_5219_);
    lean_dec_ref(v_xs_5219_);
    v_r_5221_ = lean_box((v_res_5220_) as usize);
    return v_r_5221_;
}
pub unsafe fn l_Array_isEqvAux___redArg(
    mut v_xs_5222_: *mut LeanObject,
    mut v_ys_5223_: *mut LeanObject,
    mut v_p_5224_: *mut LeanObject,
    mut v_x_5225_: *mut LeanObject,
) -> u8 {
    let mut v_zero_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5227_: u8 = 0;
    let mut v_one_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: u8 = 0;
    let mut v___x_5234_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5226_ = lean_unsigned_to_nat(0);
                v_isZero_5227_ = lean_nat_dec_eq(v_x_5225_, v_zero_5226_);
                if v_isZero_5227_ == 1 {
                    lean_dec(v_x_5225_);
                    lean_dec_ref(v_p_5224_);
                    return v_isZero_5227_;
                } else {
                    v_one_5228_ = lean_unsigned_to_nat(1);
                    v_n_5229_ = lean_nat_sub(v_x_5225_, v_one_5228_);
                    lean_dec(v_x_5225_);
                    v___x_5230_ = lean_array_fget_borrowed(v_xs_5222_, v_n_5229_);
                    v___x_5231_ = lean_array_fget_borrowed(v_ys_5223_, v_n_5229_);
                    lean_inc_ref(v_p_5224_);
                    lean_inc(v___x_5231_);
                    lean_inc(v___x_5230_);
                    v___x_5232_ = lean_apply_2(v_p_5224_, v___x_5230_, v___x_5231_);
                    v___x_5233_ = (lean_unbox(v___x_5232_) as u8);
                    if v___x_5233_ == 0 {
                        lean_dec(v_n_5229_);
                        lean_dec_ref(v_p_5224_);
                        v___x_5234_ = (lean_unbox(v___x_5232_) as u8);
                        return v___x_5234_;
                    } else {
                        v_x_5225_ = v_n_5229_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___redArg___boxed(
    mut v_xs_5236_: *mut LeanObject,
    mut v_ys_5237_: *mut LeanObject,
    mut v_p_5238_: *mut LeanObject,
    mut v_x_5239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5240_: u8 = 0;
    let mut v_r_5241_: *mut LeanObject = core::ptr::null_mut();
    v_res_5240_ = l_Array_isEqvAux___redArg(v_xs_5236_, v_ys_5237_, v_p_5238_, v_x_5239_);
    lean_dec_ref(v_ys_5237_);
    lean_dec_ref(v_xs_5236_);
    v_r_5241_ = lean_box((v_res_5240_) as usize);
    return v_r_5241_;
}
pub unsafe fn l_Array_isEqvAux(
    mut v_00_u03b1_5242_: *mut LeanObject,
    mut v_xs_5243_: *mut LeanObject,
    mut v_ys_5244_: *mut LeanObject,
    mut v_hsz_5245_: *mut LeanObject,
    mut v_p_5246_: *mut LeanObject,
    mut v_x_5247_: *mut LeanObject,
    mut v_x_5248_: *mut LeanObject,
) -> u8 {
    let mut v___x_5249_: u8 = 0;
    v___x_5249_ = l_Array_isEqvAux___redArg(v_xs_5243_, v_ys_5244_, v_p_5246_, v_x_5247_);
    return v___x_5249_;
}
pub unsafe fn l_Array_isEqvAux___boxed(
    mut v_00_u03b1_5250_: *mut LeanObject,
    mut v_xs_5251_: *mut LeanObject,
    mut v_ys_5252_: *mut LeanObject,
    mut v_hsz_5253_: *mut LeanObject,
    mut v_p_5254_: *mut LeanObject,
    mut v_x_5255_: *mut LeanObject,
    mut v_x_5256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5257_: u8 = 0;
    let mut v_r_5258_: *mut LeanObject = core::ptr::null_mut();
    v_res_5257_ = l_Array_isEqvAux(
        v_00_u03b1_5250_,
        v_xs_5251_,
        v_ys_5252_,
        v_hsz_5253_,
        v_p_5254_,
        v_x_5255_,
        v_x_5256_,
    );
    lean_dec_ref(v_ys_5252_);
    lean_dec_ref(v_xs_5251_);
    v_r_5258_ = lean_box((v_res_5257_) as usize);
    return v_r_5258_;
}
pub unsafe fn l_Array_isEqv___redArg(
    mut v_xs_5259_: *mut LeanObject,
    mut v_ys_5260_: *mut LeanObject,
    mut v_p_5261_: *mut LeanObject,
) -> u8 {
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: u8 = 0;
    v___x_5262_ = lean_array_get_size(v_xs_5259_);
    v___x_5263_ = lean_array_get_size(v_ys_5260_);
    v___x_5264_ = lean_nat_dec_eq(v___x_5262_, v___x_5263_);
    if v___x_5264_ == 0 {
        lean_dec_ref(v_p_5261_);
        return v___x_5264_;
    } else {
        let mut v___x_5265_: u8 = 0;
        v___x_5265_ = l_Array_isEqvAux___redArg(v_xs_5259_, v_ys_5260_, v_p_5261_, v___x_5262_);
        return v___x_5265_;
    }
}
pub unsafe fn l_Array_isEqv___redArg___boxed(
    mut v_xs_5266_: *mut LeanObject,
    mut v_ys_5267_: *mut LeanObject,
    mut v_p_5268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5269_: u8 = 0;
    let mut v_r_5270_: *mut LeanObject = core::ptr::null_mut();
    v_res_5269_ = l_Array_isEqv___redArg(v_xs_5266_, v_ys_5267_, v_p_5268_);
    lean_dec_ref(v_ys_5267_);
    lean_dec_ref(v_xs_5266_);
    v_r_5270_ = lean_box((v_res_5269_) as usize);
    return v_r_5270_;
}
pub unsafe fn l_Array_isEqv(
    mut v_00_u03b1_5271_: *mut LeanObject,
    mut v_xs_5272_: *mut LeanObject,
    mut v_ys_5273_: *mut LeanObject,
    mut v_p_5274_: *mut LeanObject,
) -> u8 {
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: u8 = 0;
    v___x_5275_ = lean_array_get_size(v_xs_5272_);
    v___x_5276_ = lean_array_get_size(v_ys_5273_);
    v___x_5277_ = lean_nat_dec_eq(v___x_5275_, v___x_5276_);
    if v___x_5277_ == 0 {
        lean_dec_ref(v_p_5274_);
        return v___x_5277_;
    } else {
        let mut v___x_5278_: u8 = 0;
        v___x_5278_ = l_Array_isEqvAux___redArg(v_xs_5272_, v_ys_5273_, v_p_5274_, v___x_5275_);
        return v___x_5278_;
    }
}
pub unsafe fn l_Array_isEqv___boxed(
    mut v_00_u03b1_5279_: *mut LeanObject,
    mut v_xs_5280_: *mut LeanObject,
    mut v_ys_5281_: *mut LeanObject,
    mut v_p_5282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5283_: u8 = 0;
    let mut v_r_5284_: *mut LeanObject = core::ptr::null_mut();
    v_res_5283_ = l_Array_isEqv(v_00_u03b1_5279_, v_xs_5280_, v_ys_5281_, v_p_5282_);
    lean_dec_ref(v_ys_5281_);
    lean_dec_ref(v_xs_5280_);
    v_r_5284_ = lean_box((v_res_5283_) as usize);
    return v_r_5284_;
}
pub unsafe fn l_Array_instBEq___redArg___lam__0(
    mut v_inst_5285_: *mut LeanObject,
    mut v_xs_5286_: *mut LeanObject,
    mut v_ys_5287_: *mut LeanObject,
) -> u8 {
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: u8 = 0;
    v___x_5288_ = lean_array_get_size(v_xs_5286_);
    v___x_5289_ = lean_array_get_size(v_ys_5287_);
    v___x_5290_ = lean_nat_dec_eq(v___x_5288_, v___x_5289_);
    if v___x_5290_ == 0 {
        lean_dec_ref(v_inst_5285_);
        return v___x_5290_;
    } else {
        let mut v___x_5291_: u8 = 0;
        v___x_5291_ = l_Array_isEqvAux___redArg(v_xs_5286_, v_ys_5287_, v_inst_5285_, v___x_5288_);
        return v___x_5291_;
    }
}
pub unsafe fn l_Array_instBEq___redArg___lam__0___boxed(
    mut v_inst_5292_: *mut LeanObject,
    mut v_xs_5293_: *mut LeanObject,
    mut v_ys_5294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5295_: u8 = 0;
    let mut v_r_5296_: *mut LeanObject = core::ptr::null_mut();
    v_res_5295_ = l_Array_instBEq___redArg___lam__0(v_inst_5292_, v_xs_5293_, v_ys_5294_);
    lean_dec_ref(v_ys_5294_);
    lean_dec_ref(v_xs_5293_);
    v_r_5296_ = lean_box((v_res_5295_) as usize);
    return v_r_5296_;
}
pub unsafe fn l_Array_instBEq___redArg(mut v_inst_5297_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5298_: *mut LeanObject = core::ptr::null_mut();
    v___f_5298_ = lean_alloc_closure(
        l_Array_instBEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5298_, 0, v_inst_5297_);
    return v___f_5298_;
}
pub unsafe fn l_Array_instBEq(
    mut v_00_u03b1_5299_: *mut LeanObject,
    mut v_inst_5300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5301_: *mut LeanObject = core::ptr::null_mut();
    v___f_5301_ = lean_alloc_closure(
        l_Array_instBEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5301_, 0, v_inst_5300_);
    return v___f_5301_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(
    mut v_n_5302_: *mut LeanObject,
    mut v_f_5303_: *mut LeanObject,
    mut v_acc_5304_: *mut LeanObject,
    mut v_i_5305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5307_: u8 = 0;
    let mut v_one_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5306_ = lean_unsigned_to_nat(0);
                v_isZero_5307_ = lean_nat_dec_eq(v_i_5305_, v_zero_5306_);
                if v_isZero_5307_ == 1 {
                    lean_dec(v_i_5305_);
                    lean_dec(v_f_5303_);
                    return v_acc_5304_;
                } else {
                    v_one_5308_ = lean_unsigned_to_nat(1);
                    v_n_5309_ = lean_nat_sub(v_i_5305_, v_one_5308_);
                    lean_dec(v_i_5305_);
                    v___x_5310_ = lean_nat_sub(v_n_5302_, v_n_5309_);
                    v___x_5311_ = lean_nat_sub(v___x_5310_, v_one_5308_);
                    lean_dec(v___x_5310_);
                    lean_inc(v_f_5303_);
                    v___x_5312_ = lean_apply_1(v_f_5303_, v___x_5311_);
                    v___x_5313_ = lean_array_push(v_acc_5304_, v___x_5312_);
                    v_acc_5304_ = v___x_5313_;
                    v_i_5305_ = v_n_5309_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg___boxed(
    mut v_n_5315_: *mut LeanObject,
    mut v_f_5316_: *mut LeanObject,
    mut v_acc_5317_: *mut LeanObject,
    mut v_i_5318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5319_: *mut LeanObject = core::ptr::null_mut();
    v_res_5319_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(
        v_n_5315_,
        v_f_5316_,
        v_acc_5317_,
        v_i_5318_,
    );
    lean_dec(v_n_5315_);
    return v_res_5319_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_ofFn_go(
    mut v_00_u03b1_5320_: *mut LeanObject,
    mut v_n_5321_: *mut LeanObject,
    mut v_f_5322_: *mut LeanObject,
    mut v_acc_5323_: *mut LeanObject,
    mut v_i_5324_: *mut LeanObject,
    mut v_a_5325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    v___x_5326_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(
        v_n_5321_,
        v_f_5322_,
        v_acc_5323_,
        v_i_5324_,
    );
    return v___x_5326_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_ofFn_go___boxed(
    mut v_00_u03b1_5327_: *mut LeanObject,
    mut v_n_5328_: *mut LeanObject,
    mut v_f_5329_: *mut LeanObject,
    mut v_acc_5330_: *mut LeanObject,
    mut v_i_5331_: *mut LeanObject,
    mut v_a_5332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5333_: *mut LeanObject = core::ptr::null_mut();
    v_res_5333_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go(
        v_00_u03b1_5327_,
        v_n_5328_,
        v_f_5329_,
        v_acc_5330_,
        v_i_5331_,
        v_a_5332_,
    );
    lean_dec(v_n_5328_);
    return v_res_5333_;
}
pub unsafe fn l_Array_ofFn___redArg(
    mut v_n_5334_: *mut LeanObject,
    mut v_f_5335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut LeanObject = core::ptr::null_mut();
    v___x_5336_ = lean_mk_empty_array_with_capacity(v_n_5334_);
    lean_inc(v_n_5334_);
    v___x_5337_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(
        v_n_5334_,
        v_f_5335_,
        v___x_5336_,
        v_n_5334_,
    );
    lean_dec(v_n_5334_);
    return v___x_5337_;
}
pub unsafe fn l_Array_ofFn(
    mut v_00_u03b1_5338_: *mut LeanObject,
    mut v_n_5339_: *mut LeanObject,
    mut v_f_5340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5341_: *mut LeanObject = core::ptr::null_mut();
    v___x_5341_ = l_Array_ofFn___redArg(v_n_5339_, v_f_5340_);
    return v___x_5341_;
}
pub unsafe fn l_Array_range___lam__0(mut v_i_5342_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_i_5342_);
    return v_i_5342_;
}
pub unsafe fn l_Array_range___lam__0___boxed(mut v_i_5343_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5344_: *mut LeanObject = core::ptr::null_mut();
    v_res_5344_ = l_Array_range___lam__0(v_i_5343_);
    lean_dec(v_i_5343_);
    return v_res_5344_;
}
pub unsafe fn l_Array_range(mut v_n_5346_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut LeanObject = core::ptr::null_mut();
    v___f_5347_ = l_Array_range___closed__0;
    v___x_5348_ = l_Array_ofFn___redArg(v_n_5346_, v___f_5347_);
    return v___x_5348_;
}
pub unsafe fn l_Array_range_x27___lam__0(
    mut v_step_5349_: *mut LeanObject,
    mut v_start_5350_: *mut LeanObject,
    mut v_i_5351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    v___x_5352_ = lean_nat_mul(v_step_5349_, v_i_5351_);
    v___x_5353_ = lean_nat_add(v_start_5350_, v___x_5352_);
    lean_dec(v___x_5352_);
    return v___x_5353_;
}
pub unsafe fn l_Array_range_x27___lam__0___boxed(
    mut v_step_5354_: *mut LeanObject,
    mut v_start_5355_: *mut LeanObject,
    mut v_i_5356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5357_: *mut LeanObject = core::ptr::null_mut();
    v_res_5357_ = l_Array_range_x27___lam__0(v_step_5354_, v_start_5355_, v_i_5356_);
    lean_dec(v_i_5356_);
    lean_dec(v_start_5355_);
    lean_dec(v_step_5354_);
    return v_res_5357_;
}
pub unsafe fn l_Array_range_x27(
    mut v_start_5358_: *mut LeanObject,
    mut v_size_5359_: *mut LeanObject,
    mut v_step_5360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    v___f_5361_ = lean_alloc_closure(
        l_Array_range_x27___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5361_, 0, v_step_5360_);
    lean_closure_set(v___f_5361_, 1, v_start_5358_);
    v___x_5362_ = l_Array_ofFn___redArg(v_size_5359_, v___f_5361_);
    return v___x_5362_;
}
pub unsafe fn l_Array_singleton___redArg(mut v_v_5363_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut LeanObject = core::ptr::null_mut();
    v___x_5364_ = lean_unsigned_to_nat(1);
    v___x_5365_ = lean_mk_empty_array_with_capacity(v___x_5364_);
    v___x_5366_ = lean_array_push(v___x_5365_, v_v_5363_);
    return v___x_5366_;
}
pub unsafe fn l_Array_singleton(
    mut v_00_u03b1_5367_: *mut LeanObject,
    mut v_v_5368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    v___x_5369_ = lean_unsigned_to_nat(1);
    v___x_5370_ = lean_mk_empty_array_with_capacity(v___x_5369_);
    v___x_5371_ = lean_array_push(v___x_5370_, v_v_5368_);
    return v___x_5371_;
}
pub unsafe fn l_Array_back_x21___redArg(
    mut v_inst_5372_: *mut LeanObject,
    mut v_xs_5373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    v___x_5374_ = lean_array_get_size(v_xs_5373_);
    v___x_5375_ = lean_unsigned_to_nat(1);
    v___x_5376_ = lean_nat_sub(v___x_5374_, v___x_5375_);
    v___x_5377_ = lean_array_get_borrowed(v_inst_5372_, v_xs_5373_, v___x_5376_);
    lean_dec(v___x_5376_);
    lean_inc(v___x_5377_);
    return v___x_5377_;
}
pub unsafe fn l_Array_back_x21___redArg___boxed(
    mut v_inst_5378_: *mut LeanObject,
    mut v_xs_5379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5380_: *mut LeanObject = core::ptr::null_mut();
    v_res_5380_ = l_Array_back_x21___redArg(v_inst_5378_, v_xs_5379_);
    lean_dec_ref(v_xs_5379_);
    lean_dec(v_inst_5378_);
    return v_res_5380_;
}
pub unsafe fn l_Array_back_x21(
    mut v_00_u03b1_5381_: *mut LeanObject,
    mut v_inst_5382_: *mut LeanObject,
    mut v_xs_5383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
    v___x_5384_ = lean_array_get_size(v_xs_5383_);
    v___x_5385_ = lean_unsigned_to_nat(1);
    v___x_5386_ = lean_nat_sub(v___x_5384_, v___x_5385_);
    v___x_5387_ = lean_array_get_borrowed(v_inst_5382_, v_xs_5383_, v___x_5386_);
    lean_dec(v___x_5386_);
    lean_inc(v___x_5387_);
    return v___x_5387_;
}
pub unsafe fn l_Array_back_x21___boxed(
    mut v_00_u03b1_5388_: *mut LeanObject,
    mut v_inst_5389_: *mut LeanObject,
    mut v_xs_5390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5391_: *mut LeanObject = core::ptr::null_mut();
    v_res_5391_ = l_Array_back_x21(v_00_u03b1_5388_, v_inst_5389_, v_xs_5390_);
    lean_dec_ref(v_xs_5390_);
    lean_dec(v_inst_5389_);
    return v_res_5391_;
}
pub unsafe fn _init_l_Array_back___auto__1() -> *mut LeanObject {
    let mut v___x_5392_: *mut LeanObject = core::ptr::null_mut();
    v___x_5392_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__17_once),
        _init_l_Array_swap___auto__1___closed__17,
    );
    return v___x_5392_;
}
pub unsafe fn l_Array_back___redArg(mut v_xs_5393_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut LeanObject = core::ptr::null_mut();
    v___x_5394_ = lean_array_get_size(v_xs_5393_);
    v___x_5395_ = lean_unsigned_to_nat(1);
    v___x_5396_ = lean_nat_sub(v___x_5394_, v___x_5395_);
    v___x_5397_ = lean_array_fget_borrowed(v_xs_5393_, v___x_5396_);
    lean_dec(v___x_5396_);
    lean_inc(v___x_5397_);
    return v___x_5397_;
}
pub unsafe fn l_Array_back___redArg___boxed(mut v_xs_5398_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5399_: *mut LeanObject = core::ptr::null_mut();
    v_res_5399_ = l_Array_back___redArg(v_xs_5398_);
    lean_dec_ref(v_xs_5398_);
    return v_res_5399_;
}
pub unsafe fn l_Array_back(
    mut v_00_u03b1_5400_: *mut LeanObject,
    mut v_xs_5401_: *mut LeanObject,
    mut v_h_5402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    v___x_5403_ = lean_array_get_size(v_xs_5401_);
    v___x_5404_ = lean_unsigned_to_nat(1);
    v___x_5405_ = lean_nat_sub(v___x_5403_, v___x_5404_);
    v___x_5406_ = lean_array_fget_borrowed(v_xs_5401_, v___x_5405_);
    lean_dec(v___x_5405_);
    lean_inc(v___x_5406_);
    return v___x_5406_;
}
pub unsafe fn l_Array_back___boxed(
    mut v_00_u03b1_5407_: *mut LeanObject,
    mut v_xs_5408_: *mut LeanObject,
    mut v_h_5409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5410_: *mut LeanObject = core::ptr::null_mut();
    v_res_5410_ = l_Array_back(v_00_u03b1_5407_, v_xs_5408_, v_h_5409_);
    lean_dec_ref(v_xs_5408_);
    return v_res_5410_;
}
pub unsafe fn l_Array_back_x3f___redArg(mut v_xs_5411_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: u8 = 0;
    v___x_5412_ = lean_array_get_size(v_xs_5411_);
    v___x_5413_ = lean_unsigned_to_nat(1);
    v___x_5414_ = lean_nat_sub(v___x_5412_, v___x_5413_);
    v___x_5415_ = lean_nat_dec_lt(v___x_5414_, v___x_5412_);
    if v___x_5415_ == 0 {
        let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_5414_);
        v___x_5416_ = lean_box(0);
        return v___x_5416_;
    } else {
        let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
        v___x_5417_ = lean_array_fget_borrowed(v_xs_5411_, v___x_5414_);
        lean_dec(v___x_5414_);
        lean_inc(v___x_5417_);
        v___x_5418_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_5418_, 0, v___x_5417_);
        return v___x_5418_;
    }
}
pub unsafe fn l_Array_back_x3f___redArg___boxed(
    mut v_xs_5419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5420_: *mut LeanObject = core::ptr::null_mut();
    v_res_5420_ = l_Array_back_x3f___redArg(v_xs_5419_);
    lean_dec_ref(v_xs_5419_);
    return v_res_5420_;
}
pub unsafe fn l_Array_back_x3f(
    mut v_00_u03b1_5421_: *mut LeanObject,
    mut v_xs_5422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: u8 = 0;
    v___x_5423_ = lean_array_get_size(v_xs_5422_);
    v___x_5424_ = lean_unsigned_to_nat(1);
    v___x_5425_ = lean_nat_sub(v___x_5423_, v___x_5424_);
    v___x_5426_ = lean_nat_dec_lt(v___x_5425_, v___x_5423_);
    if v___x_5426_ == 0 {
        let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_5425_);
        v___x_5427_ = lean_box(0);
        return v___x_5427_;
    } else {
        let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5429_: *mut LeanObject = core::ptr::null_mut();
        v___x_5428_ = lean_array_fget_borrowed(v_xs_5422_, v___x_5425_);
        lean_dec(v___x_5425_);
        lean_inc(v___x_5428_);
        v___x_5429_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_5429_, 0, v___x_5428_);
        return v___x_5429_;
    }
}
pub unsafe fn l_Array_back_x3f___boxed(
    mut v_00_u03b1_5430_: *mut LeanObject,
    mut v_xs_5431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5432_: *mut LeanObject = core::ptr::null_mut();
    v_res_5432_ = l_Array_back_x3f(v_00_u03b1_5430_, v_xs_5431_);
    lean_dec_ref(v_xs_5431_);
    return v_res_5432_;
}
pub unsafe fn _init_l_Array_swapAt___auto__1() -> *mut LeanObject {
    let mut v___x_5433_: *mut LeanObject = core::ptr::null_mut();
    v___x_5433_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__17_once),
        _init_l_Array_swap___auto__1___closed__17,
    );
    return v___x_5433_;
}
pub unsafe fn l_Array_swapAt___redArg(
    mut v_xs_5434_: *mut LeanObject,
    mut v_i_5435_: *mut LeanObject,
    mut v_v_5436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut LeanObject = core::ptr::null_mut();
    v_e_5437_ = lean_array_fget(v_xs_5434_, v_i_5435_);
    v_xs_x27_5438_ = lean_array_fset(v_xs_5434_, v_i_5435_, v_v_5436_);
    v___x_5439_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5439_, 0, v_e_5437_);
    lean_ctor_set(v___x_5439_, 1, v_xs_x27_5438_);
    return v___x_5439_;
}
pub unsafe fn l_Array_swapAt___redArg___boxed(
    mut v_xs_5440_: *mut LeanObject,
    mut v_i_5441_: *mut LeanObject,
    mut v_v_5442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5443_: *mut LeanObject = core::ptr::null_mut();
    v_res_5443_ = l_Array_swapAt___redArg(v_xs_5440_, v_i_5441_, v_v_5442_);
    lean_dec(v_i_5441_);
    return v_res_5443_;
}
pub unsafe fn l_Array_swapAt(
    mut v_00_u03b1_5444_: *mut LeanObject,
    mut v_xs_5445_: *mut LeanObject,
    mut v_i_5446_: *mut LeanObject,
    mut v_v_5447_: *mut LeanObject,
    mut v_hi_5448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    v_e_5449_ = lean_array_fget(v_xs_5445_, v_i_5446_);
    v_xs_x27_5450_ = lean_array_fset(v_xs_5445_, v_i_5446_, v_v_5447_);
    v___x_5451_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5451_, 0, v_e_5449_);
    lean_ctor_set(v___x_5451_, 1, v_xs_x27_5450_);
    return v___x_5451_;
}
pub unsafe fn l_Array_swapAt___boxed(
    mut v_00_u03b1_5452_: *mut LeanObject,
    mut v_xs_5453_: *mut LeanObject,
    mut v_i_5454_: *mut LeanObject,
    mut v_v_5455_: *mut LeanObject,
    mut v_hi_5456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5457_: *mut LeanObject = core::ptr::null_mut();
    v_res_5457_ = l_Array_swapAt(
        v_00_u03b1_5452_,
        v_xs_5453_,
        v_i_5454_,
        v_v_5455_,
        v_hi_5456_,
    );
    lean_dec(v_i_5454_);
    return v_res_5457_;
}
pub unsafe fn l_Array_swapAt_x21___redArg(
    mut v_xs_5462_: *mut LeanObject,
    mut v_i_5463_: *mut LeanObject,
    mut v_v_5464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: u8 = 0;
    v___x_5465_ = lean_array_get_size(v_xs_5462_);
    v___x_5466_ = lean_nat_dec_lt(v_i_5463_, v___x_5465_);
    if v___x_5466_ == 0 {
        let mut v_this_5467_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5475_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5476_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5477_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5478_: *mut LeanObject = core::ptr::null_mut();
        v_this_5467_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v_this_5467_, 0, v_v_5464_);
        lean_ctor_set(v_this_5467_, 1, v_xs_5462_);
        v___x_5468_ = l_Array_swapAt_x21___redArg___closed__0;
        v___x_5469_ = l_Array_swapAt_x21___redArg___closed__1;
        v___x_5470_ = lean_unsigned_to_nat(438);
        v___x_5471_ = lean_unsigned_to_nat(4);
        v___x_5472_ = l_Array_swapAt_x21___redArg___closed__2;
        v___x_5473_ = l_Nat_reprFast(v_i_5463_);
        v___x_5474_ = lean_string_append(v___x_5472_, v___x_5473_);
        lean_dec_ref(v___x_5473_);
        v___x_5475_ = l_Array_swapAt_x21___redArg___closed__3;
        v___x_5476_ = lean_string_append(v___x_5474_, v___x_5475_);
        v___x_5477_ = l_mkPanicMessageWithDecl(
            v___x_5468_,
            v___x_5469_,
            v___x_5470_,
            v___x_5471_,
            v___x_5476_,
        );
        lean_dec_ref(v___x_5476_);
        v___x_5478_ = l_panic___redArg(v_this_5467_, v___x_5477_);
        lean_dec_ref_known(v_this_5467_, 2);
        return v___x_5478_;
    } else {
        let mut v_e_5479_: *mut LeanObject = core::ptr::null_mut();
        let mut v_xs_x27_5480_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5481_: *mut LeanObject = core::ptr::null_mut();
        v_e_5479_ = lean_array_fget(v_xs_5462_, v_i_5463_);
        v_xs_x27_5480_ = lean_array_fset(v_xs_5462_, v_i_5463_, v_v_5464_);
        lean_dec(v_i_5463_);
        v___x_5481_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5481_, 0, v_e_5479_);
        lean_ctor_set(v___x_5481_, 1, v_xs_x27_5480_);
        return v___x_5481_;
    }
}
pub unsafe fn l_Array_swapAt_x21(
    mut v_00_u03b1_5482_: *mut LeanObject,
    mut v_xs_5483_: *mut LeanObject,
    mut v_i_5484_: *mut LeanObject,
    mut v_v_5485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: u8 = 0;
    v___x_5486_ = lean_array_get_size(v_xs_5483_);
    v___x_5487_ = lean_nat_dec_lt(v_i_5484_, v___x_5486_);
    if v___x_5487_ == 0 {
        let mut v_this_5488_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5491_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
        v_this_5488_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v_this_5488_, 0, v_v_5485_);
        lean_ctor_set(v_this_5488_, 1, v_xs_5483_);
        v___x_5489_ = l_Array_swapAt_x21___redArg___closed__0;
        v___x_5490_ = l_Array_swapAt_x21___redArg___closed__1;
        v___x_5491_ = lean_unsigned_to_nat(438);
        v___x_5492_ = lean_unsigned_to_nat(4);
        v___x_5493_ = l_Array_swapAt_x21___redArg___closed__2;
        v___x_5494_ = l_Nat_reprFast(v_i_5484_);
        v___x_5495_ = lean_string_append(v___x_5493_, v___x_5494_);
        lean_dec_ref(v___x_5494_);
        v___x_5496_ = l_Array_swapAt_x21___redArg___closed__3;
        v___x_5497_ = lean_string_append(v___x_5495_, v___x_5496_);
        v___x_5498_ = l_mkPanicMessageWithDecl(
            v___x_5489_,
            v___x_5490_,
            v___x_5491_,
            v___x_5492_,
            v___x_5497_,
        );
        lean_dec_ref(v___x_5497_);
        v___x_5499_ = l_panic___redArg(v_this_5488_, v___x_5498_);
        lean_dec_ref_known(v_this_5488_, 2);
        return v___x_5499_;
    } else {
        let mut v_e_5500_: *mut LeanObject = core::ptr::null_mut();
        let mut v_xs_x27_5501_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
        v_e_5500_ = lean_array_fget(v_xs_5483_, v_i_5484_);
        v_xs_x27_5501_ = lean_array_fset(v_xs_5483_, v_i_5484_, v_v_5485_);
        lean_dec(v_i_5484_);
        v___x_5502_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5502_, 0, v_e_5500_);
        lean_ctor_set(v___x_5502_, 1, v_xs_x27_5501_);
        return v___x_5502_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(
    mut v_x_5503_: *mut LeanObject,
    mut v_x_5504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5506_: u8 = 0;
    let mut v_one_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5505_ = lean_unsigned_to_nat(0);
                v_isZero_5506_ = lean_nat_dec_eq(v_x_5503_, v_zero_5505_);
                if v_isZero_5506_ == 1 {
                    lean_dec(v_x_5503_);
                    return v_x_5504_;
                } else {
                    v_one_5507_ = lean_unsigned_to_nat(1);
                    v_n_5508_ = lean_nat_sub(v_x_5503_, v_one_5507_);
                    lean_dec(v_x_5503_);
                    v___x_5509_ = lean_array_pop(v_x_5504_);
                    v_x_5503_ = v_n_5508_;
                    v_x_5504_ = v___x_5509_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_shrink_loop(
    mut v_00_u03b1_5511_: *mut LeanObject,
    mut v_x_5512_: *mut LeanObject,
    mut v_x_5513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
    v___x_5514_ =
        l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(v_x_5512_, v_x_5513_);
    return v___x_5514_;
}
pub unsafe fn l_Array_shrink___redArg(
    mut v_xs_5515_: *mut LeanObject,
    mut v_n_5516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    v___x_5517_ = lean_array_get_size(v_xs_5515_);
    v___x_5518_ = lean_nat_sub(v___x_5517_, v_n_5516_);
    v___x_5519_ =
        l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(v___x_5518_, v_xs_5515_);
    return v___x_5519_;
}
pub unsafe fn l_Array_shrink___redArg___boxed(
    mut v_xs_5520_: *mut LeanObject,
    mut v_n_5521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5522_: *mut LeanObject = core::ptr::null_mut();
    v_res_5522_ = l_Array_shrink___redArg(v_xs_5520_, v_n_5521_);
    lean_dec(v_n_5521_);
    return v_res_5522_;
}
pub unsafe fn l_Array_shrink(
    mut v_00_u03b1_5523_: *mut LeanObject,
    mut v_xs_5524_: *mut LeanObject,
    mut v_n_5525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    v___x_5526_ = l_Array_shrink___redArg(v_xs_5524_, v_n_5525_);
    return v___x_5526_;
}
pub unsafe fn l_Array_shrink___boxed(
    mut v_00_u03b1_5527_: *mut LeanObject,
    mut v_xs_5528_: *mut LeanObject,
    mut v_n_5529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5530_: *mut LeanObject = core::ptr::null_mut();
    v_res_5530_ = l_Array_shrink(v_00_u03b1_5527_, v_xs_5528_, v_n_5529_);
    lean_dec(v_n_5529_);
    return v_res_5530_;
}
pub unsafe fn l_Array_take___redArg(
    mut v_xs_5531_: *mut LeanObject,
    mut v_i_5532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    v___x_5533_ = lean_unsigned_to_nat(0);
    v___x_5534_ = l_Array_extract___redArg(v_xs_5531_, v___x_5533_, v_i_5532_);
    return v___x_5534_;
}
pub unsafe fn l_Array_take___redArg___boxed(
    mut v_xs_5535_: *mut LeanObject,
    mut v_i_5536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5537_: *mut LeanObject = core::ptr::null_mut();
    v_res_5537_ = l_Array_take___redArg(v_xs_5535_, v_i_5536_);
    lean_dec_ref(v_xs_5535_);
    return v_res_5537_;
}
pub unsafe fn l_Array_take(
    mut v_00_u03b1_5538_: *mut LeanObject,
    mut v_xs_5539_: *mut LeanObject,
    mut v_i_5540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    v___x_5541_ = lean_unsigned_to_nat(0);
    v___x_5542_ = l_Array_extract___redArg(v_xs_5539_, v___x_5541_, v_i_5540_);
    return v___x_5542_;
}
pub unsafe fn l_Array_take___boxed(
    mut v_00_u03b1_5543_: *mut LeanObject,
    mut v_xs_5544_: *mut LeanObject,
    mut v_i_5545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5546_: *mut LeanObject = core::ptr::null_mut();
    v_res_5546_ = l_Array_take(v_00_u03b1_5543_, v_xs_5544_, v_i_5545_);
    lean_dec_ref(v_xs_5544_);
    return v_res_5546_;
}
pub unsafe fn l_Array_drop___redArg(
    mut v_xs_5547_: *mut LeanObject,
    mut v_i_5548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut LeanObject = core::ptr::null_mut();
    v___x_5549_ = lean_array_get_size(v_xs_5547_);
    v___x_5550_ = l_Array_extract___redArg(v_xs_5547_, v_i_5548_, v___x_5549_);
    return v___x_5550_;
}
pub unsafe fn l_Array_drop___redArg___boxed(
    mut v_xs_5551_: *mut LeanObject,
    mut v_i_5552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5553_: *mut LeanObject = core::ptr::null_mut();
    v_res_5553_ = l_Array_drop___redArg(v_xs_5551_, v_i_5552_);
    lean_dec_ref(v_xs_5551_);
    return v_res_5553_;
}
pub unsafe fn l_Array_drop(
    mut v_00_u03b1_5554_: *mut LeanObject,
    mut v_xs_5555_: *mut LeanObject,
    mut v_i_5556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut LeanObject = core::ptr::null_mut();
    v___x_5557_ = lean_array_get_size(v_xs_5555_);
    v___x_5558_ = l_Array_extract___redArg(v_xs_5555_, v_i_5556_, v___x_5557_);
    return v___x_5558_;
}
pub unsafe fn l_Array_drop___boxed(
    mut v_00_u03b1_5559_: *mut LeanObject,
    mut v_xs_5560_: *mut LeanObject,
    mut v_i_5561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5562_: *mut LeanObject = core::ptr::null_mut();
    v_res_5562_ = l_Array_drop(v_00_u03b1_5559_, v_xs_5560_, v_i_5561_);
    lean_dec_ref(v_xs_5560_);
    return v_res_5562_;
}
pub unsafe fn l_Array_modifyMUnsafe___redArg___lam__0(
    mut v_toApplicative_5563_: *mut LeanObject,
    mut v_xs_x27_5564_: *mut LeanObject,
    mut v_i_5565_: *mut LeanObject,
    mut v_v_5566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_5567_ = lean_ctor_get(v_toApplicative_5563_, 1);
    lean_inc(v_toPure_5567_);
    lean_dec_ref(v_toApplicative_5563_);
    v___x_5568_ = lean_array_fset(v_xs_x27_5564_, v_i_5565_, v_v_5566_);
    v___x_5569_ = lean_apply_2(v_toPure_5567_, lean_box(0), v___x_5568_);
    return v___x_5569_;
}
pub unsafe fn l_Array_modifyMUnsafe___redArg___lam__0___boxed(
    mut v_toApplicative_5570_: *mut LeanObject,
    mut v_xs_x27_5571_: *mut LeanObject,
    mut v_i_5572_: *mut LeanObject,
    mut v_v_5573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5574_: *mut LeanObject = core::ptr::null_mut();
    v_res_5574_ = l_Array_modifyMUnsafe___redArg___lam__0(
        v_toApplicative_5570_,
        v_xs_x27_5571_,
        v_i_5572_,
        v_v_5573_,
    );
    lean_dec(v_i_5572_);
    return v_res_5574_;
}
pub unsafe fn l_Array_modifyMUnsafe___redArg(
    mut v_inst_5575_: *mut LeanObject,
    mut v_xs_5576_: *mut LeanObject,
    mut v_i_5577_: *mut LeanObject,
    mut v_f_5578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: u8 = 0;
    v___x_5579_ = lean_array_get_size(v_xs_5576_);
    v___x_5580_ = lean_nat_dec_lt(v_i_5577_, v___x_5579_);
    if v___x_5580_ == 0 {
        let mut v_toApplicative_5581_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_5582_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_5578_);
        lean_dec(v_i_5577_);
        v_toApplicative_5581_ = lean_ctor_get(v_inst_5575_, 0);
        lean_inc_ref(v_toApplicative_5581_);
        lean_dec_ref(v_inst_5575_);
        v_toPure_5582_ = lean_ctor_get(v_toApplicative_5581_, 1);
        lean_inc(v_toPure_5582_);
        lean_dec_ref(v_toApplicative_5581_);
        v___x_5583_ = lean_apply_2(v_toPure_5582_, lean_box(0), v_xs_5576_);
        return v___x_5583_;
    } else {
        let mut v_toApplicative_5584_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_5585_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5586_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
        let mut v_xs_x27_5588_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5589_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_5584_ = lean_ctor_get(v_inst_5575_, 0);
        lean_inc_ref(v_toApplicative_5584_);
        v_toBind_5585_ = lean_ctor_get(v_inst_5575_, 1);
        lean_inc(v_toBind_5585_);
        lean_dec_ref(v_inst_5575_);
        v_v_5586_ = lean_array_fget(v_xs_5576_, v_i_5577_);
        v___x_5587_ = lean_box(0);
        v_xs_x27_5588_ = lean_array_fset(v_xs_5576_, v_i_5577_, v___x_5587_);
        v___f_5589_ = lean_alloc_closure(
            l_Array_modifyMUnsafe___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_5589_, 0, v_toApplicative_5584_);
        lean_closure_set(v___f_5589_, 1, v_xs_x27_5588_);
        lean_closure_set(v___f_5589_, 2, v_i_5577_);
        v___x_5590_ = lean_apply_1(v_f_5578_, v_v_5586_);
        v___x_5591_ = lean_apply_4(
            v_toBind_5585_,
            lean_box(0),
            lean_box(0),
            v___x_5590_,
            v___f_5589_,
        );
        return v___x_5591_;
    }
}
pub unsafe fn l_Array_modifyMUnsafe(
    mut v_00_u03b1_5592_: *mut LeanObject,
    mut v_m_5593_: *mut LeanObject,
    mut v_inst_5594_: *mut LeanObject,
    mut v_xs_5595_: *mut LeanObject,
    mut v_i_5596_: *mut LeanObject,
    mut v_f_5597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: u8 = 0;
    v___x_5598_ = lean_array_get_size(v_xs_5595_);
    v___x_5599_ = lean_nat_dec_lt(v_i_5596_, v___x_5598_);
    if v___x_5599_ == 0 {
        let mut v_toApplicative_5600_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_5601_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5602_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_5597_);
        lean_dec(v_i_5596_);
        v_toApplicative_5600_ = lean_ctor_get(v_inst_5594_, 0);
        lean_inc_ref(v_toApplicative_5600_);
        lean_dec_ref(v_inst_5594_);
        v_toPure_5601_ = lean_ctor_get(v_toApplicative_5600_, 1);
        lean_inc(v_toPure_5601_);
        lean_dec_ref(v_toApplicative_5600_);
        v___x_5602_ = lean_apply_2(v_toPure_5601_, lean_box(0), v_xs_5595_);
        return v___x_5602_;
    } else {
        let mut v_toApplicative_5603_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_5604_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5605_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
        let mut v_xs_x27_5607_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5608_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5609_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_5603_ = lean_ctor_get(v_inst_5594_, 0);
        lean_inc_ref(v_toApplicative_5603_);
        v_toBind_5604_ = lean_ctor_get(v_inst_5594_, 1);
        lean_inc(v_toBind_5604_);
        lean_dec_ref(v_inst_5594_);
        v_v_5605_ = lean_array_fget(v_xs_5595_, v_i_5596_);
        v___x_5606_ = lean_box(0);
        v_xs_x27_5607_ = lean_array_fset(v_xs_5595_, v_i_5596_, v___x_5606_);
        v___f_5608_ = lean_alloc_closure(
            l_Array_modifyMUnsafe___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_5608_, 0, v_toApplicative_5603_);
        lean_closure_set(v___f_5608_, 1, v_xs_x27_5607_);
        lean_closure_set(v___f_5608_, 2, v_i_5596_);
        v___x_5609_ = lean_apply_1(v_f_5597_, v_v_5605_);
        v___x_5610_ = lean_apply_4(
            v_toBind_5604_,
            lean_box(0),
            lean_box(0),
            v___x_5609_,
            v___f_5608_,
        );
        return v___x_5610_;
    }
}
pub unsafe fn l_Array_modify___redArg(
    mut v_xs_5611_: *mut LeanObject,
    mut v_i_5612_: *mut LeanObject,
    mut v_f_5613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: u8 = 0;
    v___x_5614_ = lean_array_get_size(v_xs_5611_);
    v___x_5615_ = lean_nat_dec_lt(v_i_5612_, v___x_5614_);
    if v___x_5615_ == 0 {
        lean_dec(v_f_5613_);
        return v_xs_5611_;
    } else {
        let mut v_v_5616_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5617_: *mut LeanObject = core::ptr::null_mut();
        let mut v_xs_x27_5618_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5620_: *mut LeanObject = core::ptr::null_mut();
        v_v_5616_ = lean_array_fget(v_xs_5611_, v_i_5612_);
        v___x_5617_ = lean_box(0);
        v_xs_x27_5618_ = lean_array_fset(v_xs_5611_, v_i_5612_, v___x_5617_);
        v___x_5619_ = lean_apply_1(v_f_5613_, v_v_5616_);
        v___x_5620_ = lean_array_fset(v_xs_x27_5618_, v_i_5612_, v___x_5619_);
        return v___x_5620_;
    }
}
pub unsafe fn l_Array_modify___redArg___boxed(
    mut v_xs_5621_: *mut LeanObject,
    mut v_i_5622_: *mut LeanObject,
    mut v_f_5623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5624_: *mut LeanObject = core::ptr::null_mut();
    v_res_5624_ = l_Array_modify___redArg(v_xs_5621_, v_i_5622_, v_f_5623_);
    lean_dec(v_i_5622_);
    return v_res_5624_;
}
pub unsafe fn l_Array_modify(
    mut v_00_u03b1_5625_: *mut LeanObject,
    mut v_xs_5626_: *mut LeanObject,
    mut v_i_5627_: *mut LeanObject,
    mut v_f_5628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: u8 = 0;
    v___x_5629_ = lean_array_get_size(v_xs_5626_);
    v___x_5630_ = lean_nat_dec_lt(v_i_5627_, v___x_5629_);
    if v___x_5630_ == 0 {
        lean_dec(v_f_5628_);
        return v_xs_5626_;
    } else {
        let mut v_v_5631_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
        let mut v_xs_x27_5633_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5634_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
        v_v_5631_ = lean_array_fget(v_xs_5626_, v_i_5627_);
        v___x_5632_ = lean_box(0);
        v_xs_x27_5633_ = lean_array_fset(v_xs_5626_, v_i_5627_, v___x_5632_);
        v___x_5634_ = lean_apply_1(v_f_5628_, v_v_5631_);
        v___x_5635_ = lean_array_fset(v_xs_x27_5633_, v_i_5627_, v___x_5634_);
        return v___x_5635_;
    }
}
pub unsafe fn l_Array_modify___boxed(
    mut v_00_u03b1_5636_: *mut LeanObject,
    mut v_xs_5637_: *mut LeanObject,
    mut v_i_5638_: *mut LeanObject,
    mut v_f_5639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5640_: *mut LeanObject = core::ptr::null_mut();
    v_res_5640_ = l_Array_modify(v_00_u03b1_5636_, v_xs_5637_, v_i_5638_, v_f_5639_);
    lean_dec(v_i_5638_);
    return v_res_5640_;
}
pub unsafe fn l_Array_modifyOp___redArg(
    mut v_xs_5641_: *mut LeanObject,
    mut v_idx_5642_: *mut LeanObject,
    mut v_f_5643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: u8 = 0;
    v___x_5644_ = lean_array_get_size(v_xs_5641_);
    v___x_5645_ = lean_nat_dec_lt(v_idx_5642_, v___x_5644_);
    if v___x_5645_ == 0 {
        lean_dec(v_f_5643_);
        return v_xs_5641_;
    } else {
        let mut v_v_5646_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5647_: *mut LeanObject = core::ptr::null_mut();
        let mut v_xs_x27_5648_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5649_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5650_: *mut LeanObject = core::ptr::null_mut();
        v_v_5646_ = lean_array_fget(v_xs_5641_, v_idx_5642_);
        v___x_5647_ = lean_box(0);
        v_xs_x27_5648_ = lean_array_fset(v_xs_5641_, v_idx_5642_, v___x_5647_);
        v___x_5649_ = lean_apply_1(v_f_5643_, v_v_5646_);
        v___x_5650_ = lean_array_fset(v_xs_x27_5648_, v_idx_5642_, v___x_5649_);
        return v___x_5650_;
    }
}
pub unsafe fn l_Array_modifyOp___redArg___boxed(
    mut v_xs_5651_: *mut LeanObject,
    mut v_idx_5652_: *mut LeanObject,
    mut v_f_5653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5654_: *mut LeanObject = core::ptr::null_mut();
    v_res_5654_ = l_Array_modifyOp___redArg(v_xs_5651_, v_idx_5652_, v_f_5653_);
    lean_dec(v_idx_5652_);
    return v_res_5654_;
}
pub unsafe fn l_Array_modifyOp(
    mut v_00_u03b1_5655_: *mut LeanObject,
    mut v_xs_5656_: *mut LeanObject,
    mut v_idx_5657_: *mut LeanObject,
    mut v_f_5658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: u8 = 0;
    v___x_5659_ = lean_array_get_size(v_xs_5656_);
    v___x_5660_ = lean_nat_dec_lt(v_idx_5657_, v___x_5659_);
    if v___x_5660_ == 0 {
        lean_dec(v_f_5658_);
        return v_xs_5656_;
    } else {
        let mut v_v_5661_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
        let mut v_xs_x27_5663_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
        v_v_5661_ = lean_array_fget(v_xs_5656_, v_idx_5657_);
        v___x_5662_ = lean_box(0);
        v_xs_x27_5663_ = lean_array_fset(v_xs_5656_, v_idx_5657_, v___x_5662_);
        v___x_5664_ = lean_apply_1(v_f_5658_, v_v_5661_);
        v___x_5665_ = lean_array_fset(v_xs_x27_5663_, v_idx_5657_, v___x_5664_);
        return v___x_5665_;
    }
}
pub unsafe fn l_Array_modifyOp___boxed(
    mut v_00_u03b1_5666_: *mut LeanObject,
    mut v_xs_5667_: *mut LeanObject,
    mut v_idx_5668_: *mut LeanObject,
    mut v_f_5669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5670_: *mut LeanObject = core::ptr::null_mut();
    v_res_5670_ = l_Array_modifyOp(v_00_u03b1_5666_, v_xs_5667_, v_idx_5668_, v_f_5669_);
    lean_dec(v_idx_5668_);
    return v_res_5670_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0___boxed(
    mut v_toApplicative_5671_: *mut LeanObject,
    mut v_i_5672_: *mut LeanObject,
    mut v_inst_5673_: *mut LeanObject,
    mut v_as_5674_: *mut LeanObject,
    mut v_f_5675_: *mut LeanObject,
    mut v_sz_5676_: *mut LeanObject,
    mut v_____do__lift_5677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5678_: usize = 0;
    let mut v_sz_boxed_5679_: usize = 0;
    let mut v_res_5680_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5678_ = lean_unbox_usize(v_i_5672_);
    lean_dec(v_i_5672_);
    v_sz_boxed_5679_ = lean_unbox_usize(v_sz_5676_);
    lean_dec(v_sz_5676_);
    v_res_5680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0(
        v_toApplicative_5671_,
        v_i_boxed_5678_,
        v_inst_5673_,
        v_as_5674_,
        v_f_5675_,
        v_sz_boxed_5679_,
        v_____do__lift_5677_,
    );
    return v_res_5680_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
    mut v_inst_5681_: *mut LeanObject,
    mut v_as_5682_: *mut LeanObject,
    mut v_f_5683_: *mut LeanObject,
    mut v_sz_5684_: usize,
    mut v_i_5685_: usize,
    mut v_b_5686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5687_: u8 = 0;
    v___x_5687_ = lean_usize_dec_lt(v_i_5685_, v_sz_5684_);
    if v___x_5687_ == 0 {
        let mut v_toApplicative_5688_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_5689_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5690_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_5683_);
        lean_dec_ref(v_as_5682_);
        v_toApplicative_5688_ = lean_ctor_get(v_inst_5681_, 0);
        lean_inc_ref(v_toApplicative_5688_);
        lean_dec_ref(v_inst_5681_);
        v_toPure_5689_ = lean_ctor_get(v_toApplicative_5688_, 1);
        lean_inc(v_toPure_5689_);
        lean_dec_ref(v_toApplicative_5688_);
        v___x_5690_ = lean_apply_2(v_toPure_5689_, lean_box(0), v_b_5686_);
        return v___x_5690_;
    } else {
        let mut v_toApplicative_5691_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_5692_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5693_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5694_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5695_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_5696_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5697_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_5691_ = lean_ctor_get(v_inst_5681_, 0);
        lean_inc_ref(v_toApplicative_5691_);
        v_toBind_5692_ = lean_ctor_get(v_inst_5681_, 1);
        lean_inc(v_toBind_5692_);
        v___x_5693_ = lean_box_usize(v_i_5685_);
        v___x_5694_ = lean_box_usize(v_sz_5684_);
        lean_inc(v_f_5683_);
        lean_inc_ref(v_as_5682_);
        v___f_5695_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 6);
        lean_closure_set(v___f_5695_, 0, v_toApplicative_5691_);
        lean_closure_set(v___f_5695_, 1, v___x_5693_);
        lean_closure_set(v___f_5695_, 2, v_inst_5681_);
        lean_closure_set(v___f_5695_, 3, v_as_5682_);
        lean_closure_set(v___f_5695_, 4, v_f_5683_);
        lean_closure_set(v___f_5695_, 5, v___x_5694_);
        v_a_5696_ = lean_array_uget(v_as_5682_, v_i_5685_);
        lean_dec_ref(v_as_5682_);
        v___x_5697_ = lean_apply_3(v_f_5683_, v_a_5696_, lean_box(0), v_b_5686_);
        v___x_5698_ = lean_apply_4(
            v_toBind_5692_,
            lean_box(0),
            lean_box(0),
            v___x_5697_,
            v___f_5695_,
        );
        return v___x_5698_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0(
    mut v_toApplicative_5699_: *mut LeanObject,
    mut v_i_5700_: usize,
    mut v_inst_5701_: *mut LeanObject,
    mut v_as_5702_: *mut LeanObject,
    mut v_f_5703_: *mut LeanObject,
    mut v_sz_5704_: usize,
    mut v_____do__lift_5705_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_5705_) == 0 {
        let mut v_a_5706_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_5707_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5708_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_5703_);
        lean_dec_ref(v_as_5702_);
        lean_dec_ref(v_inst_5701_);
        v_a_5706_ = lean_ctor_get(v_____do__lift_5705_, 0);
        lean_inc(v_a_5706_);
        lean_dec_ref_known(v_____do__lift_5705_, 1);
        v_toPure_5707_ = lean_ctor_get(v_toApplicative_5699_, 1);
        lean_inc(v_toPure_5707_);
        lean_dec_ref(v_toApplicative_5699_);
        v___x_5708_ = lean_apply_2(v_toPure_5707_, lean_box(0), v_a_5706_);
        return v___x_5708_;
    } else {
        let mut v_a_5709_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5710_: usize = 0;
        let mut v___x_5711_: usize = 0;
        let mut v___x_5712_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_5699_);
        v_a_5709_ = lean_ctor_get(v_____do__lift_5705_, 0);
        lean_inc(v_a_5709_);
        lean_dec_ref_known(v_____do__lift_5705_, 1);
        v___x_5710_ = 1usize;
        v___x_5711_ = lean_usize_add(v_i_5700_, v___x_5710_);
        v___x_5712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
            v_inst_5701_,
            v_as_5702_,
            v_f_5703_,
            v_sz_5704_,
            v___x_5711_,
            v_a_5709_,
        );
        return v___x_5712_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___boxed(
    mut v_inst_5713_: *mut LeanObject,
    mut v_as_5714_: *mut LeanObject,
    mut v_f_5715_: *mut LeanObject,
    mut v_sz_5716_: *mut LeanObject,
    mut v_i_5717_: *mut LeanObject,
    mut v_b_5718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5719_: usize = 0;
    let mut v_i_boxed_5720_: usize = 0;
    let mut v_res_5721_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5719_ = lean_unbox_usize(v_sz_5716_);
    lean_dec(v_sz_5716_);
    v_i_boxed_5720_ = lean_unbox_usize(v_i_5717_);
    lean_dec(v_i_5717_);
    v_res_5721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
        v_inst_5713_,
        v_as_5714_,
        v_f_5715_,
        v_sz_boxed_5719_,
        v_i_boxed_5720_,
        v_b_5718_,
    );
    return v_res_5721_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
    mut v_00_u03b1_5722_: *mut LeanObject,
    mut v_00_u03b2_5723_: *mut LeanObject,
    mut v_m_5724_: *mut LeanObject,
    mut v_inst_5725_: *mut LeanObject,
    mut v_as_5726_: *mut LeanObject,
    mut v_f_5727_: *mut LeanObject,
    mut v_sz_5728_: usize,
    mut v_i_5729_: usize,
    mut v_b_5730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    v___x_5731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
        v_inst_5725_,
        v_as_5726_,
        v_f_5727_,
        v_sz_5728_,
        v_i_5729_,
        v_b_5730_,
    );
    return v___x_5731_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___boxed(
    mut v_00_u03b1_5732_: *mut LeanObject,
    mut v_00_u03b2_5733_: *mut LeanObject,
    mut v_m_5734_: *mut LeanObject,
    mut v_inst_5735_: *mut LeanObject,
    mut v_as_5736_: *mut LeanObject,
    mut v_f_5737_: *mut LeanObject,
    mut v_sz_5738_: *mut LeanObject,
    mut v_i_5739_: *mut LeanObject,
    mut v_b_5740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5741_: usize = 0;
    let mut v_i_boxed_5742_: usize = 0;
    let mut v_res_5743_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5741_ = lean_unbox_usize(v_sz_5738_);
    lean_dec(v_sz_5738_);
    v_i_boxed_5742_ = lean_unbox_usize(v_i_5739_);
    lean_dec(v_i_5739_);
    v_res_5743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        v_00_u03b1_5732_,
        v_00_u03b2_5733_,
        v_m_5734_,
        v_inst_5735_,
        v_as_5736_,
        v_f_5737_,
        v_sz_boxed_5741_,
        v_i_boxed_5742_,
        v_b_5740_,
    );
    return v_res_5743_;
}
pub unsafe fn l_Array_forIn_x27Unsafe___redArg(
    mut v_inst_5744_: *mut LeanObject,
    mut v_as_5745_: *mut LeanObject,
    mut v_b_5746_: *mut LeanObject,
    mut v_f_5747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_5748_: usize = 0;
    let mut v___x_5749_: usize = 0;
    let mut v___x_5750_: *mut LeanObject = core::ptr::null_mut();
    v_sz_5748_ = lean_array_size(v_as_5745_);
    v___x_5749_ = 0usize;
    v___x_5750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
        v_inst_5744_,
        v_as_5745_,
        v_f_5747_,
        v_sz_5748_,
        v___x_5749_,
        v_b_5746_,
    );
    return v___x_5750_;
}
pub unsafe fn l_Array_forIn_x27Unsafe(
    mut v_00_u03b1_5751_: *mut LeanObject,
    mut v_00_u03b2_5752_: *mut LeanObject,
    mut v_m_5753_: *mut LeanObject,
    mut v_inst_5754_: *mut LeanObject,
    mut v_as_5755_: *mut LeanObject,
    mut v_b_5756_: *mut LeanObject,
    mut v_f_5757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_5758_: usize = 0;
    let mut v___x_5759_: usize = 0;
    let mut v___x_5760_: *mut LeanObject = core::ptr::null_mut();
    v_sz_5758_ = lean_array_size(v_as_5755_);
    v___x_5759_ = 0usize;
    v___x_5760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
        v_inst_5754_,
        v_as_5755_,
        v_f_5757_,
        v_sz_5758_,
        v___x_5759_,
        v_b_5756_,
    );
    return v___x_5760_;
}
pub unsafe fn l_Array_forIn_x27_loop___redArg___lam__0___boxed(
    mut v_toPure_5761_: *mut LeanObject,
    mut v_inst_5762_: *mut LeanObject,
    mut v_as_5763_: *mut LeanObject,
    mut v_f_5764_: *mut LeanObject,
    mut v_n_5765_: *mut LeanObject,
    mut v_____do__lift_5766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5767_: *mut LeanObject = core::ptr::null_mut();
    v_res_5767_ = l_Array_forIn_x27_loop___redArg___lam__0(
        v_toPure_5761_,
        v_inst_5762_,
        v_as_5763_,
        v_f_5764_,
        v_n_5765_,
        v_____do__lift_5766_,
    );
    lean_dec(v_n_5765_);
    return v_res_5767_;
}
pub unsafe fn l_Array_forIn_x27_loop___redArg(
    mut v_inst_5768_: *mut LeanObject,
    mut v_as_5769_: *mut LeanObject,
    mut v_f_5770_: *mut LeanObject,
    mut v_i_5771_: *mut LeanObject,
    mut v_b_5772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_5776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5777_: u8 = 0;
    v_toApplicative_5773_ = lean_ctor_get(v_inst_5768_, 0);
    v_toBind_5774_ = lean_ctor_get(v_inst_5768_, 1);
    lean_inc(v_toBind_5774_);
    v_toPure_5775_ = lean_ctor_get(v_toApplicative_5773_, 1);
    lean_inc(v_toPure_5775_);
    v_zero_5776_ = lean_unsigned_to_nat(0);
    v_isZero_5777_ = lean_nat_dec_eq(v_i_5771_, v_zero_5776_);
    if v_isZero_5777_ == 1 {
        let mut v___x_5778_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_5774_);
        lean_dec(v_f_5770_);
        lean_dec_ref(v_as_5769_);
        lean_dec_ref(v_inst_5768_);
        v___x_5778_ = lean_apply_2(v_toPure_5775_, lean_box(0), v_b_5772_);
        return v___x_5778_;
    } else {
        let mut v_one_5779_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_5780_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5781_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5783_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5784_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5785_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5787_: *mut LeanObject = core::ptr::null_mut();
        v_one_5779_ = lean_unsigned_to_nat(1);
        v_n_5780_ = lean_nat_sub(v_i_5771_, v_one_5779_);
        lean_inc(v_n_5780_);
        lean_inc(v_f_5770_);
        lean_inc_ref(v_as_5769_);
        v___f_5781_ = lean_alloc_closure(
            l_Array_forIn_x27_loop___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_5781_, 0, v_toPure_5775_);
        lean_closure_set(v___f_5781_, 1, v_inst_5768_);
        lean_closure_set(v___f_5781_, 2, v_as_5769_);
        lean_closure_set(v___f_5781_, 3, v_f_5770_);
        lean_closure_set(v___f_5781_, 4, v_n_5780_);
        v___x_5782_ = lean_array_get_size(v_as_5769_);
        v___x_5783_ = lean_nat_sub(v___x_5782_, v_one_5779_);
        v___x_5784_ = lean_nat_sub(v___x_5783_, v_n_5780_);
        lean_dec(v_n_5780_);
        lean_dec(v___x_5783_);
        v___x_5785_ = lean_array_fget(v_as_5769_, v___x_5784_);
        lean_dec(v___x_5784_);
        lean_dec_ref(v_as_5769_);
        v___x_5786_ = lean_apply_3(v_f_5770_, v___x_5785_, lean_box(0), v_b_5772_);
        v___x_5787_ = lean_apply_4(
            v_toBind_5774_,
            lean_box(0),
            lean_box(0),
            v___x_5786_,
            v___f_5781_,
        );
        return v___x_5787_;
    }
}
pub unsafe fn l_Array_forIn_x27_loop___redArg___lam__0(
    mut v_toPure_5788_: *mut LeanObject,
    mut v_inst_5789_: *mut LeanObject,
    mut v_as_5790_: *mut LeanObject,
    mut v_f_5791_: *mut LeanObject,
    mut v_n_5792_: *mut LeanObject,
    mut v_____do__lift_5793_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_5793_) == 0 {
        let mut v_a_5794_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_5791_);
        lean_dec_ref(v_as_5790_);
        lean_dec_ref(v_inst_5789_);
        v_a_5794_ = lean_ctor_get(v_____do__lift_5793_, 0);
        lean_inc(v_a_5794_);
        lean_dec_ref_known(v_____do__lift_5793_, 1);
        v___x_5795_ = lean_apply_2(v_toPure_5788_, lean_box(0), v_a_5794_);
        return v___x_5795_;
    } else {
        let mut v_a_5796_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_5788_);
        v_a_5796_ = lean_ctor_get(v_____do__lift_5793_, 0);
        lean_inc(v_a_5796_);
        lean_dec_ref_known(v_____do__lift_5793_, 1);
        v___x_5797_ = l_Array_forIn_x27_loop___redArg(
            v_inst_5789_,
            v_as_5790_,
            v_f_5791_,
            v_n_5792_,
            v_a_5796_,
        );
        return v___x_5797_;
    }
}
pub unsafe fn l_Array_forIn_x27_loop___redArg___boxed(
    mut v_inst_5798_: *mut LeanObject,
    mut v_as_5799_: *mut LeanObject,
    mut v_f_5800_: *mut LeanObject,
    mut v_i_5801_: *mut LeanObject,
    mut v_b_5802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5803_: *mut LeanObject = core::ptr::null_mut();
    v_res_5803_ =
        l_Array_forIn_x27_loop___redArg(v_inst_5798_, v_as_5799_, v_f_5800_, v_i_5801_, v_b_5802_);
    lean_dec(v_i_5801_);
    return v_res_5803_;
}
pub unsafe fn l_Array_forIn_x27_loop(
    mut v_00_u03b1_5804_: *mut LeanObject,
    mut v_00_u03b2_5805_: *mut LeanObject,
    mut v_m_5806_: *mut LeanObject,
    mut v_inst_5807_: *mut LeanObject,
    mut v_as_5808_: *mut LeanObject,
    mut v_f_5809_: *mut LeanObject,
    mut v_i_5810_: *mut LeanObject,
    mut v_h_5811_: *mut LeanObject,
    mut v_b_5812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5813_: *mut LeanObject = core::ptr::null_mut();
    v___x_5813_ =
        l_Array_forIn_x27_loop___redArg(v_inst_5807_, v_as_5808_, v_f_5809_, v_i_5810_, v_b_5812_);
    return v___x_5813_;
}
pub unsafe fn l_Array_forIn_x27_loop___boxed(
    mut v_00_u03b1_5814_: *mut LeanObject,
    mut v_00_u03b2_5815_: *mut LeanObject,
    mut v_m_5816_: *mut LeanObject,
    mut v_inst_5817_: *mut LeanObject,
    mut v_as_5818_: *mut LeanObject,
    mut v_f_5819_: *mut LeanObject,
    mut v_i_5820_: *mut LeanObject,
    mut v_h_5821_: *mut LeanObject,
    mut v_b_5822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5823_: *mut LeanObject = core::ptr::null_mut();
    v_res_5823_ = l_Array_forIn_x27_loop(
        v_00_u03b1_5814_,
        v_00_u03b2_5815_,
        v_m_5816_,
        v_inst_5817_,
        v_as_5818_,
        v_f_5819_,
        v_i_5820_,
        v_h_5821_,
        v_b_5822_,
    );
    lean_dec(v_i_5820_);
    return v_res_5823_;
}
pub unsafe fn l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(
    mut v_inst_5824_: *mut LeanObject,
    mut v_00_u03b2_5825_: *mut LeanObject,
    mut v___y_5826_: *mut LeanObject,
    mut v___y_5827_: *mut LeanObject,
    mut v___y_5828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_5829_: usize = 0;
    let mut v___x_5830_: usize = 0;
    let mut v___x_5831_: *mut LeanObject = core::ptr::null_mut();
    v_sz_5829_ = lean_array_size(v___y_5826_);
    v___x_5830_ = 0usize;
    v___x_5831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
        v_inst_5824_,
        v___y_5826_,
        v___y_5828_,
        v_sz_5829_,
        v___x_5830_,
        v___y_5827_,
    );
    return v___x_5831_;
}
pub unsafe fn l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg(
    mut v_inst_5832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5833_: *mut LeanObject = core::ptr::null_mut();
    v___f_5833_ = lean_alloc_closure(
        l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_5833_, 0, v_inst_5832_);
    return v___f_5833_;
}
pub unsafe fn l_Array_instForIn_x27InferInstanceMembershipOfMonad(
    mut v_00_u03b1_5834_: *mut LeanObject,
    mut v_m_5835_: *mut LeanObject,
    mut v_inst_5836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5837_: *mut LeanObject = core::ptr::null_mut();
    v___f_5837_ = lean_alloc_closure(
        l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_5837_, 0, v_inst_5836_);
    return v___f_5837_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0___boxed(
    mut v_i_5838_: *mut LeanObject,
    mut v_inst_5839_: *mut LeanObject,
    mut v_f_5840_: *mut LeanObject,
    mut v_as_5841_: *mut LeanObject,
    mut v_stop_5842_: *mut LeanObject,
    mut v_____do__lift_5843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5844_: usize = 0;
    let mut v_stop_boxed_5845_: usize = 0;
    let mut v_res_5846_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5844_ = lean_unbox_usize(v_i_5838_);
    lean_dec(v_i_5838_);
    v_stop_boxed_5845_ = lean_unbox_usize(v_stop_5842_);
    lean_dec(v_stop_5842_);
    v_res_5846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0(
        v_i_boxed_5844_,
        v_inst_5839_,
        v_f_5840_,
        v_as_5841_,
        v_stop_boxed_5845_,
        v_____do__lift_5843_,
    );
    return v_res_5846_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
    mut v_inst_5847_: *mut LeanObject,
    mut v_f_5848_: *mut LeanObject,
    mut v_as_5849_: *mut LeanObject,
    mut v_i_5850_: usize,
    mut v_stop_5851_: usize,
    mut v_b_5852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5853_: u8 = 0;
    v___x_5853_ = lean_usize_dec_eq(v_i_5850_, v_stop_5851_);
    if v___x_5853_ == 0 {
        let mut v_toBind_5854_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5855_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5856_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5857_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5858_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5859_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_5854_ = lean_ctor_get(v_inst_5847_, 1);
        lean_inc(v_toBind_5854_);
        v___x_5855_ = lean_box_usize(v_i_5850_);
        v___x_5856_ = lean_box_usize(v_stop_5851_);
        lean_inc_ref(v_as_5849_);
        lean_inc(v_f_5848_);
        v___f_5857_ = lean_alloc_closure(
            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_5857_, 0, v___x_5855_);
        lean_closure_set(v___f_5857_, 1, v_inst_5847_);
        lean_closure_set(v___f_5857_, 2, v_f_5848_);
        lean_closure_set(v___f_5857_, 3, v_as_5849_);
        lean_closure_set(v___f_5857_, 4, v___x_5856_);
        v___x_5858_ = lean_array_uget(v_as_5849_, v_i_5850_);
        lean_dec_ref(v_as_5849_);
        v___x_5859_ = lean_apply_2(v_f_5848_, v_b_5852_, v___x_5858_);
        v___x_5860_ = lean_apply_4(
            v_toBind_5854_,
            lean_box(0),
            lean_box(0),
            v___x_5859_,
            v___f_5857_,
        );
        return v___x_5860_;
    } else {
        let mut v_toApplicative_5861_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_5862_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5863_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_as_5849_);
        lean_dec(v_f_5848_);
        v_toApplicative_5861_ = lean_ctor_get(v_inst_5847_, 0);
        lean_inc_ref(v_toApplicative_5861_);
        lean_dec_ref(v_inst_5847_);
        v_toPure_5862_ = lean_ctor_get(v_toApplicative_5861_, 1);
        lean_inc(v_toPure_5862_);
        lean_dec_ref(v_toApplicative_5861_);
        v___x_5863_ = lean_apply_2(v_toPure_5862_, lean_box(0), v_b_5852_);
        return v___x_5863_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0(
    mut v_i_5864_: usize,
    mut v_inst_5865_: *mut LeanObject,
    mut v_f_5866_: *mut LeanObject,
    mut v_as_5867_: *mut LeanObject,
    mut v_stop_5868_: usize,
    mut v_____do__lift_5869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5870_: usize = 0;
    let mut v___x_5871_: usize = 0;
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    v___x_5870_ = 1usize;
    v___x_5871_ = lean_usize_add(v_i_5864_, v___x_5870_);
    v___x_5872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
        v_inst_5865_,
        v_f_5866_,
        v_as_5867_,
        v___x_5871_,
        v_stop_5868_,
        v_____do__lift_5869_,
    );
    return v___x_5872_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___boxed(
    mut v_inst_5873_: *mut LeanObject,
    mut v_f_5874_: *mut LeanObject,
    mut v_as_5875_: *mut LeanObject,
    mut v_i_5876_: *mut LeanObject,
    mut v_stop_5877_: *mut LeanObject,
    mut v_b_5878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5879_: usize = 0;
    let mut v_stop_boxed_5880_: usize = 0;
    let mut v_res_5881_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5879_ = lean_unbox_usize(v_i_5876_);
    lean_dec(v_i_5876_);
    v_stop_boxed_5880_ = lean_unbox_usize(v_stop_5877_);
    lean_dec(v_stop_5877_);
    v_res_5881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
        v_inst_5873_,
        v_f_5874_,
        v_as_5875_,
        v_i_boxed_5879_,
        v_stop_boxed_5880_,
        v_b_5878_,
    );
    return v_res_5881_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
    mut v_00_u03b1_5882_: *mut LeanObject,
    mut v_00_u03b2_5883_: *mut LeanObject,
    mut v_m_5884_: *mut LeanObject,
    mut v_inst_5885_: *mut LeanObject,
    mut v_f_5886_: *mut LeanObject,
    mut v_as_5887_: *mut LeanObject,
    mut v_i_5888_: usize,
    mut v_stop_5889_: usize,
    mut v_b_5890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5891_: *mut LeanObject = core::ptr::null_mut();
    v___x_5891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
        v_inst_5885_,
        v_f_5886_,
        v_as_5887_,
        v_i_5888_,
        v_stop_5889_,
        v_b_5890_,
    );
    return v___x_5891_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___boxed(
    mut v_00_u03b1_5892_: *mut LeanObject,
    mut v_00_u03b2_5893_: *mut LeanObject,
    mut v_m_5894_: *mut LeanObject,
    mut v_inst_5895_: *mut LeanObject,
    mut v_f_5896_: *mut LeanObject,
    mut v_as_5897_: *mut LeanObject,
    mut v_i_5898_: *mut LeanObject,
    mut v_stop_5899_: *mut LeanObject,
    mut v_b_5900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5901_: usize = 0;
    let mut v_stop_boxed_5902_: usize = 0;
    let mut v_res_5903_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5901_ = lean_unbox_usize(v_i_5898_);
    lean_dec(v_i_5898_);
    v_stop_boxed_5902_ = lean_unbox_usize(v_stop_5899_);
    lean_dec(v_stop_5899_);
    v_res_5903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
        v_00_u03b1_5892_,
        v_00_u03b2_5893_,
        v_m_5894_,
        v_inst_5895_,
        v_f_5896_,
        v_as_5897_,
        v_i_boxed_5901_,
        v_stop_boxed_5902_,
        v_b_5900_,
    );
    return v_res_5903_;
}
pub unsafe fn l_Array_foldlMUnsafe___redArg(
    mut v_inst_5904_: *mut LeanObject,
    mut v_f_5905_: *mut LeanObject,
    mut v_init_5906_: *mut LeanObject,
    mut v_as_5907_: *mut LeanObject,
    mut v_start_5908_: *mut LeanObject,
    mut v_stop_5909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5910_: u8 = 0;
    v___x_5910_ = lean_nat_dec_lt(v_start_5908_, v_stop_5909_);
    if v___x_5910_ == 0 {
        let mut v_toApplicative_5911_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_5912_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5913_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_as_5907_);
        lean_dec(v_f_5905_);
        v_toApplicative_5911_ = lean_ctor_get(v_inst_5904_, 0);
        lean_inc_ref(v_toApplicative_5911_);
        lean_dec_ref(v_inst_5904_);
        v_toPure_5912_ = lean_ctor_get(v_toApplicative_5911_, 1);
        lean_inc(v_toPure_5912_);
        lean_dec_ref(v_toApplicative_5911_);
        v___x_5913_ = lean_apply_2(v_toPure_5912_, lean_box(0), v_init_5906_);
        return v___x_5913_;
    } else {
        let mut v___x_5914_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5915_: u8 = 0;
        v___x_5914_ = lean_array_get_size(v_as_5907_);
        v___x_5915_ = lean_nat_dec_le(v_stop_5909_, v___x_5914_);
        if v___x_5915_ == 0 {
            let mut v___x_5916_: u8 = 0;
            v___x_5916_ = lean_nat_dec_lt(v_start_5908_, v___x_5914_);
            if v___x_5916_ == 0 {
                let mut v_toApplicative_5917_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_5918_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5919_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_as_5907_);
                lean_dec(v_f_5905_);
                v_toApplicative_5917_ = lean_ctor_get(v_inst_5904_, 0);
                lean_inc_ref(v_toApplicative_5917_);
                lean_dec_ref(v_inst_5904_);
                v_toPure_5918_ = lean_ctor_get(v_toApplicative_5917_, 1);
                lean_inc(v_toPure_5918_);
                lean_dec_ref(v_toApplicative_5917_);
                v___x_5919_ = lean_apply_2(v_toPure_5918_, lean_box(0), v_init_5906_);
                return v___x_5919_;
            } else {
                let mut v___x_5920_: usize = 0;
                let mut v___x_5921_: usize = 0;
                let mut v___x_5922_: *mut LeanObject = core::ptr::null_mut();
                v___x_5920_ = lean_usize_of_nat(v_start_5908_);
                v___x_5921_ = lean_usize_of_nat(v___x_5914_);
                v___x_5922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v_inst_5904_,
                    v_f_5905_,
                    v_as_5907_,
                    v___x_5920_,
                    v___x_5921_,
                    v_init_5906_,
                );
                return v___x_5922_;
            }
        } else {
            let mut v___x_5923_: usize = 0;
            let mut v___x_5924_: usize = 0;
            let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
            v___x_5923_ = lean_usize_of_nat(v_start_5908_);
            v___x_5924_ = lean_usize_of_nat(v_stop_5909_);
            v___x_5925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v_inst_5904_,
                v_f_5905_,
                v_as_5907_,
                v___x_5923_,
                v___x_5924_,
                v_init_5906_,
            );
            return v___x_5925_;
        }
    }
}
pub unsafe fn l_Array_foldlMUnsafe___redArg___boxed(
    mut v_inst_5926_: *mut LeanObject,
    mut v_f_5927_: *mut LeanObject,
    mut v_init_5928_: *mut LeanObject,
    mut v_as_5929_: *mut LeanObject,
    mut v_start_5930_: *mut LeanObject,
    mut v_stop_5931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5932_: *mut LeanObject = core::ptr::null_mut();
    v_res_5932_ = l_Array_foldlMUnsafe___redArg(
        v_inst_5926_,
        v_f_5927_,
        v_init_5928_,
        v_as_5929_,
        v_start_5930_,
        v_stop_5931_,
    );
    lean_dec(v_stop_5931_);
    lean_dec(v_start_5930_);
    return v_res_5932_;
}
pub unsafe fn l_Array_foldlMUnsafe(
    mut v_00_u03b1_5933_: *mut LeanObject,
    mut v_00_u03b2_5934_: *mut LeanObject,
    mut v_m_5935_: *mut LeanObject,
    mut v_inst_5936_: *mut LeanObject,
    mut v_f_5937_: *mut LeanObject,
    mut v_init_5938_: *mut LeanObject,
    mut v_as_5939_: *mut LeanObject,
    mut v_start_5940_: *mut LeanObject,
    mut v_stop_5941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5942_: u8 = 0;
    v___x_5942_ = lean_nat_dec_lt(v_start_5940_, v_stop_5941_);
    if v___x_5942_ == 0 {
        let mut v_toApplicative_5943_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_5944_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5945_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_as_5939_);
        lean_dec(v_f_5937_);
        v_toApplicative_5943_ = lean_ctor_get(v_inst_5936_, 0);
        lean_inc_ref(v_toApplicative_5943_);
        lean_dec_ref(v_inst_5936_);
        v_toPure_5944_ = lean_ctor_get(v_toApplicative_5943_, 1);
        lean_inc(v_toPure_5944_);
        lean_dec_ref(v_toApplicative_5943_);
        v___x_5945_ = lean_apply_2(v_toPure_5944_, lean_box(0), v_init_5938_);
        return v___x_5945_;
    } else {
        let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5947_: u8 = 0;
        v___x_5946_ = lean_array_get_size(v_as_5939_);
        v___x_5947_ = lean_nat_dec_le(v_stop_5941_, v___x_5946_);
        if v___x_5947_ == 0 {
            let mut v___x_5948_: u8 = 0;
            v___x_5948_ = lean_nat_dec_lt(v_start_5940_, v___x_5946_);
            if v___x_5948_ == 0 {
                let mut v_toApplicative_5949_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_5950_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_as_5939_);
                lean_dec(v_f_5937_);
                v_toApplicative_5949_ = lean_ctor_get(v_inst_5936_, 0);
                lean_inc_ref(v_toApplicative_5949_);
                lean_dec_ref(v_inst_5936_);
                v_toPure_5950_ = lean_ctor_get(v_toApplicative_5949_, 1);
                lean_inc(v_toPure_5950_);
                lean_dec_ref(v_toApplicative_5949_);
                v___x_5951_ = lean_apply_2(v_toPure_5950_, lean_box(0), v_init_5938_);
                return v___x_5951_;
            } else {
                let mut v___x_5952_: usize = 0;
                let mut v___x_5953_: usize = 0;
                let mut v___x_5954_: *mut LeanObject = core::ptr::null_mut();
                v___x_5952_ = lean_usize_of_nat(v_start_5940_);
                v___x_5953_ = lean_usize_of_nat(v___x_5946_);
                v___x_5954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v_inst_5936_,
                    v_f_5937_,
                    v_as_5939_,
                    v___x_5952_,
                    v___x_5953_,
                    v_init_5938_,
                );
                return v___x_5954_;
            }
        } else {
            let mut v___x_5955_: usize = 0;
            let mut v___x_5956_: usize = 0;
            let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
            v___x_5955_ = lean_usize_of_nat(v_start_5940_);
            v___x_5956_ = lean_usize_of_nat(v_stop_5941_);
            v___x_5957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v_inst_5936_,
                v_f_5937_,
                v_as_5939_,
                v___x_5955_,
                v___x_5956_,
                v_init_5938_,
            );
            return v___x_5957_;
        }
    }
}
pub unsafe fn l_Array_foldlMUnsafe___boxed(
    mut v_00_u03b1_5958_: *mut LeanObject,
    mut v_00_u03b2_5959_: *mut LeanObject,
    mut v_m_5960_: *mut LeanObject,
    mut v_inst_5961_: *mut LeanObject,
    mut v_f_5962_: *mut LeanObject,
    mut v_init_5963_: *mut LeanObject,
    mut v_as_5964_: *mut LeanObject,
    mut v_start_5965_: *mut LeanObject,
    mut v_stop_5966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5967_: *mut LeanObject = core::ptr::null_mut();
    v_res_5967_ = l_Array_foldlMUnsafe(
        v_00_u03b1_5958_,
        v_00_u03b2_5959_,
        v_m_5960_,
        v_inst_5961_,
        v_f_5962_,
        v_init_5963_,
        v_as_5964_,
        v_start_5965_,
        v_stop_5966_,
    );
    lean_dec(v_stop_5966_);
    lean_dec(v_start_5965_);
    return v_res_5967_;
}
pub unsafe fn l_Array_foldlM_loop___redArg___lam__0___boxed(
    mut v_j_5968_: *mut LeanObject,
    mut v_inst_5969_: *mut LeanObject,
    mut v_f_5970_: *mut LeanObject,
    mut v_as_5971_: *mut LeanObject,
    mut v_stop_5972_: *mut LeanObject,
    mut v_n_5973_: *mut LeanObject,
    mut v_____do__lift_5974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5975_: *mut LeanObject = core::ptr::null_mut();
    v_res_5975_ = l_Array_foldlM_loop___redArg___lam__0(
        v_j_5968_,
        v_inst_5969_,
        v_f_5970_,
        v_as_5971_,
        v_stop_5972_,
        v_n_5973_,
        v_____do__lift_5974_,
    );
    lean_dec(v_n_5973_);
    lean_dec(v_j_5968_);
    return v_res_5975_;
}
pub unsafe fn l_Array_foldlM_loop___redArg(
    mut v_inst_5976_: *mut LeanObject,
    mut v_f_5977_: *mut LeanObject,
    mut v_as_5978_: *mut LeanObject,
    mut v_stop_5979_: *mut LeanObject,
    mut v_i_5980_: *mut LeanObject,
    mut v_j_5981_: *mut LeanObject,
    mut v_b_5982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5983_: u8 = 0;
    v___x_5983_ = lean_nat_dec_lt(v_j_5981_, v_stop_5979_);
    if v___x_5983_ == 0 {
        let mut v_toApplicative_5984_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_5985_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_j_5981_);
        lean_dec(v_stop_5979_);
        lean_dec_ref(v_as_5978_);
        lean_dec(v_f_5977_);
        v_toApplicative_5984_ = lean_ctor_get(v_inst_5976_, 0);
        lean_inc_ref(v_toApplicative_5984_);
        lean_dec_ref(v_inst_5976_);
        v_toPure_5985_ = lean_ctor_get(v_toApplicative_5984_, 1);
        lean_inc(v_toPure_5985_);
        lean_dec_ref(v_toApplicative_5984_);
        v___x_5986_ = lean_apply_2(v_toPure_5985_, lean_box(0), v_b_5982_);
        return v___x_5986_;
    } else {
        let mut v_zero_5987_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_5988_: u8 = 0;
        v_zero_5987_ = lean_unsigned_to_nat(0);
        v_isZero_5988_ = lean_nat_dec_eq(v_i_5980_, v_zero_5987_);
        if v_isZero_5988_ == 1 {
            let mut v_toApplicative_5989_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_5990_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5991_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_j_5981_);
            lean_dec(v_stop_5979_);
            lean_dec_ref(v_as_5978_);
            lean_dec(v_f_5977_);
            v_toApplicative_5989_ = lean_ctor_get(v_inst_5976_, 0);
            lean_inc_ref(v_toApplicative_5989_);
            lean_dec_ref(v_inst_5976_);
            v_toPure_5990_ = lean_ctor_get(v_toApplicative_5989_, 1);
            lean_inc(v_toPure_5990_);
            lean_dec_ref(v_toApplicative_5989_);
            v___x_5991_ = lean_apply_2(v_toPure_5990_, lean_box(0), v_b_5982_);
            return v___x_5991_;
        } else {
            let mut v_toBind_5992_: *mut LeanObject = core::ptr::null_mut();
            let mut v_one_5993_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_5994_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5995_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5997_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5998_: *mut LeanObject = core::ptr::null_mut();
            v_toBind_5992_ = lean_ctor_get(v_inst_5976_, 1);
            lean_inc(v_toBind_5992_);
            v_one_5993_ = lean_unsigned_to_nat(1);
            v_n_5994_ = lean_nat_sub(v_i_5980_, v_one_5993_);
            lean_inc_ref(v_as_5978_);
            lean_inc(v_f_5977_);
            lean_inc(v_j_5981_);
            v___f_5995_ = lean_alloc_closure(
                l_Array_foldlM_loop___redArg___lam__0___boxed as *mut core::ffi::c_void,
                7,
                6,
            );
            lean_closure_set(v___f_5995_, 0, v_j_5981_);
            lean_closure_set(v___f_5995_, 1, v_inst_5976_);
            lean_closure_set(v___f_5995_, 2, v_f_5977_);
            lean_closure_set(v___f_5995_, 3, v_as_5978_);
            lean_closure_set(v___f_5995_, 4, v_stop_5979_);
            lean_closure_set(v___f_5995_, 5, v_n_5994_);
            v___x_5996_ = lean_array_fget(v_as_5978_, v_j_5981_);
            lean_dec(v_j_5981_);
            lean_dec_ref(v_as_5978_);
            v___x_5997_ = lean_apply_2(v_f_5977_, v_b_5982_, v___x_5996_);
            v___x_5998_ = lean_apply_4(
                v_toBind_5992_,
                lean_box(0),
                lean_box(0),
                v___x_5997_,
                v___f_5995_,
            );
            return v___x_5998_;
        }
    }
}
pub unsafe fn l_Array_foldlM_loop___redArg___lam__0(
    mut v_j_5999_: *mut LeanObject,
    mut v_inst_6000_: *mut LeanObject,
    mut v_f_6001_: *mut LeanObject,
    mut v_as_6002_: *mut LeanObject,
    mut v_stop_6003_: *mut LeanObject,
    mut v_n_6004_: *mut LeanObject,
    mut v_____do__lift_6005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut LeanObject = core::ptr::null_mut();
    v___x_6006_ = lean_unsigned_to_nat(1);
    v___x_6007_ = lean_nat_add(v_j_5999_, v___x_6006_);
    v___x_6008_ = l_Array_foldlM_loop___redArg(
        v_inst_6000_,
        v_f_6001_,
        v_as_6002_,
        v_stop_6003_,
        v_n_6004_,
        v___x_6007_,
        v_____do__lift_6005_,
    );
    return v___x_6008_;
}
pub unsafe fn l_Array_foldlM_loop___redArg___boxed(
    mut v_inst_6009_: *mut LeanObject,
    mut v_f_6010_: *mut LeanObject,
    mut v_as_6011_: *mut LeanObject,
    mut v_stop_6012_: *mut LeanObject,
    mut v_i_6013_: *mut LeanObject,
    mut v_j_6014_: *mut LeanObject,
    mut v_b_6015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6016_: *mut LeanObject = core::ptr::null_mut();
    v_res_6016_ = l_Array_foldlM_loop___redArg(
        v_inst_6009_,
        v_f_6010_,
        v_as_6011_,
        v_stop_6012_,
        v_i_6013_,
        v_j_6014_,
        v_b_6015_,
    );
    lean_dec(v_i_6013_);
    return v_res_6016_;
}
pub unsafe fn l_Array_foldlM_loop(
    mut v_00_u03b1_6017_: *mut LeanObject,
    mut v_00_u03b2_6018_: *mut LeanObject,
    mut v_m_6019_: *mut LeanObject,
    mut v_inst_6020_: *mut LeanObject,
    mut v_f_6021_: *mut LeanObject,
    mut v_as_6022_: *mut LeanObject,
    mut v_stop_6023_: *mut LeanObject,
    mut v_h_6024_: *mut LeanObject,
    mut v_i_6025_: *mut LeanObject,
    mut v_j_6026_: *mut LeanObject,
    mut v_b_6027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6028_: *mut LeanObject = core::ptr::null_mut();
    v___x_6028_ = l_Array_foldlM_loop___redArg(
        v_inst_6020_,
        v_f_6021_,
        v_as_6022_,
        v_stop_6023_,
        v_i_6025_,
        v_j_6026_,
        v_b_6027_,
    );
    return v___x_6028_;
}
pub unsafe fn l_Array_foldlM_loop___boxed(
    mut v_00_u03b1_6029_: *mut LeanObject,
    mut v_00_u03b2_6030_: *mut LeanObject,
    mut v_m_6031_: *mut LeanObject,
    mut v_inst_6032_: *mut LeanObject,
    mut v_f_6033_: *mut LeanObject,
    mut v_as_6034_: *mut LeanObject,
    mut v_stop_6035_: *mut LeanObject,
    mut v_h_6036_: *mut LeanObject,
    mut v_i_6037_: *mut LeanObject,
    mut v_j_6038_: *mut LeanObject,
    mut v_b_6039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6040_: *mut LeanObject = core::ptr::null_mut();
    v_res_6040_ = l_Array_foldlM_loop(
        v_00_u03b1_6029_,
        v_00_u03b2_6030_,
        v_m_6031_,
        v_inst_6032_,
        v_f_6033_,
        v_as_6034_,
        v_stop_6035_,
        v_h_6036_,
        v_i_6037_,
        v_j_6038_,
        v_b_6039_,
    );
    lean_dec(v_i_6037_);
    return v_res_6040_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0___boxed(
    mut v_inst_6041_: *mut LeanObject,
    mut v_f_6042_: *mut LeanObject,
    mut v_as_6043_: *mut LeanObject,
    mut v___x_6044_: *mut LeanObject,
    mut v_stop_6045_: *mut LeanObject,
    mut v_____do__lift_6046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_94__boxed_6047_: usize = 0;
    let mut v_stop_boxed_6048_: usize = 0;
    let mut v_res_6049_: *mut LeanObject = core::ptr::null_mut();
    v___x_94__boxed_6047_ = lean_unbox_usize(v___x_6044_);
    lean_dec(v___x_6044_);
    v_stop_boxed_6048_ = lean_unbox_usize(v_stop_6045_);
    lean_dec(v_stop_6045_);
    v_res_6049_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0(
        v_inst_6041_,
        v_f_6042_,
        v_as_6043_,
        v___x_94__boxed_6047_,
        v_stop_boxed_6048_,
        v_____do__lift_6046_,
    );
    return v_res_6049_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
    mut v_inst_6050_: *mut LeanObject,
    mut v_f_6051_: *mut LeanObject,
    mut v_as_6052_: *mut LeanObject,
    mut v_i_6053_: usize,
    mut v_stop_6054_: usize,
    mut v_b_6055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6056_: u8 = 0;
    v___x_6056_ = lean_usize_dec_eq(v_i_6053_, v_stop_6054_);
    if v___x_6056_ == 0 {
        let mut v_toBind_6057_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6058_: usize = 0;
        let mut v___x_6059_: usize = 0;
        let mut v___x_6060_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_6062_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6063_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6065_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_6057_ = lean_ctor_get(v_inst_6050_, 1);
        lean_inc(v_toBind_6057_);
        v___x_6058_ = 1usize;
        v___x_6059_ = lean_usize_sub(v_i_6053_, v___x_6058_);
        v___x_6060_ = lean_box_usize(v___x_6059_);
        v___x_6061_ = lean_box_usize(v_stop_6054_);
        lean_inc_ref(v_as_6052_);
        lean_inc(v_f_6051_);
        v___f_6062_ = lean_alloc_closure(
            l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_6062_, 0, v_inst_6050_);
        lean_closure_set(v___f_6062_, 1, v_f_6051_);
        lean_closure_set(v___f_6062_, 2, v_as_6052_);
        lean_closure_set(v___f_6062_, 3, v___x_6060_);
        lean_closure_set(v___f_6062_, 4, v___x_6061_);
        v___x_6063_ = lean_array_uget(v_as_6052_, v___x_6059_);
        lean_dec_ref(v_as_6052_);
        v___x_6064_ = lean_apply_2(v_f_6051_, v___x_6063_, v_b_6055_);
        v___x_6065_ = lean_apply_4(
            v_toBind_6057_,
            lean_box(0),
            lean_box(0),
            v___x_6064_,
            v___f_6062_,
        );
        return v___x_6065_;
    } else {
        let mut v_toApplicative_6066_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_6067_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_as_6052_);
        lean_dec(v_f_6051_);
        v_toApplicative_6066_ = lean_ctor_get(v_inst_6050_, 0);
        lean_inc_ref(v_toApplicative_6066_);
        lean_dec_ref(v_inst_6050_);
        v_toPure_6067_ = lean_ctor_get(v_toApplicative_6066_, 1);
        lean_inc(v_toPure_6067_);
        lean_dec_ref(v_toApplicative_6066_);
        v___x_6068_ = lean_apply_2(v_toPure_6067_, lean_box(0), v_b_6055_);
        return v___x_6068_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0(
    mut v_inst_6069_: *mut LeanObject,
    mut v_f_6070_: *mut LeanObject,
    mut v_as_6071_: *mut LeanObject,
    mut v___x_6072_: usize,
    mut v_stop_6073_: usize,
    mut v_____do__lift_6074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6075_: *mut LeanObject = core::ptr::null_mut();
    v___x_6075_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
        v_inst_6069_,
        v_f_6070_,
        v_as_6071_,
        v___x_6072_,
        v_stop_6073_,
        v_____do__lift_6074_,
    );
    return v___x_6075_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___boxed(
    mut v_inst_6076_: *mut LeanObject,
    mut v_f_6077_: *mut LeanObject,
    mut v_as_6078_: *mut LeanObject,
    mut v_i_6079_: *mut LeanObject,
    mut v_stop_6080_: *mut LeanObject,
    mut v_b_6081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6082_: usize = 0;
    let mut v_stop_boxed_6083_: usize = 0;
    let mut v_res_6084_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6082_ = lean_unbox_usize(v_i_6079_);
    lean_dec(v_i_6079_);
    v_stop_boxed_6083_ = lean_unbox_usize(v_stop_6080_);
    lean_dec(v_stop_6080_);
    v_res_6084_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
        v_inst_6076_,
        v_f_6077_,
        v_as_6078_,
        v_i_boxed_6082_,
        v_stop_boxed_6083_,
        v_b_6081_,
    );
    return v_res_6084_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
    mut v_00_u03b1_6085_: *mut LeanObject,
    mut v_00_u03b2_6086_: *mut LeanObject,
    mut v_m_6087_: *mut LeanObject,
    mut v_inst_6088_: *mut LeanObject,
    mut v_f_6089_: *mut LeanObject,
    mut v_as_6090_: *mut LeanObject,
    mut v_i_6091_: usize,
    mut v_stop_6092_: usize,
    mut v_b_6093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    v___x_6094_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
        v_inst_6088_,
        v_f_6089_,
        v_as_6090_,
        v_i_6091_,
        v_stop_6092_,
        v_b_6093_,
    );
    return v___x_6094_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___boxed(
    mut v_00_u03b1_6095_: *mut LeanObject,
    mut v_00_u03b2_6096_: *mut LeanObject,
    mut v_m_6097_: *mut LeanObject,
    mut v_inst_6098_: *mut LeanObject,
    mut v_f_6099_: *mut LeanObject,
    mut v_as_6100_: *mut LeanObject,
    mut v_i_6101_: *mut LeanObject,
    mut v_stop_6102_: *mut LeanObject,
    mut v_b_6103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6104_: usize = 0;
    let mut v_stop_boxed_6105_: usize = 0;
    let mut v_res_6106_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6104_ = lean_unbox_usize(v_i_6101_);
    lean_dec(v_i_6101_);
    v_stop_boxed_6105_ = lean_unbox_usize(v_stop_6102_);
    lean_dec(v_stop_6102_);
    v_res_6106_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
        v_00_u03b1_6095_,
        v_00_u03b2_6096_,
        v_m_6097_,
        v_inst_6098_,
        v_f_6099_,
        v_as_6100_,
        v_i_boxed_6104_,
        v_stop_boxed_6105_,
        v_b_6103_,
    );
    return v_res_6106_;
}
pub unsafe fn l_Array_foldrMUnsafe___redArg(
    mut v_inst_6107_: *mut LeanObject,
    mut v_f_6108_: *mut LeanObject,
    mut v_init_6109_: *mut LeanObject,
    mut v_as_6110_: *mut LeanObject,
    mut v_start_6111_: *mut LeanObject,
    mut v_stop_6112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: u8 = 0;
    v___x_6113_ = lean_array_get_size(v_as_6110_);
    v___x_6114_ = lean_nat_dec_le(v_start_6111_, v___x_6113_);
    if v___x_6114_ == 0 {
        let mut v___x_6115_: u8 = 0;
        v___x_6115_ = lean_nat_dec_lt(v_stop_6112_, v___x_6113_);
        if v___x_6115_ == 0 {
            let mut v_toApplicative_6116_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_6117_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6118_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_as_6110_);
            lean_dec(v_f_6108_);
            v_toApplicative_6116_ = lean_ctor_get(v_inst_6107_, 0);
            lean_inc_ref(v_toApplicative_6116_);
            lean_dec_ref(v_inst_6107_);
            v_toPure_6117_ = lean_ctor_get(v_toApplicative_6116_, 1);
            lean_inc(v_toPure_6117_);
            lean_dec_ref(v_toApplicative_6116_);
            v___x_6118_ = lean_apply_2(v_toPure_6117_, lean_box(0), v_init_6109_);
            return v___x_6118_;
        } else {
            let mut v___x_6119_: usize = 0;
            let mut v___x_6120_: usize = 0;
            let mut v___x_6121_: *mut LeanObject = core::ptr::null_mut();
            v___x_6119_ = lean_usize_of_nat(v___x_6113_);
            v___x_6120_ = lean_usize_of_nat(v_stop_6112_);
            v___x_6121_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
                v_inst_6107_,
                v_f_6108_,
                v_as_6110_,
                v___x_6119_,
                v___x_6120_,
                v_init_6109_,
            );
            return v___x_6121_;
        }
    } else {
        let mut v___x_6122_: u8 = 0;
        v___x_6122_ = lean_nat_dec_lt(v_stop_6112_, v_start_6111_);
        if v___x_6122_ == 0 {
            let mut v_toApplicative_6123_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_6124_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6125_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_as_6110_);
            lean_dec(v_f_6108_);
            v_toApplicative_6123_ = lean_ctor_get(v_inst_6107_, 0);
            lean_inc_ref(v_toApplicative_6123_);
            lean_dec_ref(v_inst_6107_);
            v_toPure_6124_ = lean_ctor_get(v_toApplicative_6123_, 1);
            lean_inc(v_toPure_6124_);
            lean_dec_ref(v_toApplicative_6123_);
            v___x_6125_ = lean_apply_2(v_toPure_6124_, lean_box(0), v_init_6109_);
            return v___x_6125_;
        } else {
            let mut v___x_6126_: usize = 0;
            let mut v___x_6127_: usize = 0;
            let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
            v___x_6126_ = lean_usize_of_nat(v_start_6111_);
            v___x_6127_ = lean_usize_of_nat(v_stop_6112_);
            v___x_6128_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
                v_inst_6107_,
                v_f_6108_,
                v_as_6110_,
                v___x_6126_,
                v___x_6127_,
                v_init_6109_,
            );
            return v___x_6128_;
        }
    }
}
pub unsafe fn l_Array_foldrMUnsafe___redArg___boxed(
    mut v_inst_6129_: *mut LeanObject,
    mut v_f_6130_: *mut LeanObject,
    mut v_init_6131_: *mut LeanObject,
    mut v_as_6132_: *mut LeanObject,
    mut v_start_6133_: *mut LeanObject,
    mut v_stop_6134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6135_: *mut LeanObject = core::ptr::null_mut();
    v_res_6135_ = l_Array_foldrMUnsafe___redArg(
        v_inst_6129_,
        v_f_6130_,
        v_init_6131_,
        v_as_6132_,
        v_start_6133_,
        v_stop_6134_,
    );
    lean_dec(v_stop_6134_);
    lean_dec(v_start_6133_);
    return v_res_6135_;
}
pub unsafe fn l_Array_foldrMUnsafe(
    mut v_00_u03b1_6136_: *mut LeanObject,
    mut v_00_u03b2_6137_: *mut LeanObject,
    mut v_m_6138_: *mut LeanObject,
    mut v_inst_6139_: *mut LeanObject,
    mut v_f_6140_: *mut LeanObject,
    mut v_init_6141_: *mut LeanObject,
    mut v_as_6142_: *mut LeanObject,
    mut v_start_6143_: *mut LeanObject,
    mut v_stop_6144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: u8 = 0;
    v___x_6145_ = lean_array_get_size(v_as_6142_);
    v___x_6146_ = lean_nat_dec_le(v_start_6143_, v___x_6145_);
    if v___x_6146_ == 0 {
        let mut v___x_6147_: u8 = 0;
        v___x_6147_ = lean_nat_dec_lt(v_stop_6144_, v___x_6145_);
        if v___x_6147_ == 0 {
            let mut v_toApplicative_6148_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_6149_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6150_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_as_6142_);
            lean_dec(v_f_6140_);
            v_toApplicative_6148_ = lean_ctor_get(v_inst_6139_, 0);
            lean_inc_ref(v_toApplicative_6148_);
            lean_dec_ref(v_inst_6139_);
            v_toPure_6149_ = lean_ctor_get(v_toApplicative_6148_, 1);
            lean_inc(v_toPure_6149_);
            lean_dec_ref(v_toApplicative_6148_);
            v___x_6150_ = lean_apply_2(v_toPure_6149_, lean_box(0), v_init_6141_);
            return v___x_6150_;
        } else {
            let mut v___x_6151_: usize = 0;
            let mut v___x_6152_: usize = 0;
            let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
            v___x_6151_ = lean_usize_of_nat(v___x_6145_);
            v___x_6152_ = lean_usize_of_nat(v_stop_6144_);
            v___x_6153_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
                v_inst_6139_,
                v_f_6140_,
                v_as_6142_,
                v___x_6151_,
                v___x_6152_,
                v_init_6141_,
            );
            return v___x_6153_;
        }
    } else {
        let mut v___x_6154_: u8 = 0;
        v___x_6154_ = lean_nat_dec_lt(v_stop_6144_, v_start_6143_);
        if v___x_6154_ == 0 {
            let mut v_toApplicative_6155_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_6156_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6157_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_as_6142_);
            lean_dec(v_f_6140_);
            v_toApplicative_6155_ = lean_ctor_get(v_inst_6139_, 0);
            lean_inc_ref(v_toApplicative_6155_);
            lean_dec_ref(v_inst_6139_);
            v_toPure_6156_ = lean_ctor_get(v_toApplicative_6155_, 1);
            lean_inc(v_toPure_6156_);
            lean_dec_ref(v_toApplicative_6155_);
            v___x_6157_ = lean_apply_2(v_toPure_6156_, lean_box(0), v_init_6141_);
            return v___x_6157_;
        } else {
            let mut v___x_6158_: usize = 0;
            let mut v___x_6159_: usize = 0;
            let mut v___x_6160_: *mut LeanObject = core::ptr::null_mut();
            v___x_6158_ = lean_usize_of_nat(v_start_6143_);
            v___x_6159_ = lean_usize_of_nat(v_stop_6144_);
            v___x_6160_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
                v_inst_6139_,
                v_f_6140_,
                v_as_6142_,
                v___x_6158_,
                v___x_6159_,
                v_init_6141_,
            );
            return v___x_6160_;
        }
    }
}
pub unsafe fn l_Array_foldrMUnsafe___boxed(
    mut v_00_u03b1_6161_: *mut LeanObject,
    mut v_00_u03b2_6162_: *mut LeanObject,
    mut v_m_6163_: *mut LeanObject,
    mut v_inst_6164_: *mut LeanObject,
    mut v_f_6165_: *mut LeanObject,
    mut v_init_6166_: *mut LeanObject,
    mut v_as_6167_: *mut LeanObject,
    mut v_start_6168_: *mut LeanObject,
    mut v_stop_6169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6170_: *mut LeanObject = core::ptr::null_mut();
    v_res_6170_ = l_Array_foldrMUnsafe(
        v_00_u03b1_6161_,
        v_00_u03b2_6162_,
        v_m_6163_,
        v_inst_6164_,
        v_f_6165_,
        v_init_6166_,
        v_as_6167_,
        v_start_6168_,
        v_stop_6169_,
    );
    lean_dec(v_stop_6169_);
    lean_dec(v_start_6168_);
    return v_res_6170_;
}
pub unsafe fn l_Array_foldrM_fold___redArg___lam__0___boxed(
    mut v_inst_6171_: *mut LeanObject,
    mut v_f_6172_: *mut LeanObject,
    mut v_as_6173_: *mut LeanObject,
    mut v_stop_6174_: *mut LeanObject,
    mut v_n_6175_: *mut LeanObject,
    mut v_____do__lift_6176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6177_: *mut LeanObject = core::ptr::null_mut();
    v_res_6177_ = l_Array_foldrM_fold___redArg___lam__0(
        v_inst_6171_,
        v_f_6172_,
        v_as_6173_,
        v_stop_6174_,
        v_n_6175_,
        v_____do__lift_6176_,
    );
    lean_dec(v_n_6175_);
    return v_res_6177_;
}
pub unsafe fn l_Array_foldrM_fold___redArg(
    mut v_inst_6178_: *mut LeanObject,
    mut v_f_6179_: *mut LeanObject,
    mut v_as_6180_: *mut LeanObject,
    mut v_stop_6181_: *mut LeanObject,
    mut v_i_6182_: *mut LeanObject,
    mut v_b_6183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6184_: u8 = 0;
    v___x_6184_ = lean_nat_dec_eq(v_i_6182_, v_stop_6181_);
    if v___x_6184_ == 0 {
        let mut v_zero_6185_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_6186_: u8 = 0;
        v_zero_6185_ = lean_unsigned_to_nat(0);
        v_isZero_6186_ = lean_nat_dec_eq(v_i_6182_, v_zero_6185_);
        if v_isZero_6186_ == 1 {
            let mut v_toApplicative_6187_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_6188_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6189_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_stop_6181_);
            lean_dec_ref(v_as_6180_);
            lean_dec(v_f_6179_);
            v_toApplicative_6187_ = lean_ctor_get(v_inst_6178_, 0);
            lean_inc_ref(v_toApplicative_6187_);
            lean_dec_ref(v_inst_6178_);
            v_toPure_6188_ = lean_ctor_get(v_toApplicative_6187_, 1);
            lean_inc(v_toPure_6188_);
            lean_dec_ref(v_toApplicative_6187_);
            v___x_6189_ = lean_apply_2(v_toPure_6188_, lean_box(0), v_b_6183_);
            return v___x_6189_;
        } else {
            let mut v_toBind_6190_: *mut LeanObject = core::ptr::null_mut();
            let mut v_one_6191_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_6192_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_6193_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6194_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6196_: *mut LeanObject = core::ptr::null_mut();
            v_toBind_6190_ = lean_ctor_get(v_inst_6178_, 1);
            lean_inc(v_toBind_6190_);
            v_one_6191_ = lean_unsigned_to_nat(1);
            v_n_6192_ = lean_nat_sub(v_i_6182_, v_one_6191_);
            lean_inc(v_n_6192_);
            lean_inc_ref(v_as_6180_);
            lean_inc(v_f_6179_);
            v___f_6193_ = lean_alloc_closure(
                l_Array_foldrM_fold___redArg___lam__0___boxed as *mut core::ffi::c_void,
                6,
                5,
            );
            lean_closure_set(v___f_6193_, 0, v_inst_6178_);
            lean_closure_set(v___f_6193_, 1, v_f_6179_);
            lean_closure_set(v___f_6193_, 2, v_as_6180_);
            lean_closure_set(v___f_6193_, 3, v_stop_6181_);
            lean_closure_set(v___f_6193_, 4, v_n_6192_);
            v___x_6194_ = lean_array_fget(v_as_6180_, v_n_6192_);
            lean_dec(v_n_6192_);
            lean_dec_ref(v_as_6180_);
            v___x_6195_ = lean_apply_2(v_f_6179_, v___x_6194_, v_b_6183_);
            v___x_6196_ = lean_apply_4(
                v_toBind_6190_,
                lean_box(0),
                lean_box(0),
                v___x_6195_,
                v___f_6193_,
            );
            return v___x_6196_;
        }
    } else {
        let mut v_toApplicative_6197_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_6198_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6199_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stop_6181_);
        lean_dec_ref(v_as_6180_);
        lean_dec(v_f_6179_);
        v_toApplicative_6197_ = lean_ctor_get(v_inst_6178_, 0);
        lean_inc_ref(v_toApplicative_6197_);
        lean_dec_ref(v_inst_6178_);
        v_toPure_6198_ = lean_ctor_get(v_toApplicative_6197_, 1);
        lean_inc(v_toPure_6198_);
        lean_dec_ref(v_toApplicative_6197_);
        v___x_6199_ = lean_apply_2(v_toPure_6198_, lean_box(0), v_b_6183_);
        return v___x_6199_;
    }
}
pub unsafe fn l_Array_foldrM_fold___redArg___lam__0(
    mut v_inst_6200_: *mut LeanObject,
    mut v_f_6201_: *mut LeanObject,
    mut v_as_6202_: *mut LeanObject,
    mut v_stop_6203_: *mut LeanObject,
    mut v_n_6204_: *mut LeanObject,
    mut v_____do__lift_6205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6206_: *mut LeanObject = core::ptr::null_mut();
    v___x_6206_ = l_Array_foldrM_fold___redArg(
        v_inst_6200_,
        v_f_6201_,
        v_as_6202_,
        v_stop_6203_,
        v_n_6204_,
        v_____do__lift_6205_,
    );
    return v___x_6206_;
}
pub unsafe fn l_Array_foldrM_fold___redArg___boxed(
    mut v_inst_6207_: *mut LeanObject,
    mut v_f_6208_: *mut LeanObject,
    mut v_as_6209_: *mut LeanObject,
    mut v_stop_6210_: *mut LeanObject,
    mut v_i_6211_: *mut LeanObject,
    mut v_b_6212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6213_: *mut LeanObject = core::ptr::null_mut();
    v_res_6213_ = l_Array_foldrM_fold___redArg(
        v_inst_6207_,
        v_f_6208_,
        v_as_6209_,
        v_stop_6210_,
        v_i_6211_,
        v_b_6212_,
    );
    lean_dec(v_i_6211_);
    return v_res_6213_;
}
pub unsafe fn l_Array_foldrM_fold(
    mut v_00_u03b1_6214_: *mut LeanObject,
    mut v_00_u03b2_6215_: *mut LeanObject,
    mut v_m_6216_: *mut LeanObject,
    mut v_inst_6217_: *mut LeanObject,
    mut v_f_6218_: *mut LeanObject,
    mut v_as_6219_: *mut LeanObject,
    mut v_stop_6220_: *mut LeanObject,
    mut v_i_6221_: *mut LeanObject,
    mut v_h_6222_: *mut LeanObject,
    mut v_b_6223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6224_: *mut LeanObject = core::ptr::null_mut();
    v___x_6224_ = l_Array_foldrM_fold___redArg(
        v_inst_6217_,
        v_f_6218_,
        v_as_6219_,
        v_stop_6220_,
        v_i_6221_,
        v_b_6223_,
    );
    return v___x_6224_;
}
pub unsafe fn l_Array_foldrM_fold___boxed(
    mut v_00_u03b1_6225_: *mut LeanObject,
    mut v_00_u03b2_6226_: *mut LeanObject,
    mut v_m_6227_: *mut LeanObject,
    mut v_inst_6228_: *mut LeanObject,
    mut v_f_6229_: *mut LeanObject,
    mut v_as_6230_: *mut LeanObject,
    mut v_stop_6231_: *mut LeanObject,
    mut v_i_6232_: *mut LeanObject,
    mut v_h_6233_: *mut LeanObject,
    mut v_b_6234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6235_: *mut LeanObject = core::ptr::null_mut();
    v_res_6235_ = l_Array_foldrM_fold(
        v_00_u03b1_6225_,
        v_00_u03b2_6226_,
        v_m_6227_,
        v_inst_6228_,
        v_f_6229_,
        v_as_6230_,
        v_stop_6231_,
        v_i_6232_,
        v_h_6233_,
        v_b_6234_,
    );
    lean_dec(v_i_6232_);
    return v_res_6235_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0___boxed(
    mut v_i_6236_: *mut LeanObject,
    mut v_bs_x27_6237_: *mut LeanObject,
    mut v_inst_6238_: *mut LeanObject,
    mut v_f_6239_: *mut LeanObject,
    mut v_sz_6240_: *mut LeanObject,
    mut v_vNew_6241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6242_: usize = 0;
    let mut v_sz_boxed_6243_: usize = 0;
    let mut v_res_6244_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6242_ = lean_unbox_usize(v_i_6236_);
    lean_dec(v_i_6236_);
    v_sz_boxed_6243_ = lean_unbox_usize(v_sz_6240_);
    lean_dec(v_sz_6240_);
    v_res_6244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0(
        v_i_boxed_6242_,
        v_bs_x27_6237_,
        v_inst_6238_,
        v_f_6239_,
        v_sz_boxed_6243_,
        v_vNew_6241_,
    );
    return v_res_6244_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(
    mut v_inst_6245_: *mut LeanObject,
    mut v_f_6246_: *mut LeanObject,
    mut v_sz_6247_: usize,
    mut v_i_6248_: usize,
    mut v_bs_6249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6250_: u8 = 0;
    v___x_6250_ = lean_usize_dec_lt(v_i_6248_, v_sz_6247_);
    if v___x_6250_ == 0 {
        let mut v_toApplicative_6251_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_6252_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6253_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_6246_);
        v_toApplicative_6251_ = lean_ctor_get(v_inst_6245_, 0);
        lean_inc_ref(v_toApplicative_6251_);
        lean_dec_ref(v_inst_6245_);
        v_toPure_6252_ = lean_ctor_get(v_toApplicative_6251_, 1);
        lean_inc(v_toPure_6252_);
        lean_dec_ref(v_toApplicative_6251_);
        v___x_6253_ = lean_apply_2(v_toPure_6252_, lean_box(0), v_bs_6249_);
        return v___x_6253_;
    } else {
        let mut v_toBind_6254_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_6255_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6256_: *mut LeanObject = core::ptr::null_mut();
        let mut v_bs_x27_6257_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6258_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6259_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_6260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6262_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_6254_ = lean_ctor_get(v_inst_6245_, 1);
        lean_inc(v_toBind_6254_);
        v_v_6255_ = lean_array_uget(v_bs_6249_, v_i_6248_);
        v___x_6256_ = lean_unsigned_to_nat(0);
        v_bs_x27_6257_ = lean_array_uset(v_bs_6249_, v_i_6248_, v___x_6256_);
        v___x_6258_ = lean_box_usize(v_i_6248_);
        v___x_6259_ = lean_box_usize(v_sz_6247_);
        lean_inc(v_f_6246_);
        v___f_6260_ = lean_alloc_closure(
            l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_6260_, 0, v___x_6258_);
        lean_closure_set(v___f_6260_, 1, v_bs_x27_6257_);
        lean_closure_set(v___f_6260_, 2, v_inst_6245_);
        lean_closure_set(v___f_6260_, 3, v_f_6246_);
        lean_closure_set(v___f_6260_, 4, v___x_6259_);
        v___x_6261_ = lean_apply_1(v_f_6246_, v_v_6255_);
        v___x_6262_ = lean_apply_4(
            v_toBind_6254_,
            lean_box(0),
            lean_box(0),
            v___x_6261_,
            v___f_6260_,
        );
        return v___x_6262_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0(
    mut v_i_6263_: usize,
    mut v_bs_x27_6264_: *mut LeanObject,
    mut v_inst_6265_: *mut LeanObject,
    mut v_f_6266_: *mut LeanObject,
    mut v_sz_6267_: usize,
    mut v_vNew_6268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6269_: usize = 0;
    let mut v___x_6270_: usize = 0;
    let mut v___x_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut LeanObject = core::ptr::null_mut();
    v___x_6269_ = 1usize;
    v___x_6270_ = lean_usize_add(v_i_6263_, v___x_6269_);
    v___x_6271_ = lean_array_uset(v_bs_x27_6264_, v_i_6263_, v_vNew_6268_);
    v___x_6272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(
        v_inst_6265_,
        v_f_6266_,
        v_sz_6267_,
        v___x_6270_,
        v___x_6271_,
    );
    return v___x_6272_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___boxed(
    mut v_inst_6273_: *mut LeanObject,
    mut v_f_6274_: *mut LeanObject,
    mut v_sz_6275_: *mut LeanObject,
    mut v_i_6276_: *mut LeanObject,
    mut v_bs_6277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6278_: usize = 0;
    let mut v_i_boxed_6279_: usize = 0;
    let mut v_res_6280_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6278_ = lean_unbox_usize(v_sz_6275_);
    lean_dec(v_sz_6275_);
    v_i_boxed_6279_ = lean_unbox_usize(v_i_6276_);
    lean_dec(v_i_6276_);
    v_res_6280_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(
        v_inst_6273_,
        v_f_6274_,
        v_sz_boxed_6278_,
        v_i_boxed_6279_,
        v_bs_6277_,
    );
    return v_res_6280_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
    mut v_00_u03b1_6281_: *mut LeanObject,
    mut v_00_u03b2_6282_: *mut LeanObject,
    mut v_m_6283_: *mut LeanObject,
    mut v_inst_6284_: *mut LeanObject,
    mut v_f_6285_: *mut LeanObject,
    mut v_sz_6286_: usize,
    mut v_i_6287_: usize,
    mut v_bs_6288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6289_: *mut LeanObject = core::ptr::null_mut();
    v___x_6289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(
        v_inst_6284_,
        v_f_6285_,
        v_sz_6286_,
        v_i_6287_,
        v_bs_6288_,
    );
    return v___x_6289_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___boxed(
    mut v_00_u03b1_6290_: *mut LeanObject,
    mut v_00_u03b2_6291_: *mut LeanObject,
    mut v_m_6292_: *mut LeanObject,
    mut v_inst_6293_: *mut LeanObject,
    mut v_f_6294_: *mut LeanObject,
    mut v_sz_6295_: *mut LeanObject,
    mut v_i_6296_: *mut LeanObject,
    mut v_bs_6297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6298_: usize = 0;
    let mut v_i_boxed_6299_: usize = 0;
    let mut v_res_6300_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6298_ = lean_unbox_usize(v_sz_6295_);
    lean_dec(v_sz_6295_);
    v_i_boxed_6299_ = lean_unbox_usize(v_i_6296_);
    lean_dec(v_i_6296_);
    v_res_6300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        v_00_u03b1_6290_,
        v_00_u03b2_6291_,
        v_m_6292_,
        v_inst_6293_,
        v_f_6294_,
        v_sz_boxed_6298_,
        v_i_boxed_6299_,
        v_bs_6297_,
    );
    return v_res_6300_;
}
pub unsafe fn l_Array_mapMUnsafe___redArg(
    mut v_inst_6301_: *mut LeanObject,
    mut v_f_6302_: *mut LeanObject,
    mut v_as_6303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_6304_: usize = 0;
    let mut v___x_6305_: usize = 0;
    let mut v___x_6306_: *mut LeanObject = core::ptr::null_mut();
    v_sz_6304_ = lean_array_size(v_as_6303_);
    v___x_6305_ = 0usize;
    v___x_6306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(
        v_inst_6301_,
        v_f_6302_,
        v_sz_6304_,
        v___x_6305_,
        v_as_6303_,
    );
    return v___x_6306_;
}
pub unsafe fn l_Array_mapMUnsafe(
    mut v_00_u03b1_6307_: *mut LeanObject,
    mut v_00_u03b2_6308_: *mut LeanObject,
    mut v_m_6309_: *mut LeanObject,
    mut v_inst_6310_: *mut LeanObject,
    mut v_f_6311_: *mut LeanObject,
    mut v_as_6312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_6313_: usize = 0;
    let mut v___x_6314_: usize = 0;
    let mut v___x_6315_: *mut LeanObject = core::ptr::null_mut();
    v_sz_6313_ = lean_array_size(v_as_6312_);
    v___x_6314_ = 0usize;
    v___x_6315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(
        v_inst_6310_,
        v_f_6311_,
        v_sz_6313_,
        v___x_6314_,
        v_as_6312_,
    );
    return v___x_6315_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0___boxed(
    mut v_i_6316_: *mut LeanObject,
    mut v_bs_6317_: *mut LeanObject,
    mut v_inst_6318_: *mut LeanObject,
    mut v_f_6319_: *mut LeanObject,
    mut v_as_6320_: *mut LeanObject,
    mut v_____do__lift_6321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6322_: *mut LeanObject = core::ptr::null_mut();
    v_res_6322_ = l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0(
        v_i_6316_,
        v_bs_6317_,
        v_inst_6318_,
        v_f_6319_,
        v_as_6320_,
        v_____do__lift_6321_,
    );
    lean_dec(v_i_6316_);
    return v_res_6322_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(
    mut v_inst_6323_: *mut LeanObject,
    mut v_f_6324_: *mut LeanObject,
    mut v_as_6325_: *mut LeanObject,
    mut v_i_6326_: *mut LeanObject,
    mut v_bs_6327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: u8 = 0;
    v___x_6328_ = lean_array_get_size(v_as_6325_);
    v___x_6329_ = lean_nat_dec_lt(v_i_6326_, v___x_6328_);
    if v___x_6329_ == 0 {
        let mut v_toApplicative_6330_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_6331_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6332_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_i_6326_);
        lean_dec_ref(v_as_6325_);
        lean_dec(v_f_6324_);
        v_toApplicative_6330_ = lean_ctor_get(v_inst_6323_, 0);
        lean_inc_ref(v_toApplicative_6330_);
        lean_dec_ref(v_inst_6323_);
        v_toPure_6331_ = lean_ctor_get(v_toApplicative_6330_, 1);
        lean_inc(v_toPure_6331_);
        lean_dec_ref(v_toApplicative_6330_);
        v___x_6332_ = lean_apply_2(v_toPure_6331_, lean_box(0), v_bs_6327_);
        return v___x_6332_;
    } else {
        let mut v_toBind_6333_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_6334_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6336_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6337_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_6333_ = lean_ctor_get(v_inst_6323_, 1);
        lean_inc(v_toBind_6333_);
        lean_inc_ref(v_as_6325_);
        lean_inc(v_f_6324_);
        lean_inc(v_i_6326_);
        v___f_6334_ = lean_alloc_closure(
            l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_6334_, 0, v_i_6326_);
        lean_closure_set(v___f_6334_, 1, v_bs_6327_);
        lean_closure_set(v___f_6334_, 2, v_inst_6323_);
        lean_closure_set(v___f_6334_, 3, v_f_6324_);
        lean_closure_set(v___f_6334_, 4, v_as_6325_);
        v___x_6335_ = lean_array_fget(v_as_6325_, v_i_6326_);
        lean_dec(v_i_6326_);
        lean_dec_ref(v_as_6325_);
        v___x_6336_ = lean_apply_1(v_f_6324_, v___x_6335_);
        v___x_6337_ = lean_apply_4(
            v_toBind_6333_,
            lean_box(0),
            lean_box(0),
            v___x_6336_,
            v___f_6334_,
        );
        return v___x_6337_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0(
    mut v_i_6338_: *mut LeanObject,
    mut v_bs_6339_: *mut LeanObject,
    mut v_inst_6340_: *mut LeanObject,
    mut v_f_6341_: *mut LeanObject,
    mut v_as_6342_: *mut LeanObject,
    mut v_____do__lift_6343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: *mut LeanObject = core::ptr::null_mut();
    v___x_6344_ = lean_unsigned_to_nat(1);
    v___x_6345_ = lean_nat_add(v_i_6338_, v___x_6344_);
    v___x_6346_ = lean_array_push(v_bs_6339_, v_____do__lift_6343_);
    v___x_6347_ = l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(
        v_inst_6340_,
        v_f_6341_,
        v_as_6342_,
        v___x_6345_,
        v___x_6346_,
    );
    return v___x_6347_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapM_map(
    mut v_00_u03b1_6348_: *mut LeanObject,
    mut v_00_u03b2_6349_: *mut LeanObject,
    mut v_m_6350_: *mut LeanObject,
    mut v_inst_6351_: *mut LeanObject,
    mut v_f_6352_: *mut LeanObject,
    mut v_as_6353_: *mut LeanObject,
    mut v_i_6354_: *mut LeanObject,
    mut v_bs_6355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6356_: *mut LeanObject = core::ptr::null_mut();
    v___x_6356_ = l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(
        v_inst_6351_,
        v_f_6352_,
        v_as_6353_,
        v_i_6354_,
        v_bs_6355_,
    );
    return v___x_6356_;
}
pub unsafe fn l_Array_mapFinIdxM_map___redArg___lam__0___boxed(
    mut v_j_6357_: *mut LeanObject,
    mut v_bs_6358_: *mut LeanObject,
    mut v_inst_6359_: *mut LeanObject,
    mut v_as_6360_: *mut LeanObject,
    mut v_f_6361_: *mut LeanObject,
    mut v_n_6362_: *mut LeanObject,
    mut v_____do__lift_6363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6364_: *mut LeanObject = core::ptr::null_mut();
    v_res_6364_ = l_Array_mapFinIdxM_map___redArg___lam__0(
        v_j_6357_,
        v_bs_6358_,
        v_inst_6359_,
        v_as_6360_,
        v_f_6361_,
        v_n_6362_,
        v_____do__lift_6363_,
    );
    lean_dec(v_n_6362_);
    lean_dec(v_j_6357_);
    return v_res_6364_;
}
pub unsafe fn l_Array_mapFinIdxM_map___redArg(
    mut v_inst_6365_: *mut LeanObject,
    mut v_as_6366_: *mut LeanObject,
    mut v_f_6367_: *mut LeanObject,
    mut v_i_6368_: *mut LeanObject,
    mut v_j_6369_: *mut LeanObject,
    mut v_bs_6370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_6374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6375_: u8 = 0;
    v_toApplicative_6371_ = lean_ctor_get(v_inst_6365_, 0);
    v_toBind_6372_ = lean_ctor_get(v_inst_6365_, 1);
    lean_inc(v_toBind_6372_);
    v_toPure_6373_ = lean_ctor_get(v_toApplicative_6371_, 1);
    v_zero_6374_ = lean_unsigned_to_nat(0);
    v_isZero_6375_ = lean_nat_dec_eq(v_i_6368_, v_zero_6374_);
    if v_isZero_6375_ == 1 {
        let mut v___x_6376_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_toPure_6373_);
        lean_dec(v_toBind_6372_);
        lean_dec(v_j_6369_);
        lean_dec(v_f_6367_);
        lean_dec_ref(v_as_6366_);
        lean_dec_ref(v_inst_6365_);
        v___x_6376_ = lean_apply_2(v_toPure_6373_, lean_box(0), v_bs_6370_);
        return v___x_6376_;
    } else {
        let mut v_one_6377_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_6378_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_6379_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6380_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6381_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6382_: *mut LeanObject = core::ptr::null_mut();
        v_one_6377_ = lean_unsigned_to_nat(1);
        v_n_6378_ = lean_nat_sub(v_i_6368_, v_one_6377_);
        lean_inc(v_f_6367_);
        lean_inc_ref(v_as_6366_);
        lean_inc(v_j_6369_);
        v___f_6379_ = lean_alloc_closure(
            l_Array_mapFinIdxM_map___redArg___lam__0___boxed as *mut core::ffi::c_void,
            7,
            6,
        );
        lean_closure_set(v___f_6379_, 0, v_j_6369_);
        lean_closure_set(v___f_6379_, 1, v_bs_6370_);
        lean_closure_set(v___f_6379_, 2, v_inst_6365_);
        lean_closure_set(v___f_6379_, 3, v_as_6366_);
        lean_closure_set(v___f_6379_, 4, v_f_6367_);
        lean_closure_set(v___f_6379_, 5, v_n_6378_);
        v___x_6380_ = lean_array_fget(v_as_6366_, v_j_6369_);
        lean_dec_ref(v_as_6366_);
        v___x_6381_ = lean_apply_3(v_f_6367_, v_j_6369_, v___x_6380_, lean_box(0));
        v___x_6382_ = lean_apply_4(
            v_toBind_6372_,
            lean_box(0),
            lean_box(0),
            v___x_6381_,
            v___f_6379_,
        );
        return v___x_6382_;
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___redArg___lam__0(
    mut v_j_6383_: *mut LeanObject,
    mut v_bs_6384_: *mut LeanObject,
    mut v_inst_6385_: *mut LeanObject,
    mut v_as_6386_: *mut LeanObject,
    mut v_f_6387_: *mut LeanObject,
    mut v_n_6388_: *mut LeanObject,
    mut v_____do__lift_6389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6393_: *mut LeanObject = core::ptr::null_mut();
    v___x_6390_ = lean_unsigned_to_nat(1);
    v___x_6391_ = lean_nat_add(v_j_6383_, v___x_6390_);
    v___x_6392_ = lean_array_push(v_bs_6384_, v_____do__lift_6389_);
    v___x_6393_ = l_Array_mapFinIdxM_map___redArg(
        v_inst_6385_,
        v_as_6386_,
        v_f_6387_,
        v_n_6388_,
        v___x_6391_,
        v___x_6392_,
    );
    return v___x_6393_;
}
pub unsafe fn l_Array_mapFinIdxM_map___redArg___boxed(
    mut v_inst_6394_: *mut LeanObject,
    mut v_as_6395_: *mut LeanObject,
    mut v_f_6396_: *mut LeanObject,
    mut v_i_6397_: *mut LeanObject,
    mut v_j_6398_: *mut LeanObject,
    mut v_bs_6399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6400_: *mut LeanObject = core::ptr::null_mut();
    v_res_6400_ = l_Array_mapFinIdxM_map___redArg(
        v_inst_6394_,
        v_as_6395_,
        v_f_6396_,
        v_i_6397_,
        v_j_6398_,
        v_bs_6399_,
    );
    lean_dec(v_i_6397_);
    return v_res_6400_;
}
pub unsafe fn l_Array_mapFinIdxM_map(
    mut v_00_u03b1_6401_: *mut LeanObject,
    mut v_00_u03b2_6402_: *mut LeanObject,
    mut v_m_6403_: *mut LeanObject,
    mut v_inst_6404_: *mut LeanObject,
    mut v_as_6405_: *mut LeanObject,
    mut v_f_6406_: *mut LeanObject,
    mut v_i_6407_: *mut LeanObject,
    mut v_j_6408_: *mut LeanObject,
    mut v_inv_6409_: *mut LeanObject,
    mut v_bs_6410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6411_: *mut LeanObject = core::ptr::null_mut();
    v___x_6411_ = l_Array_mapFinIdxM_map___redArg(
        v_inst_6404_,
        v_as_6405_,
        v_f_6406_,
        v_i_6407_,
        v_j_6408_,
        v_bs_6410_,
    );
    return v___x_6411_;
}
pub unsafe fn l_Array_mapFinIdxM_map___boxed(
    mut v_00_u03b1_6412_: *mut LeanObject,
    mut v_00_u03b2_6413_: *mut LeanObject,
    mut v_m_6414_: *mut LeanObject,
    mut v_inst_6415_: *mut LeanObject,
    mut v_as_6416_: *mut LeanObject,
    mut v_f_6417_: *mut LeanObject,
    mut v_i_6418_: *mut LeanObject,
    mut v_j_6419_: *mut LeanObject,
    mut v_inv_6420_: *mut LeanObject,
    mut v_bs_6421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6422_: *mut LeanObject = core::ptr::null_mut();
    v_res_6422_ = l_Array_mapFinIdxM_map(
        v_00_u03b1_6412_,
        v_00_u03b2_6413_,
        v_m_6414_,
        v_inst_6415_,
        v_as_6416_,
        v_f_6417_,
        v_i_6418_,
        v_j_6419_,
        v_inv_6420_,
        v_bs_6421_,
    );
    lean_dec(v_i_6418_);
    return v_res_6422_;
}
pub unsafe fn l_Array_mapFinIdxM___redArg(
    mut v_inst_6423_: *mut LeanObject,
    mut v_as_6424_: *mut LeanObject,
    mut v_f_6425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut LeanObject = core::ptr::null_mut();
    v___x_6426_ = lean_array_get_size(v_as_6424_);
    v___x_6427_ = lean_unsigned_to_nat(0);
    v___x_6428_ = lean_mk_empty_array_with_capacity(v___x_6426_);
    v___x_6429_ = l_Array_mapFinIdxM_map___redArg(
        v_inst_6423_,
        v_as_6424_,
        v_f_6425_,
        v___x_6426_,
        v___x_6427_,
        v___x_6428_,
    );
    return v___x_6429_;
}
pub unsafe fn l_Array_mapFinIdxM(
    mut v_00_u03b1_6430_: *mut LeanObject,
    mut v_00_u03b2_6431_: *mut LeanObject,
    mut v_m_6432_: *mut LeanObject,
    mut v_inst_6433_: *mut LeanObject,
    mut v_as_6434_: *mut LeanObject,
    mut v_f_6435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    v___x_6436_ = lean_array_get_size(v_as_6434_);
    v___x_6437_ = lean_unsigned_to_nat(0);
    v___x_6438_ = lean_mk_empty_array_with_capacity(v___x_6436_);
    v___x_6439_ = l_Array_mapFinIdxM_map___redArg(
        v_inst_6433_,
        v_as_6434_,
        v_f_6435_,
        v___x_6436_,
        v___x_6437_,
        v___x_6438_,
    );
    return v___x_6439_;
}
pub unsafe fn l_Array_mapIdxM___redArg___lam__0(
    mut v_f_6440_: *mut LeanObject,
    mut v_i_6441_: *mut LeanObject,
    mut v_a_6442_: *mut LeanObject,
    mut v_x_6443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6444_: *mut LeanObject = core::ptr::null_mut();
    v___x_6444_ = lean_apply_2(v_f_6440_, v_i_6441_, v_a_6442_);
    return v___x_6444_;
}
pub unsafe fn l_Array_mapIdxM___redArg(
    mut v_inst_6445_: *mut LeanObject,
    mut v_f_6446_: *mut LeanObject,
    mut v_as_6447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: *mut LeanObject = core::ptr::null_mut();
    v___f_6448_ = lean_alloc_closure(
        l_Array_mapIdxM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_6448_, 0, v_f_6446_);
    v___x_6449_ = lean_array_get_size(v_as_6447_);
    v___x_6450_ = lean_unsigned_to_nat(0);
    v___x_6451_ = lean_mk_empty_array_with_capacity(v___x_6449_);
    v___x_6452_ = l_Array_mapFinIdxM_map___redArg(
        v_inst_6445_,
        v_as_6447_,
        v___f_6448_,
        v___x_6449_,
        v___x_6450_,
        v___x_6451_,
    );
    return v___x_6452_;
}
pub unsafe fn l_Array_mapIdxM(
    mut v_00_u03b1_6453_: *mut LeanObject,
    mut v_00_u03b2_6454_: *mut LeanObject,
    mut v_m_6455_: *mut LeanObject,
    mut v_inst_6456_: *mut LeanObject,
    mut v_f_6457_: *mut LeanObject,
    mut v_as_6458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut LeanObject = core::ptr::null_mut();
    v___f_6459_ = lean_alloc_closure(
        l_Array_mapIdxM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_6459_, 0, v_f_6457_);
    v___x_6460_ = lean_array_get_size(v_as_6458_);
    v___x_6461_ = lean_unsigned_to_nat(0);
    v___x_6462_ = lean_mk_empty_array_with_capacity(v___x_6460_);
    v___x_6463_ = l_Array_mapFinIdxM_map___redArg(
        v_inst_6456_,
        v_as_6458_,
        v___f_6459_,
        v___x_6460_,
        v___x_6461_,
        v___x_6462_,
    );
    return v___x_6463_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed(
    mut v_i_6464_: *mut LeanObject,
    mut v_inst_6465_: *mut LeanObject,
    mut v_f_6466_: *mut LeanObject,
    mut v_as_6467_: *mut LeanObject,
    mut v_x_6468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6469_: *mut LeanObject = core::ptr::null_mut();
    v_res_6469_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(
        v_i_6464_,
        v_inst_6465_,
        v_f_6466_,
        v_as_6467_,
        v_x_6468_,
    );
    lean_dec(v_i_6464_);
    return v_res_6469_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(
    mut v_inst_6470_: *mut LeanObject,
    mut v_f_6471_: *mut LeanObject,
    mut v_as_6472_: *mut LeanObject,
    mut v_i_6473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: u8 = 0;
    v___x_6474_ = lean_array_get_size(v_as_6472_);
    v___x_6475_ = lean_nat_dec_lt(v_i_6473_, v___x_6474_);
    if v___x_6475_ == 0 {
        let mut v_failure_6476_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6477_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_i_6473_);
        lean_dec_ref(v_as_6472_);
        lean_dec(v_f_6471_);
        v_failure_6476_ = lean_ctor_get(v_inst_6470_, 1);
        lean_inc(v_failure_6476_);
        lean_dec_ref(v_inst_6470_);
        v___x_6477_ = lean_apply_1(v_failure_6476_, lean_box(0));
        return v___x_6477_;
    } else {
        let mut v_orElse_6478_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_6479_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6480_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6481_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6482_: *mut LeanObject = core::ptr::null_mut();
        v_orElse_6478_ = lean_ctor_get(v_inst_6470_, 2);
        lean_inc(v_orElse_6478_);
        lean_inc_ref(v_as_6472_);
        lean_inc(v_f_6471_);
        lean_inc(v_i_6473_);
        v___f_6479_ = lean_alloc_closure(
            l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_6479_, 0, v_i_6473_);
        lean_closure_set(v___f_6479_, 1, v_inst_6470_);
        lean_closure_set(v___f_6479_, 2, v_f_6471_);
        lean_closure_set(v___f_6479_, 3, v_as_6472_);
        v___x_6480_ = lean_array_fget(v_as_6472_, v_i_6473_);
        lean_dec(v_i_6473_);
        lean_dec_ref(v_as_6472_);
        v___x_6481_ = lean_apply_1(v_f_6471_, v___x_6480_);
        v___x_6482_ = lean_apply_3(v_orElse_6478_, lean_box(0), v___x_6481_, v___f_6479_);
        return v___x_6482_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(
    mut v_i_6483_: *mut LeanObject,
    mut v_inst_6484_: *mut LeanObject,
    mut v_f_6485_: *mut LeanObject,
    mut v_as_6486_: *mut LeanObject,
    mut v_x_6487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut LeanObject = core::ptr::null_mut();
    v___x_6488_ = lean_unsigned_to_nat(1);
    v___x_6489_ = lean_nat_add(v_i_6483_, v___x_6488_);
    v___x_6490_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(
        v_inst_6484_,
        v_f_6485_,
        v_as_6486_,
        v___x_6489_,
    );
    return v___x_6490_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_firstM_go(
    mut v_00_u03b2_6491_: *mut LeanObject,
    mut v_00_u03b1_6492_: *mut LeanObject,
    mut v_m_6493_: *mut LeanObject,
    mut v_inst_6494_: *mut LeanObject,
    mut v_f_6495_: *mut LeanObject,
    mut v_as_6496_: *mut LeanObject,
    mut v_i_6497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6498_: *mut LeanObject = core::ptr::null_mut();
    v___x_6498_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(
        v_inst_6494_,
        v_f_6495_,
        v_as_6496_,
        v_i_6497_,
    );
    return v___x_6498_;
}
pub unsafe fn l_Array_firstM___redArg(
    mut v_inst_6499_: *mut LeanObject,
    mut v_f_6500_: *mut LeanObject,
    mut v_as_6501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut LeanObject = core::ptr::null_mut();
    v___x_6502_ = lean_unsigned_to_nat(0);
    v___x_6503_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(
        v_inst_6499_,
        v_f_6500_,
        v_as_6501_,
        v___x_6502_,
    );
    return v___x_6503_;
}
pub unsafe fn l_Array_firstM(
    mut v_00_u03b2_6504_: *mut LeanObject,
    mut v_00_u03b1_6505_: *mut LeanObject,
    mut v_m_6506_: *mut LeanObject,
    mut v_inst_6507_: *mut LeanObject,
    mut v_f_6508_: *mut LeanObject,
    mut v_as_6509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut LeanObject = core::ptr::null_mut();
    v___x_6510_ = lean_unsigned_to_nat(0);
    v___x_6511_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(
        v_inst_6507_,
        v_f_6508_,
        v_as_6509_,
        v___x_6510_,
    );
    return v___x_6511_;
}
pub unsafe fn l_Array_findSomeM_x3f___redArg___lam__0(
    mut v___x_6512_: *mut LeanObject,
    mut v_toPure_6513_: *mut LeanObject,
    mut v___x_6514_: *mut LeanObject,
    mut v_____do__lift_6515_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_6515_) == 1 {
        let mut v___x_6516_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6517_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6518_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6519_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_6514_);
        v___x_6516_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_6516_, 0, v_____do__lift_6515_);
        v___x_6517_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_6517_, 0, v___x_6516_);
        lean_ctor_set(v___x_6517_, 1, v___x_6512_);
        v___x_6518_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6518_, 0, v___x_6517_);
        v___x_6519_ = lean_apply_2(v_toPure_6513_, lean_box(0), v___x_6518_);
        return v___x_6519_;
    } else {
        let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6521_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_____do__lift_6515_);
        v___x_6520_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_6520_, 0, v___x_6514_);
        v___x_6521_ = lean_apply_2(v_toPure_6513_, lean_box(0), v___x_6520_);
        return v___x_6521_;
    }
}
pub unsafe fn l_Array_findSomeM_x3f___redArg___lam__1(
    mut v_f_6522_: *mut LeanObject,
    mut v_toBind_6523_: *mut LeanObject,
    mut v___f_6524_: *mut LeanObject,
    mut v_a_6525_: *mut LeanObject,
    mut v_x_6526_: *mut LeanObject,
    mut v___y_6527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut LeanObject = core::ptr::null_mut();
    v___x_6528_ = lean_apply_1(v_f_6522_, v_a_6525_);
    v___x_6529_ = lean_apply_4(
        v_toBind_6523_,
        lean_box(0),
        lean_box(0),
        v___x_6528_,
        v___f_6524_,
    );
    return v___x_6529_;
}
pub unsafe fn l_Array_findSomeM_x3f___redArg___lam__1___boxed(
    mut v_f_6530_: *mut LeanObject,
    mut v_toBind_6531_: *mut LeanObject,
    mut v___f_6532_: *mut LeanObject,
    mut v_a_6533_: *mut LeanObject,
    mut v_x_6534_: *mut LeanObject,
    mut v___y_6535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6536_: *mut LeanObject = core::ptr::null_mut();
    v_res_6536_ = l_Array_findSomeM_x3f___redArg___lam__1(
        v_f_6530_,
        v_toBind_6531_,
        v___f_6532_,
        v_a_6533_,
        v_x_6534_,
        v___y_6535_,
    );
    lean_dec_ref(v___y_6535_);
    return v_res_6536_;
}
pub unsafe fn l_Array_findSomeM_x3f___redArg___lam__2(
    mut v_toPure_6537_: *mut LeanObject,
    mut v_____s_6538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_6539_: *mut LeanObject = core::ptr::null_mut();
    v_fst_6539_ = lean_ctor_get(v_____s_6538_, 0);
    lean_inc(v_fst_6539_);
    lean_dec_ref(v_____s_6538_);
    if lean_obj_tag(v_fst_6539_) == 0 {
        let mut v___x_6540_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6541_: *mut LeanObject = core::ptr::null_mut();
        v___x_6540_ = lean_box(0);
        v___x_6541_ = lean_apply_2(v_toPure_6537_, lean_box(0), v___x_6540_);
        return v___x_6541_;
    } else {
        let mut v_val_6542_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6543_: *mut LeanObject = core::ptr::null_mut();
        v_val_6542_ = lean_ctor_get(v_fst_6539_, 0);
        lean_inc(v_val_6542_);
        lean_dec_ref_known(v_fst_6539_, 1);
        v___x_6543_ = lean_apply_2(v_toPure_6537_, lean_box(0), v_val_6542_);
        return v___x_6543_;
    }
}
pub unsafe fn l_Array_findSomeM_x3f___redArg(
    mut v_inst_6547_: *mut LeanObject,
    mut v_f_6548_: *mut LeanObject,
    mut v_as_6549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6558_: usize = 0;
    let mut v___x_6559_: usize = 0;
    let mut v___x_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6550_ = lean_ctor_get(v_inst_6547_, 0);
    v_toBind_6551_ = lean_ctor_get(v_inst_6547_, 1);
    lean_inc_n(v_toBind_6551_, 2);
    v_toPure_6552_ = lean_ctor_get(v_toApplicative_6550_, 1);
    v___x_6553_ = lean_box(0);
    v___x_6554_ = l_Array_findSomeM_x3f___redArg___closed__0;
    lean_inc_n(v_toPure_6552_, 2);
    v___f_6555_ = lean_alloc_closure(
        l_Array_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6555_, 0, v___x_6553_);
    lean_closure_set(v___f_6555_, 1, v_toPure_6552_);
    lean_closure_set(v___f_6555_, 2, v___x_6554_);
    v___f_6556_ = lean_alloc_closure(
        l_Array_findSomeM_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_6556_, 0, v_f_6548_);
    lean_closure_set(v___f_6556_, 1, v_toBind_6551_);
    lean_closure_set(v___f_6556_, 2, v___f_6555_);
    v___f_6557_ = lean_alloc_closure(
        l_Array_findSomeM_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6557_, 0, v_toPure_6552_);
    v_sz_6558_ = lean_array_size(v_as_6549_);
    v___x_6559_ = 0usize;
    v___x_6560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
        v_inst_6547_,
        v_as_6549_,
        v___f_6556_,
        v_sz_6558_,
        v___x_6559_,
        v___x_6554_,
    );
    v___x_6561_ = lean_apply_4(
        v_toBind_6551_,
        lean_box(0),
        lean_box(0),
        v___x_6560_,
        v___f_6557_,
    );
    return v___x_6561_;
}
pub unsafe fn l_Array_findSomeM_x3f(
    mut v_00_u03b1_6562_: *mut LeanObject,
    mut v_00_u03b2_6563_: *mut LeanObject,
    mut v_m_6564_: *mut LeanObject,
    mut v_inst_6565_: *mut LeanObject,
    mut v_f_6566_: *mut LeanObject,
    mut v_as_6567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6576_: usize = 0;
    let mut v___x_6577_: usize = 0;
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6568_ = lean_ctor_get(v_inst_6565_, 0);
    v_toBind_6569_ = lean_ctor_get(v_inst_6565_, 1);
    lean_inc_n(v_toBind_6569_, 2);
    v_toPure_6570_ = lean_ctor_get(v_toApplicative_6568_, 1);
    v___x_6571_ = lean_box(0);
    v___x_6572_ = l_Array_findSomeM_x3f___redArg___closed__0;
    lean_inc_n(v_toPure_6570_, 2);
    v___f_6573_ = lean_alloc_closure(
        l_Array_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6573_, 0, v___x_6571_);
    lean_closure_set(v___f_6573_, 1, v_toPure_6570_);
    lean_closure_set(v___f_6573_, 2, v___x_6572_);
    v___f_6574_ = lean_alloc_closure(
        l_Array_findSomeM_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_6574_, 0, v_f_6566_);
    lean_closure_set(v___f_6574_, 1, v_toBind_6569_);
    lean_closure_set(v___f_6574_, 2, v___f_6573_);
    v___f_6575_ = lean_alloc_closure(
        l_Array_findSomeM_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6575_, 0, v_toPure_6570_);
    v_sz_6576_ = lean_array_size(v_as_6567_);
    v___x_6577_ = 0usize;
    v___x_6578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
        v_inst_6565_,
        v_as_6567_,
        v___f_6574_,
        v_sz_6576_,
        v___x_6577_,
        v___x_6572_,
    );
    v___x_6579_ = lean_apply_4(
        v_toBind_6569_,
        lean_box(0),
        lean_box(0),
        v___x_6578_,
        v___f_6575_,
    );
    return v___x_6579_;
}
pub unsafe fn l_Array_findM_x3f___redArg___lam__0(
    mut v___x_6580_: *mut LeanObject,
    mut v_toPure_6581_: *mut LeanObject,
    mut v_a_6582_: *mut LeanObject,
    mut v___x_6583_: *mut LeanObject,
    mut v_____do__lift_6584_: u8,
) -> *mut LeanObject {
    if v_____do__lift_6584_ == 0 {
        let mut v___x_6585_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6586_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_6582_);
        v___x_6585_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_6585_, 0, v___x_6580_);
        v___x_6586_ = lean_apply_2(v_toPure_6581_, lean_box(0), v___x_6585_);
        return v___x_6586_;
    } else {
        let mut v___x_6587_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6588_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6589_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6590_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6591_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_6580_);
        v___x_6587_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_6587_, 0, v_a_6582_);
        v___x_6588_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_6588_, 0, v___x_6587_);
        v___x_6589_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_6589_, 0, v___x_6588_);
        lean_ctor_set(v___x_6589_, 1, v___x_6583_);
        v___x_6590_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6590_, 0, v___x_6589_);
        v___x_6591_ = lean_apply_2(v_toPure_6581_, lean_box(0), v___x_6590_);
        return v___x_6591_;
    }
}
pub unsafe fn l_Array_findM_x3f___redArg___lam__0___boxed(
    mut v___x_6592_: *mut LeanObject,
    mut v_toPure_6593_: *mut LeanObject,
    mut v_a_6594_: *mut LeanObject,
    mut v___x_6595_: *mut LeanObject,
    mut v_____do__lift_6596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_214__boxed_6597_: u8 = 0;
    let mut v_res_6598_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_214__boxed_6597_ = (lean_unbox(v_____do__lift_6596_) as u8);
    v_res_6598_ = l_Array_findM_x3f___redArg___lam__0(
        v___x_6592_,
        v_toPure_6593_,
        v_a_6594_,
        v___x_6595_,
        v_____do__lift_214__boxed_6597_,
    );
    return v_res_6598_;
}
pub unsafe fn l_Array_findM_x3f___redArg___lam__1(
    mut v___x_6599_: *mut LeanObject,
    mut v_toPure_6600_: *mut LeanObject,
    mut v___x_6601_: *mut LeanObject,
    mut v_p_6602_: *mut LeanObject,
    mut v_toBind_6603_: *mut LeanObject,
    mut v_a_6604_: *mut LeanObject,
    mut v_x_6605_: *mut LeanObject,
    mut v___y_6606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6604_);
    v___f_6607_ = lean_alloc_closure(
        l_Array_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6607_, 0, v___x_6599_);
    lean_closure_set(v___f_6607_, 1, v_toPure_6600_);
    lean_closure_set(v___f_6607_, 2, v_a_6604_);
    lean_closure_set(v___f_6607_, 3, v___x_6601_);
    v___x_6608_ = lean_apply_1(v_p_6602_, v_a_6604_);
    v___x_6609_ = lean_apply_4(
        v_toBind_6603_,
        lean_box(0),
        lean_box(0),
        v___x_6608_,
        v___f_6607_,
    );
    return v___x_6609_;
}
pub unsafe fn l_Array_findM_x3f___redArg___lam__1___boxed(
    mut v___x_6610_: *mut LeanObject,
    mut v_toPure_6611_: *mut LeanObject,
    mut v___x_6612_: *mut LeanObject,
    mut v_p_6613_: *mut LeanObject,
    mut v_toBind_6614_: *mut LeanObject,
    mut v_a_6615_: *mut LeanObject,
    mut v_x_6616_: *mut LeanObject,
    mut v___y_6617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6618_: *mut LeanObject = core::ptr::null_mut();
    v_res_6618_ = l_Array_findM_x3f___redArg___lam__1(
        v___x_6610_,
        v_toPure_6611_,
        v___x_6612_,
        v_p_6613_,
        v_toBind_6614_,
        v_a_6615_,
        v_x_6616_,
        v___y_6617_,
    );
    lean_dec_ref(v___y_6617_);
    return v_res_6618_;
}
pub unsafe fn l_Array_findM_x3f___redArg(
    mut v_inst_6619_: *mut LeanObject,
    mut v_p_6620_: *mut LeanObject,
    mut v_as_6621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6629_: usize = 0;
    let mut v___x_6630_: usize = 0;
    let mut v___x_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6622_ = lean_ctor_get(v_inst_6619_, 0);
    v_toBind_6623_ = lean_ctor_get(v_inst_6619_, 1);
    lean_inc_n(v_toBind_6623_, 2);
    v_toPure_6624_ = lean_ctor_get(v_toApplicative_6622_, 1);
    v___x_6625_ = lean_box(0);
    v___x_6626_ = l_Array_findSomeM_x3f___redArg___closed__0;
    lean_inc_n(v_toPure_6624_, 2);
    v___f_6627_ = lean_alloc_closure(
        l_Array_findM_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_6627_, 0, v___x_6626_);
    lean_closure_set(v___f_6627_, 1, v_toPure_6624_);
    lean_closure_set(v___f_6627_, 2, v___x_6625_);
    lean_closure_set(v___f_6627_, 3, v_p_6620_);
    lean_closure_set(v___f_6627_, 4, v_toBind_6623_);
    v___f_6628_ = lean_alloc_closure(
        l_Array_findSomeM_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6628_, 0, v_toPure_6624_);
    v_sz_6629_ = lean_array_size(v_as_6621_);
    v___x_6630_ = 0usize;
    v___x_6631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
        v_inst_6619_,
        v_as_6621_,
        v___f_6627_,
        v_sz_6629_,
        v___x_6630_,
        v___x_6626_,
    );
    v___x_6632_ = lean_apply_4(
        v_toBind_6623_,
        lean_box(0),
        lean_box(0),
        v___x_6631_,
        v___f_6628_,
    );
    return v___x_6632_;
}
pub unsafe fn l_Array_findM_x3f(
    mut v_m_6633_: *mut LeanObject,
    mut v_00_u03b1_6634_: *mut LeanObject,
    mut v_inst_6635_: *mut LeanObject,
    mut v_p_6636_: *mut LeanObject,
    mut v_as_6637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6645_: usize = 0;
    let mut v___x_6646_: usize = 0;
    let mut v___x_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6648_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6638_ = lean_ctor_get(v_inst_6635_, 0);
    v_toBind_6639_ = lean_ctor_get(v_inst_6635_, 1);
    lean_inc_n(v_toBind_6639_, 2);
    v_toPure_6640_ = lean_ctor_get(v_toApplicative_6638_, 1);
    v___x_6641_ = lean_box(0);
    v___x_6642_ = l_Array_findSomeM_x3f___redArg___closed__0;
    lean_inc_n(v_toPure_6640_, 2);
    v___f_6643_ = lean_alloc_closure(
        l_Array_findM_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_6643_, 0, v___x_6642_);
    lean_closure_set(v___f_6643_, 1, v_toPure_6640_);
    lean_closure_set(v___f_6643_, 2, v___x_6641_);
    lean_closure_set(v___f_6643_, 3, v_p_6636_);
    lean_closure_set(v___f_6643_, 4, v_toBind_6639_);
    v___f_6644_ = lean_alloc_closure(
        l_Array_findSomeM_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6644_, 0, v_toPure_6640_);
    v_sz_6645_ = lean_array_size(v_as_6637_);
    v___x_6646_ = 0usize;
    v___x_6647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
        v_inst_6635_,
        v_as_6637_,
        v___f_6643_,
        v_sz_6645_,
        v___x_6646_,
        v___x_6642_,
    );
    v___x_6648_ = lean_apply_4(
        v_toBind_6639_,
        lean_box(0),
        lean_box(0),
        v___x_6647_,
        v___f_6644_,
    );
    return v___x_6648_;
}
pub unsafe fn l_Array_findIdxM_x3f___redArg___lam__0(
    mut v_snd_6649_: *mut LeanObject,
    mut v___x_6650_: *mut LeanObject,
    mut v_toPure_6651_: *mut LeanObject,
    mut v_____do__lift_6652_: u8,
) -> *mut LeanObject {
    if v_____do__lift_6652_ == 0 {
        let mut v___x_6653_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6654_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6655_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6656_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6657_: *mut LeanObject = core::ptr::null_mut();
        v___x_6653_ = lean_unsigned_to_nat(1);
        v___x_6654_ = lean_nat_add(v_snd_6649_, v___x_6653_);
        lean_dec(v_snd_6649_);
        v___x_6655_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_6655_, 0, v___x_6650_);
        lean_ctor_set(v___x_6655_, 1, v___x_6654_);
        v___x_6656_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_6656_, 0, v___x_6655_);
        v___x_6657_ = lean_apply_2(v_toPure_6651_, lean_box(0), v___x_6656_);
        return v___x_6657_;
    } else {
        let mut v___x_6658_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6659_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6660_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6661_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6662_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_6650_);
        lean_inc(v_snd_6649_);
        v___x_6658_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_6658_, 0, v_snd_6649_);
        v___x_6659_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_6659_, 0, v___x_6658_);
        v___x_6660_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_6660_, 0, v___x_6659_);
        lean_ctor_set(v___x_6660_, 1, v_snd_6649_);
        v___x_6661_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6661_, 0, v___x_6660_);
        v___x_6662_ = lean_apply_2(v_toPure_6651_, lean_box(0), v___x_6661_);
        return v___x_6662_;
    }
}
pub unsafe fn l_Array_findIdxM_x3f___redArg___lam__0___boxed(
    mut v_snd_6663_: *mut LeanObject,
    mut v___x_6664_: *mut LeanObject,
    mut v_toPure_6665_: *mut LeanObject,
    mut v_____do__lift_6666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_249__boxed_6667_: u8 = 0;
    let mut v_res_6668_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_249__boxed_6667_ = (lean_unbox(v_____do__lift_6666_) as u8);
    v_res_6668_ = l_Array_findIdxM_x3f___redArg___lam__0(
        v_snd_6663_,
        v___x_6664_,
        v_toPure_6665_,
        v_____do__lift_249__boxed_6667_,
    );
    return v_res_6668_;
}
pub unsafe fn l_Array_findIdxM_x3f___redArg___lam__1(
    mut v___x_6669_: *mut LeanObject,
    mut v_toPure_6670_: *mut LeanObject,
    mut v_p_6671_: *mut LeanObject,
    mut v_toBind_6672_: *mut LeanObject,
    mut v_a_6673_: *mut LeanObject,
    mut v_x_6674_: *mut LeanObject,
    mut v___y_6675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6679_: *mut LeanObject = core::ptr::null_mut();
    v_snd_6676_ = lean_ctor_get(v___y_6675_, 1);
    lean_inc(v_snd_6676_);
    lean_dec_ref(v___y_6675_);
    v___f_6677_ = lean_alloc_closure(
        l_Array_findIdxM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6677_, 0, v_snd_6676_);
    lean_closure_set(v___f_6677_, 1, v___x_6669_);
    lean_closure_set(v___f_6677_, 2, v_toPure_6670_);
    v___x_6678_ = lean_apply_1(v_p_6671_, v_a_6673_);
    v___x_6679_ = lean_apply_4(
        v_toBind_6672_,
        lean_box(0),
        lean_box(0),
        v___x_6678_,
        v___f_6677_,
    );
    return v___x_6679_;
}
pub unsafe fn l_Array_findIdxM_x3f___redArg___lam__2(
    mut v_toPure_6680_: *mut LeanObject,
    mut v_____s_6681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_6682_: *mut LeanObject = core::ptr::null_mut();
    v_fst_6682_ = lean_ctor_get(v_____s_6681_, 0);
    lean_inc(v_fst_6682_);
    lean_dec_ref(v_____s_6681_);
    if lean_obj_tag(v_fst_6682_) == 0 {
        let mut v___x_6683_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6684_: *mut LeanObject = core::ptr::null_mut();
        v___x_6683_ = lean_box(0);
        v___x_6684_ = lean_apply_2(v_toPure_6680_, lean_box(0), v___x_6683_);
        return v___x_6684_;
    } else {
        let mut v_val_6685_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6686_: *mut LeanObject = core::ptr::null_mut();
        v_val_6685_ = lean_ctor_get(v_fst_6682_, 0);
        lean_inc(v_val_6685_);
        lean_dec_ref_known(v_fst_6682_, 1);
        v___x_6686_ = lean_apply_2(v_toPure_6680_, lean_box(0), v_val_6685_);
        return v___x_6686_;
    }
}
pub unsafe fn l_Array_findIdxM_x3f___redArg(
    mut v_inst_6690_: *mut LeanObject,
    mut v_p_6691_: *mut LeanObject,
    mut v_as_6692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6700_: usize = 0;
    let mut v___x_6701_: usize = 0;
    let mut v___x_6702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6703_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6693_ = lean_ctor_get(v_inst_6690_, 0);
    v_toBind_6694_ = lean_ctor_get(v_inst_6690_, 1);
    lean_inc_n(v_toBind_6694_, 2);
    v_toPure_6695_ = lean_ctor_get(v_toApplicative_6693_, 1);
    v___x_6696_ = lean_box(0);
    v___x_6697_ = l_Array_findIdxM_x3f___redArg___closed__0;
    lean_inc_n(v_toPure_6695_, 2);
    v___f_6698_ = lean_alloc_closure(
        l_Array_findIdxM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_6698_, 0, v___x_6696_);
    lean_closure_set(v___f_6698_, 1, v_toPure_6695_);
    lean_closure_set(v___f_6698_, 2, v_p_6691_);
    lean_closure_set(v___f_6698_, 3, v_toBind_6694_);
    v___f_6699_ = lean_alloc_closure(
        l_Array_findIdxM_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6699_, 0, v_toPure_6695_);
    v_sz_6700_ = lean_array_size(v_as_6692_);
    v___x_6701_ = 0usize;
    v___x_6702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
        v_inst_6690_,
        v_as_6692_,
        v___f_6698_,
        v_sz_6700_,
        v___x_6701_,
        v___x_6697_,
    );
    v___x_6703_ = lean_apply_4(
        v_toBind_6694_,
        lean_box(0),
        lean_box(0),
        v___x_6702_,
        v___f_6699_,
    );
    return v___x_6703_;
}
pub unsafe fn l_Array_findIdxM_x3f(
    mut v_00_u03b1_6704_: *mut LeanObject,
    mut v_m_6705_: *mut LeanObject,
    mut v_inst_6706_: *mut LeanObject,
    mut v_p_6707_: *mut LeanObject,
    mut v_as_6708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6716_: usize = 0;
    let mut v___x_6717_: usize = 0;
    let mut v___x_6718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6719_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6709_ = lean_ctor_get(v_inst_6706_, 0);
    v_toBind_6710_ = lean_ctor_get(v_inst_6706_, 1);
    lean_inc_n(v_toBind_6710_, 2);
    v_toPure_6711_ = lean_ctor_get(v_toApplicative_6709_, 1);
    v___x_6712_ = lean_box(0);
    v___x_6713_ = l_Array_findIdxM_x3f___redArg___closed__0;
    lean_inc_n(v_toPure_6711_, 2);
    v___f_6714_ = lean_alloc_closure(
        l_Array_findIdxM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_6714_, 0, v___x_6712_);
    lean_closure_set(v___f_6714_, 1, v_toPure_6711_);
    lean_closure_set(v___f_6714_, 2, v_p_6707_);
    lean_closure_set(v___f_6714_, 3, v_toBind_6710_);
    v___f_6715_ = lean_alloc_closure(
        l_Array_findIdxM_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6715_, 0, v_toPure_6711_);
    v_sz_6716_ = lean_array_size(v_as_6708_);
    v___x_6717_ = 0usize;
    v___x_6718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
        v_inst_6706_,
        v_as_6708_,
        v___f_6714_,
        v_sz_6716_,
        v___x_6717_,
        v___x_6713_,
    );
    v___x_6719_ = lean_apply_4(
        v_toBind_6710_,
        lean_box(0),
        lean_box(0),
        v___x_6718_,
        v___f_6715_,
    );
    return v___x_6719_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed(
    mut v_i_6720_: *mut LeanObject,
    mut v_inst_6721_: *mut LeanObject,
    mut v_p_6722_: *mut LeanObject,
    mut v_as_6723_: *mut LeanObject,
    mut v_stop_6724_: *mut LeanObject,
    mut v_toApplicative_6725_: *mut LeanObject,
    mut v___x_6726_: *mut LeanObject,
    mut v_____do__lift_6727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6728_: usize = 0;
    let mut v_stop_boxed_6729_: usize = 0;
    let mut v___x_153__boxed_6730_: u8 = 0;
    let mut v_____do__lift_154__boxed_6731_: u8 = 0;
    let mut v_res_6732_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6728_ = lean_unbox_usize(v_i_6720_);
    lean_dec(v_i_6720_);
    v_stop_boxed_6729_ = lean_unbox_usize(v_stop_6724_);
    lean_dec(v_stop_6724_);
    v___x_153__boxed_6730_ = (lean_unbox(v___x_6726_) as u8);
    v_____do__lift_154__boxed_6731_ = (lean_unbox(v_____do__lift_6727_) as u8);
    v_res_6732_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(
        v_i_boxed_6728_,
        v_inst_6721_,
        v_p_6722_,
        v_as_6723_,
        v_stop_boxed_6729_,
        v_toApplicative_6725_,
        v___x_153__boxed_6730_,
        v_____do__lift_154__boxed_6731_,
    );
    return v_res_6732_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(
    mut v_inst_6733_: *mut LeanObject,
    mut v_p_6734_: *mut LeanObject,
    mut v_as_6735_: *mut LeanObject,
    mut v_i_6736_: usize,
    mut v_stop_6737_: usize,
) -> *mut LeanObject {
    let mut v___x_6738_: u8 = 0;
    v___x_6738_ = lean_usize_dec_eq(v_i_6736_, v_stop_6737_);
    if v___x_6738_ == 0 {
        let mut v_toApplicative_6739_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_6740_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6741_: u8 = 0;
        let mut v___x_6742_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6743_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6744_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_6745_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6746_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6747_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6748_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_6739_ = lean_ctor_get(v_inst_6733_, 0);
        lean_inc_ref(v_toApplicative_6739_);
        v_toBind_6740_ = lean_ctor_get(v_inst_6733_, 1);
        lean_inc(v_toBind_6740_);
        v___x_6741_ = 1;
        v___x_6742_ = lean_box_usize(v_i_6736_);
        v___x_6743_ = lean_box_usize(v_stop_6737_);
        v___x_6744_ = lean_box((v___x_6741_) as usize);
        lean_inc_ref(v_as_6735_);
        lean_inc(v_p_6734_);
        v___f_6745_ = lean_alloc_closure(
            l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            8,
            7,
        );
        lean_closure_set(v___f_6745_, 0, v___x_6742_);
        lean_closure_set(v___f_6745_, 1, v_inst_6733_);
        lean_closure_set(v___f_6745_, 2, v_p_6734_);
        lean_closure_set(v___f_6745_, 3, v_as_6735_);
        lean_closure_set(v___f_6745_, 4, v___x_6743_);
        lean_closure_set(v___f_6745_, 5, v_toApplicative_6739_);
        lean_closure_set(v___f_6745_, 6, v___x_6744_);
        v___x_6746_ = lean_array_uget(v_as_6735_, v_i_6736_);
        lean_dec_ref(v_as_6735_);
        v___x_6747_ = lean_apply_1(v_p_6734_, v___x_6746_);
        v___x_6748_ = lean_apply_4(
            v_toBind_6740_,
            lean_box(0),
            lean_box(0),
            v___x_6747_,
            v___f_6745_,
        );
        return v___x_6748_;
    } else {
        let mut v_toApplicative_6749_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_6750_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6751_: u8 = 0;
        let mut v___x_6752_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6753_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_as_6735_);
        lean_dec(v_p_6734_);
        v_toApplicative_6749_ = lean_ctor_get(v_inst_6733_, 0);
        lean_inc_ref(v_toApplicative_6749_);
        lean_dec_ref(v_inst_6733_);
        v_toPure_6750_ = lean_ctor_get(v_toApplicative_6749_, 1);
        lean_inc(v_toPure_6750_);
        lean_dec_ref(v_toApplicative_6749_);
        v___x_6751_ = 0;
        v___x_6752_ = lean_box((v___x_6751_) as usize);
        v___x_6753_ = lean_apply_2(v_toPure_6750_, lean_box(0), v___x_6752_);
        return v___x_6753_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(
    mut v_i_6754_: usize,
    mut v_inst_6755_: *mut LeanObject,
    mut v_p_6756_: *mut LeanObject,
    mut v_as_6757_: *mut LeanObject,
    mut v_stop_6758_: usize,
    mut v_toApplicative_6759_: *mut LeanObject,
    mut v___x_6760_: u8,
    mut v_____do__lift_6761_: u8,
) -> *mut LeanObject {
    if v_____do__lift_6761_ == 0 {
        let mut v___x_6762_: usize = 0;
        let mut v___x_6763_: usize = 0;
        let mut v___x_6764_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_6759_);
        v___x_6762_ = 1usize;
        v___x_6763_ = lean_usize_add(v_i_6754_, v___x_6762_);
        v___x_6764_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(
            v_inst_6755_,
            v_p_6756_,
            v_as_6757_,
            v___x_6763_,
            v_stop_6758_,
        );
        return v___x_6764_;
    } else {
        let mut v_toPure_6765_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6766_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6767_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_as_6757_);
        lean_dec(v_p_6756_);
        lean_dec_ref(v_inst_6755_);
        v_toPure_6765_ = lean_ctor_get(v_toApplicative_6759_, 1);
        lean_inc(v_toPure_6765_);
        lean_dec_ref(v_toApplicative_6759_);
        v___x_6766_ = lean_box((v___x_6760_) as usize);
        v___x_6767_ = lean_apply_2(v_toPure_6765_, lean_box(0), v___x_6766_);
        return v___x_6767_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___boxed(
    mut v_inst_6768_: *mut LeanObject,
    mut v_p_6769_: *mut LeanObject,
    mut v_as_6770_: *mut LeanObject,
    mut v_i_6771_: *mut LeanObject,
    mut v_stop_6772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6773_: usize = 0;
    let mut v_stop_boxed_6774_: usize = 0;
    let mut v_res_6775_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6773_ = lean_unbox_usize(v_i_6771_);
    lean_dec(v_i_6771_);
    v_stop_boxed_6774_ = lean_unbox_usize(v_stop_6772_);
    lean_dec(v_stop_6772_);
    v_res_6775_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(
        v_inst_6768_,
        v_p_6769_,
        v_as_6770_,
        v_i_boxed_6773_,
        v_stop_boxed_6774_,
    );
    return v_res_6775_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
    mut v_00_u03b1_6776_: *mut LeanObject,
    mut v_m_6777_: *mut LeanObject,
    mut v_inst_6778_: *mut LeanObject,
    mut v_p_6779_: *mut LeanObject,
    mut v_as_6780_: *mut LeanObject,
    mut v_i_6781_: usize,
    mut v_stop_6782_: usize,
) -> *mut LeanObject {
    let mut v___x_6783_: *mut LeanObject = core::ptr::null_mut();
    v___x_6783_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(
        v_inst_6778_,
        v_p_6779_,
        v_as_6780_,
        v_i_6781_,
        v_stop_6782_,
    );
    return v___x_6783_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___boxed(
    mut v_00_u03b1_6784_: *mut LeanObject,
    mut v_m_6785_: *mut LeanObject,
    mut v_inst_6786_: *mut LeanObject,
    mut v_p_6787_: *mut LeanObject,
    mut v_as_6788_: *mut LeanObject,
    mut v_i_6789_: *mut LeanObject,
    mut v_stop_6790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6791_: usize = 0;
    let mut v_stop_boxed_6792_: usize = 0;
    let mut v_res_6793_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6791_ = lean_unbox_usize(v_i_6789_);
    lean_dec(v_i_6789_);
    v_stop_boxed_6792_ = lean_unbox_usize(v_stop_6790_);
    lean_dec(v_stop_6790_);
    v_res_6793_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
        v_00_u03b1_6784_,
        v_m_6785_,
        v_inst_6786_,
        v_p_6787_,
        v_as_6788_,
        v_i_boxed_6791_,
        v_stop_boxed_6792_,
    );
    return v_res_6793_;
}
pub unsafe fn l_Array_anyMUnsafe___redArg(
    mut v_inst_6794_: *mut LeanObject,
    mut v_p_6795_: *mut LeanObject,
    mut v_as_6796_: *mut LeanObject,
    mut v_start_6797_: *mut LeanObject,
    mut v_stop_6798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: u8 = 0;
    let mut v_toApplicative_6802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: usize = 0;
    let mut v___x_6807_: usize = 0;
    let mut v___x_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: u8 = 0;
    let mut v_toApplicative_6810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6815_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6809_ = lean_nat_dec_lt(v_start_6797_, v_stop_6798_);
                if v___x_6809_ == 0 {
                    lean_dec(v_stop_6798_);
                    lean_dec_ref(v_as_6796_);
                    lean_dec(v_p_6795_);
                    v_toApplicative_6810_ = lean_ctor_get(v_inst_6794_, 0);
                    lean_inc_ref(v_toApplicative_6810_);
                    lean_dec_ref(v_inst_6794_);
                    v_toPure_6811_ = lean_ctor_get(v_toApplicative_6810_, 1);
                    lean_inc(v_toPure_6811_);
                    lean_dec_ref(v_toApplicative_6810_);
                    v___x_6812_ = lean_box((v___x_6809_) as usize);
                    v___x_6813_ = lean_apply_2(v_toPure_6811_, lean_box(0), v___x_6812_);
                    return v___x_6813_;
                } else {
                    v___x_6814_ = lean_array_get_size(v_as_6796_);
                    v___x_6815_ = lean_nat_dec_le(v_stop_6798_, v___x_6814_);
                    if v___x_6815_ == 0 {
                        lean_dec(v_stop_6798_);
                        v___y_6800_ = v___x_6814_;
                        state = 1;
                        continue;
                    } else {
                        v___y_6800_ = v_stop_6798_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6801_ = lean_nat_dec_lt(v_start_6797_, v___y_6800_);
                if v___x_6801_ == 0 {
                    lean_dec(v___y_6800_);
                    lean_dec_ref(v_as_6796_);
                    lean_dec(v_p_6795_);
                    v_toApplicative_6802_ = lean_ctor_get(v_inst_6794_, 0);
                    lean_inc_ref(v_toApplicative_6802_);
                    lean_dec_ref(v_inst_6794_);
                    v_toPure_6803_ = lean_ctor_get(v_toApplicative_6802_, 1);
                    lean_inc(v_toPure_6803_);
                    lean_dec_ref(v_toApplicative_6802_);
                    v___x_6804_ = lean_box((v___x_6801_) as usize);
                    v___x_6805_ = lean_apply_2(v_toPure_6803_, lean_box(0), v___x_6804_);
                    return v___x_6805_;
                } else {
                    v___x_6806_ = lean_usize_of_nat(v_start_6797_);
                    v___x_6807_ = lean_usize_of_nat(v___y_6800_);
                    lean_dec(v___y_6800_);
                    v___x_6808_ =
                        l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(
                            v_inst_6794_,
                            v_p_6795_,
                            v_as_6796_,
                            v___x_6806_,
                            v___x_6807_,
                        );
                    return v___x_6808_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_anyMUnsafe___redArg___boxed(
    mut v_inst_6816_: *mut LeanObject,
    mut v_p_6817_: *mut LeanObject,
    mut v_as_6818_: *mut LeanObject,
    mut v_start_6819_: *mut LeanObject,
    mut v_stop_6820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6821_: *mut LeanObject = core::ptr::null_mut();
    v_res_6821_ = l_Array_anyMUnsafe___redArg(
        v_inst_6816_,
        v_p_6817_,
        v_as_6818_,
        v_start_6819_,
        v_stop_6820_,
    );
    lean_dec(v_start_6819_);
    return v_res_6821_;
}
pub unsafe fn l_Array_anyMUnsafe(
    mut v_00_u03b1_6822_: *mut LeanObject,
    mut v_m_6823_: *mut LeanObject,
    mut v_inst_6824_: *mut LeanObject,
    mut v_p_6825_: *mut LeanObject,
    mut v_as_6826_: *mut LeanObject,
    mut v_start_6827_: *mut LeanObject,
    mut v_stop_6828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6831_: u8 = 0;
    let mut v_toApplicative_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: usize = 0;
    let mut v___x_6837_: usize = 0;
    let mut v___x_6838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6839_: u8 = 0;
    let mut v_toApplicative_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6839_ = lean_nat_dec_lt(v_start_6827_, v_stop_6828_);
                if v___x_6839_ == 0 {
                    lean_dec(v_stop_6828_);
                    lean_dec_ref(v_as_6826_);
                    lean_dec(v_p_6825_);
                    v_toApplicative_6840_ = lean_ctor_get(v_inst_6824_, 0);
                    lean_inc_ref(v_toApplicative_6840_);
                    lean_dec_ref(v_inst_6824_);
                    v_toPure_6841_ = lean_ctor_get(v_toApplicative_6840_, 1);
                    lean_inc(v_toPure_6841_);
                    lean_dec_ref(v_toApplicative_6840_);
                    v___x_6842_ = lean_box((v___x_6839_) as usize);
                    v___x_6843_ = lean_apply_2(v_toPure_6841_, lean_box(0), v___x_6842_);
                    return v___x_6843_;
                } else {
                    v___x_6844_ = lean_array_get_size(v_as_6826_);
                    v___x_6845_ = lean_nat_dec_le(v_stop_6828_, v___x_6844_);
                    if v___x_6845_ == 0 {
                        lean_dec(v_stop_6828_);
                        v___y_6830_ = v___x_6844_;
                        state = 1;
                        continue;
                    } else {
                        v___y_6830_ = v_stop_6828_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6831_ = lean_nat_dec_lt(v_start_6827_, v___y_6830_);
                if v___x_6831_ == 0 {
                    lean_dec(v___y_6830_);
                    lean_dec_ref(v_as_6826_);
                    lean_dec(v_p_6825_);
                    v_toApplicative_6832_ = lean_ctor_get(v_inst_6824_, 0);
                    lean_inc_ref(v_toApplicative_6832_);
                    lean_dec_ref(v_inst_6824_);
                    v_toPure_6833_ = lean_ctor_get(v_toApplicative_6832_, 1);
                    lean_inc(v_toPure_6833_);
                    lean_dec_ref(v_toApplicative_6832_);
                    v___x_6834_ = lean_box((v___x_6831_) as usize);
                    v___x_6835_ = lean_apply_2(v_toPure_6833_, lean_box(0), v___x_6834_);
                    return v___x_6835_;
                } else {
                    v___x_6836_ = lean_usize_of_nat(v_start_6827_);
                    v___x_6837_ = lean_usize_of_nat(v___y_6830_);
                    lean_dec(v___y_6830_);
                    v___x_6838_ =
                        l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(
                            v_inst_6824_,
                            v_p_6825_,
                            v_as_6826_,
                            v___x_6836_,
                            v___x_6837_,
                        );
                    return v___x_6838_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_anyMUnsafe___boxed(
    mut v_00_u03b1_6846_: *mut LeanObject,
    mut v_m_6847_: *mut LeanObject,
    mut v_inst_6848_: *mut LeanObject,
    mut v_p_6849_: *mut LeanObject,
    mut v_as_6850_: *mut LeanObject,
    mut v_start_6851_: *mut LeanObject,
    mut v_stop_6852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6853_: *mut LeanObject = core::ptr::null_mut();
    v_res_6853_ = l_Array_anyMUnsafe(
        v_00_u03b1_6846_,
        v_m_6847_,
        v_inst_6848_,
        v_p_6849_,
        v_as_6850_,
        v_start_6851_,
        v_stop_6852_,
    );
    lean_dec(v_start_6851_);
    return v_res_6853_;
}
pub unsafe fn l_Array_anyM_loop___redArg___lam__0___boxed(
    mut v_j_6854_: *mut LeanObject,
    mut v_inst_6855_: *mut LeanObject,
    mut v_p_6856_: *mut LeanObject,
    mut v_as_6857_: *mut LeanObject,
    mut v_stop_6858_: *mut LeanObject,
    mut v_toApplicative_6859_: *mut LeanObject,
    mut v_____do__lift_6860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_82__boxed_6861_: u8 = 0;
    let mut v_res_6862_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_82__boxed_6861_ = (lean_unbox(v_____do__lift_6860_) as u8);
    v_res_6862_ = l_Array_anyM_loop___redArg___lam__0(
        v_j_6854_,
        v_inst_6855_,
        v_p_6856_,
        v_as_6857_,
        v_stop_6858_,
        v_toApplicative_6859_,
        v_____do__lift_82__boxed_6861_,
    );
    lean_dec(v_j_6854_);
    return v_res_6862_;
}
pub unsafe fn l_Array_anyM_loop___redArg(
    mut v_inst_6863_: *mut LeanObject,
    mut v_p_6864_: *mut LeanObject,
    mut v_as_6865_: *mut LeanObject,
    mut v_stop_6866_: *mut LeanObject,
    mut v_j_6867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6868_: u8 = 0;
    v___x_6868_ = lean_nat_dec_lt(v_j_6867_, v_stop_6866_);
    if v___x_6868_ == 0 {
        let mut v_toApplicative_6869_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_6870_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6871_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6872_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_j_6867_);
        lean_dec(v_stop_6866_);
        lean_dec_ref(v_as_6865_);
        lean_dec(v_p_6864_);
        v_toApplicative_6869_ = lean_ctor_get(v_inst_6863_, 0);
        lean_inc_ref(v_toApplicative_6869_);
        lean_dec_ref(v_inst_6863_);
        v_toPure_6870_ = lean_ctor_get(v_toApplicative_6869_, 1);
        lean_inc(v_toPure_6870_);
        lean_dec_ref(v_toApplicative_6869_);
        v___x_6871_ = lean_box((v___x_6868_) as usize);
        v___x_6872_ = lean_apply_2(v_toPure_6870_, lean_box(0), v___x_6871_);
        return v___x_6872_;
    } else {
        let mut v_toApplicative_6873_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_6874_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_6875_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6876_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6877_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6878_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_6873_ = lean_ctor_get(v_inst_6863_, 0);
        lean_inc_ref(v_toApplicative_6873_);
        v_toBind_6874_ = lean_ctor_get(v_inst_6863_, 1);
        lean_inc(v_toBind_6874_);
        lean_inc_ref(v_as_6865_);
        lean_inc(v_p_6864_);
        lean_inc(v_j_6867_);
        v___f_6875_ = lean_alloc_closure(
            l_Array_anyM_loop___redArg___lam__0___boxed as *mut core::ffi::c_void,
            7,
            6,
        );
        lean_closure_set(v___f_6875_, 0, v_j_6867_);
        lean_closure_set(v___f_6875_, 1, v_inst_6863_);
        lean_closure_set(v___f_6875_, 2, v_p_6864_);
        lean_closure_set(v___f_6875_, 3, v_as_6865_);
        lean_closure_set(v___f_6875_, 4, v_stop_6866_);
        lean_closure_set(v___f_6875_, 5, v_toApplicative_6873_);
        v___x_6876_ = lean_array_fget(v_as_6865_, v_j_6867_);
        lean_dec(v_j_6867_);
        lean_dec_ref(v_as_6865_);
        v___x_6877_ = lean_apply_1(v_p_6864_, v___x_6876_);
        v___x_6878_ = lean_apply_4(
            v_toBind_6874_,
            lean_box(0),
            lean_box(0),
            v___x_6877_,
            v___f_6875_,
        );
        return v___x_6878_;
    }
}
pub unsafe fn l_Array_anyM_loop___redArg___lam__0(
    mut v_j_6879_: *mut LeanObject,
    mut v_inst_6880_: *mut LeanObject,
    mut v_p_6881_: *mut LeanObject,
    mut v_as_6882_: *mut LeanObject,
    mut v_stop_6883_: *mut LeanObject,
    mut v_toApplicative_6884_: *mut LeanObject,
    mut v_____do__lift_6885_: u8,
) -> *mut LeanObject {
    if v_____do__lift_6885_ == 0 {
        let mut v___x_6886_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6887_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6888_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_6884_);
        v___x_6886_ = lean_unsigned_to_nat(1);
        v___x_6887_ = lean_nat_add(v_j_6879_, v___x_6886_);
        v___x_6888_ = l_Array_anyM_loop___redArg(
            v_inst_6880_,
            v_p_6881_,
            v_as_6882_,
            v_stop_6883_,
            v___x_6887_,
        );
        return v___x_6888_;
    } else {
        let mut v_toPure_6889_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6890_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6891_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stop_6883_);
        lean_dec_ref(v_as_6882_);
        lean_dec(v_p_6881_);
        lean_dec_ref(v_inst_6880_);
        v_toPure_6889_ = lean_ctor_get(v_toApplicative_6884_, 1);
        lean_inc(v_toPure_6889_);
        lean_dec_ref(v_toApplicative_6884_);
        v___x_6890_ = lean_box((v_____do__lift_6885_) as usize);
        v___x_6891_ = lean_apply_2(v_toPure_6889_, lean_box(0), v___x_6890_);
        return v___x_6891_;
    }
}
pub unsafe fn l_Array_anyM_loop(
    mut v_00_u03b1_6892_: *mut LeanObject,
    mut v_m_6893_: *mut LeanObject,
    mut v_inst_6894_: *mut LeanObject,
    mut v_p_6895_: *mut LeanObject,
    mut v_as_6896_: *mut LeanObject,
    mut v_stop_6897_: *mut LeanObject,
    mut v_h_6898_: *mut LeanObject,
    mut v_j_6899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6900_: *mut LeanObject = core::ptr::null_mut();
    v___x_6900_ =
        l_Array_anyM_loop___redArg(v_inst_6894_, v_p_6895_, v_as_6896_, v_stop_6897_, v_j_6899_);
    return v___x_6900_;
}
pub unsafe fn l_Array_allM___redArg___lam__0(
    mut v_toPure_6901_: *mut LeanObject,
    mut v_____do__lift_6902_: u8,
) -> *mut LeanObject {
    if v_____do__lift_6902_ == 0 {
        let mut v___x_6903_: u8 = 0;
        let mut v___x_6904_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6905_: *mut LeanObject = core::ptr::null_mut();
        v___x_6903_ = 1;
        v___x_6904_ = lean_box((v___x_6903_) as usize);
        v___x_6905_ = lean_apply_2(v_toPure_6901_, lean_box(0), v___x_6904_);
        return v___x_6905_;
    } else {
        let mut v___x_6906_: u8 = 0;
        let mut v___x_6907_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6908_: *mut LeanObject = core::ptr::null_mut();
        v___x_6906_ = 0;
        v___x_6907_ = lean_box((v___x_6906_) as usize);
        v___x_6908_ = lean_apply_2(v_toPure_6901_, lean_box(0), v___x_6907_);
        return v___x_6908_;
    }
}
pub unsafe fn l_Array_allM___redArg___lam__0___boxed(
    mut v_toPure_6909_: *mut LeanObject,
    mut v_____do__lift_6910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_123__boxed_6911_: u8 = 0;
    let mut v_res_6912_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_123__boxed_6911_ = (lean_unbox(v_____do__lift_6910_) as u8);
    v_res_6912_ = l_Array_allM___redArg___lam__0(v_toPure_6909_, v_____do__lift_123__boxed_6911_);
    return v_res_6912_;
}
pub unsafe fn l_Array_allM___redArg___lam__1(
    mut v_toPure_6913_: *mut LeanObject,
    mut v___x_6914_: u8,
    mut v_____do__lift_6915_: u8,
) -> *mut LeanObject {
    if v_____do__lift_6915_ == 0 {
        let mut v___x_6916_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6917_: *mut LeanObject = core::ptr::null_mut();
        v___x_6916_ = lean_box((v___x_6914_) as usize);
        v___x_6917_ = lean_apply_2(v_toPure_6913_, lean_box(0), v___x_6916_);
        return v___x_6917_;
    } else {
        let mut v___x_6918_: u8 = 0;
        let mut v___x_6919_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6920_: *mut LeanObject = core::ptr::null_mut();
        v___x_6918_ = 0;
        v___x_6919_ = lean_box((v___x_6918_) as usize);
        v___x_6920_ = lean_apply_2(v_toPure_6913_, lean_box(0), v___x_6919_);
        return v___x_6920_;
    }
}
pub unsafe fn l_Array_allM___redArg___lam__1___boxed(
    mut v_toPure_6921_: *mut LeanObject,
    mut v___x_6922_: *mut LeanObject,
    mut v_____do__lift_6923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_138__boxed_6924_: u8 = 0;
    let mut v_____do__lift_139__boxed_6925_: u8 = 0;
    let mut v_res_6926_: *mut LeanObject = core::ptr::null_mut();
    v___x_138__boxed_6924_ = (lean_unbox(v___x_6922_) as u8);
    v_____do__lift_139__boxed_6925_ = (lean_unbox(v_____do__lift_6923_) as u8);
    v_res_6926_ = l_Array_allM___redArg___lam__1(
        v_toPure_6921_,
        v___x_138__boxed_6924_,
        v_____do__lift_139__boxed_6925_,
    );
    return v_res_6926_;
}
pub unsafe fn l_Array_allM___redArg___lam__2(
    mut v_p_6927_: *mut LeanObject,
    mut v_toBind_6928_: *mut LeanObject,
    mut v___f_6929_: *mut LeanObject,
    mut v_v_6930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut LeanObject = core::ptr::null_mut();
    v___x_6931_ = lean_apply_1(v_p_6927_, v_v_6930_);
    v___x_6932_ = lean_apply_4(
        v_toBind_6928_,
        lean_box(0),
        lean_box(0),
        v___x_6931_,
        v___f_6929_,
    );
    return v___x_6932_;
}
pub unsafe fn l_Array_allM___redArg(
    mut v_inst_6933_: *mut LeanObject,
    mut v_p_6934_: *mut LeanObject,
    mut v_as_6935_: *mut LeanObject,
    mut v_start_6936_: *mut LeanObject,
    mut v_stop_6937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6942_: u8 = 0;
    let mut v___x_6943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: u8 = 0;
    let mut v___x_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: usize = 0;
    let mut v___x_6956_: usize = 0;
    let mut v___x_6957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_6938_ = lean_ctor_get(v_inst_6933_, 0);
                v_toBind_6939_ = lean_ctor_get(v_inst_6933_, 1);
                lean_inc(v_toBind_6939_);
                v_toPure_6940_ = lean_ctor_get(v_toApplicative_6938_, 1);
                lean_inc(v_toPure_6940_);
                v___f_6941_ = lean_alloc_closure(
                    l_Array_allM___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_6941_, 0, v_toPure_6940_);
                v___x_6942_ = lean_nat_dec_lt(v_start_6936_, v_stop_6937_);
                if v___x_6942_ == 0 {
                    lean_inc(v_toPure_6940_);
                    lean_dec(v_stop_6937_);
                    lean_dec_ref(v_as_6935_);
                    lean_dec(v_p_6934_);
                    lean_dec_ref(v_inst_6933_);
                    v___x_6943_ = lean_box((v___x_6942_) as usize);
                    v___x_6944_ = lean_apply_2(v_toPure_6940_, lean_box(0), v___x_6943_);
                    v___x_6945_ = lean_apply_4(
                        v_toBind_6939_,
                        lean_box(0),
                        lean_box(0),
                        v___x_6944_,
                        v___f_6941_,
                    );
                    return v___x_6945_;
                } else {
                    v___x_6946_ = lean_box((v___x_6942_) as usize);
                    lean_inc(v_toPure_6940_);
                    v___f_6947_ = lean_alloc_closure(
                        l_Array_allM___redArg___lam__1___boxed as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    lean_closure_set(v___f_6947_, 0, v_toPure_6940_);
                    lean_closure_set(v___f_6947_, 1, v___x_6946_);
                    lean_inc(v_toBind_6939_);
                    v___f_6948_ = lean_alloc_closure(
                        l_Array_allM___redArg___lam__2 as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_6948_, 0, v_p_6934_);
                    lean_closure_set(v___f_6948_, 1, v_toBind_6939_);
                    lean_closure_set(v___f_6948_, 2, v___f_6947_);
                    v___x_6959_ = lean_array_get_size(v_as_6935_);
                    v___x_6960_ = lean_nat_dec_le(v_stop_6937_, v___x_6959_);
                    if v___x_6960_ == 0 {
                        lean_dec(v_stop_6937_);
                        v___y_6950_ = v___x_6959_;
                        state = 1;
                        continue;
                    } else {
                        v___y_6950_ = v_stop_6937_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6951_ = lean_nat_dec_lt(v_start_6936_, v___y_6950_);
                if v___x_6951_ == 0 {
                    lean_inc(v_toPure_6940_);
                    lean_dec(v___y_6950_);
                    lean_dec_ref(v___f_6948_);
                    lean_dec_ref(v_as_6935_);
                    lean_dec_ref(v_inst_6933_);
                    v___x_6952_ = lean_box((v___x_6951_) as usize);
                    v___x_6953_ = lean_apply_2(v_toPure_6940_, lean_box(0), v___x_6952_);
                    v___x_6954_ = lean_apply_4(
                        v_toBind_6939_,
                        lean_box(0),
                        lean_box(0),
                        v___x_6953_,
                        v___f_6941_,
                    );
                    return v___x_6954_;
                } else {
                    v___x_6955_ = lean_usize_of_nat(v_start_6936_);
                    v___x_6956_ = lean_usize_of_nat(v___y_6950_);
                    lean_dec(v___y_6950_);
                    v___x_6957_ =
                        l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(
                            v_inst_6933_,
                            v___f_6948_,
                            v_as_6935_,
                            v___x_6955_,
                            v___x_6956_,
                        );
                    v___x_6958_ = lean_apply_4(
                        v_toBind_6939_,
                        lean_box(0),
                        lean_box(0),
                        v___x_6957_,
                        v___f_6941_,
                    );
                    return v___x_6958_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_allM___redArg___boxed(
    mut v_inst_6961_: *mut LeanObject,
    mut v_p_6962_: *mut LeanObject,
    mut v_as_6963_: *mut LeanObject,
    mut v_start_6964_: *mut LeanObject,
    mut v_stop_6965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6966_: *mut LeanObject = core::ptr::null_mut();
    v_res_6966_ = l_Array_allM___redArg(
        v_inst_6961_,
        v_p_6962_,
        v_as_6963_,
        v_start_6964_,
        v_stop_6965_,
    );
    lean_dec(v_start_6964_);
    return v_res_6966_;
}
pub unsafe fn l_Array_allM(
    mut v_00_u03b1_6967_: *mut LeanObject,
    mut v_m_6968_: *mut LeanObject,
    mut v_inst_6969_: *mut LeanObject,
    mut v_p_6970_: *mut LeanObject,
    mut v_as_6971_: *mut LeanObject,
    mut v_start_6972_: *mut LeanObject,
    mut v_stop_6973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: u8 = 0;
    let mut v___x_6979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: u8 = 0;
    let mut v___x_6988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: usize = 0;
    let mut v___x_6992_: usize = 0;
    let mut v___x_6993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6996_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_6974_ = lean_ctor_get(v_inst_6969_, 0);
                v_toBind_6975_ = lean_ctor_get(v_inst_6969_, 1);
                lean_inc(v_toBind_6975_);
                v_toPure_6976_ = lean_ctor_get(v_toApplicative_6974_, 1);
                lean_inc(v_toPure_6976_);
                v___f_6977_ = lean_alloc_closure(
                    l_Array_allM___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_6977_, 0, v_toPure_6976_);
                v___x_6978_ = lean_nat_dec_lt(v_start_6972_, v_stop_6973_);
                if v___x_6978_ == 0 {
                    lean_inc(v_toPure_6976_);
                    lean_dec(v_stop_6973_);
                    lean_dec_ref(v_as_6971_);
                    lean_dec(v_p_6970_);
                    lean_dec_ref(v_inst_6969_);
                    v___x_6979_ = lean_box((v___x_6978_) as usize);
                    v___x_6980_ = lean_apply_2(v_toPure_6976_, lean_box(0), v___x_6979_);
                    v___x_6981_ = lean_apply_4(
                        v_toBind_6975_,
                        lean_box(0),
                        lean_box(0),
                        v___x_6980_,
                        v___f_6977_,
                    );
                    return v___x_6981_;
                } else {
                    v___x_6982_ = lean_box((v___x_6978_) as usize);
                    lean_inc(v_toPure_6976_);
                    v___f_6983_ = lean_alloc_closure(
                        l_Array_allM___redArg___lam__1___boxed as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    lean_closure_set(v___f_6983_, 0, v_toPure_6976_);
                    lean_closure_set(v___f_6983_, 1, v___x_6982_);
                    lean_inc(v_toBind_6975_);
                    v___f_6984_ = lean_alloc_closure(
                        l_Array_allM___redArg___lam__2 as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_6984_, 0, v_p_6970_);
                    lean_closure_set(v___f_6984_, 1, v_toBind_6975_);
                    lean_closure_set(v___f_6984_, 2, v___f_6983_);
                    v___x_6995_ = lean_array_get_size(v_as_6971_);
                    v___x_6996_ = lean_nat_dec_le(v_stop_6973_, v___x_6995_);
                    if v___x_6996_ == 0 {
                        lean_dec(v_stop_6973_);
                        v___y_6986_ = v___x_6995_;
                        state = 1;
                        continue;
                    } else {
                        v___y_6986_ = v_stop_6973_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6987_ = lean_nat_dec_lt(v_start_6972_, v___y_6986_);
                if v___x_6987_ == 0 {
                    lean_inc(v_toPure_6976_);
                    lean_dec(v___y_6986_);
                    lean_dec_ref(v___f_6984_);
                    lean_dec_ref(v_as_6971_);
                    lean_dec_ref(v_inst_6969_);
                    v___x_6988_ = lean_box((v___x_6987_) as usize);
                    v___x_6989_ = lean_apply_2(v_toPure_6976_, lean_box(0), v___x_6988_);
                    v___x_6990_ = lean_apply_4(
                        v_toBind_6975_,
                        lean_box(0),
                        lean_box(0),
                        v___x_6989_,
                        v___f_6977_,
                    );
                    return v___x_6990_;
                } else {
                    v___x_6991_ = lean_usize_of_nat(v_start_6972_);
                    v___x_6992_ = lean_usize_of_nat(v___y_6986_);
                    lean_dec(v___y_6986_);
                    v___x_6993_ =
                        l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(
                            v_inst_6969_,
                            v___f_6984_,
                            v_as_6971_,
                            v___x_6991_,
                            v___x_6992_,
                        );
                    v___x_6994_ = lean_apply_4(
                        v_toBind_6975_,
                        lean_box(0),
                        lean_box(0),
                        v___x_6993_,
                        v___f_6977_,
                    );
                    return v___x_6994_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_allM___boxed(
    mut v_00_u03b1_6997_: *mut LeanObject,
    mut v_m_6998_: *mut LeanObject,
    mut v_inst_6999_: *mut LeanObject,
    mut v_p_7000_: *mut LeanObject,
    mut v_as_7001_: *mut LeanObject,
    mut v_start_7002_: *mut LeanObject,
    mut v_stop_7003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7004_: *mut LeanObject = core::ptr::null_mut();
    v_res_7004_ = l_Array_allM(
        v_00_u03b1_6997_,
        v_m_6998_,
        v_inst_6999_,
        v_p_7000_,
        v_as_7001_,
        v_start_7002_,
        v_stop_7003_,
    );
    lean_dec(v_start_7002_);
    return v_res_7004_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed(
    mut v_inst_7005_: *mut LeanObject,
    mut v_f_7006_: *mut LeanObject,
    mut v_as_7007_: *mut LeanObject,
    mut v_n_7008_: *mut LeanObject,
    mut v_toPure_7009_: *mut LeanObject,
    mut v_r_7010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7011_: *mut LeanObject = core::ptr::null_mut();
    v_res_7011_ =
        l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(
            v_inst_7005_,
            v_f_7006_,
            v_as_7007_,
            v_n_7008_,
            v_toPure_7009_,
            v_r_7010_,
        );
    lean_dec(v_n_7008_);
    return v_res_7011_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(
    mut v_inst_7012_: *mut LeanObject,
    mut v_f_7013_: *mut LeanObject,
    mut v_as_7014_: *mut LeanObject,
    mut v_i_7015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_7019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_7020_: u8 = 0;
    v_toApplicative_7016_ = lean_ctor_get(v_inst_7012_, 0);
    v_toBind_7017_ = lean_ctor_get(v_inst_7012_, 1);
    lean_inc(v_toBind_7017_);
    v_toPure_7018_ = lean_ctor_get(v_toApplicative_7016_, 1);
    lean_inc(v_toPure_7018_);
    v_zero_7019_ = lean_unsigned_to_nat(0);
    v_isZero_7020_ = lean_nat_dec_eq(v_i_7015_, v_zero_7019_);
    if v_isZero_7020_ == 1 {
        let mut v___x_7021_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7022_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_7017_);
        lean_dec_ref(v_as_7014_);
        lean_dec(v_f_7013_);
        lean_dec_ref(v_inst_7012_);
        v___x_7021_ = lean_box(0);
        v___x_7022_ = lean_apply_2(v_toPure_7018_, lean_box(0), v___x_7021_);
        return v___x_7022_;
    } else {
        let mut v_one_7023_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_7024_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_7025_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7026_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7027_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7028_: *mut LeanObject = core::ptr::null_mut();
        v_one_7023_ = lean_unsigned_to_nat(1);
        v_n_7024_ = lean_nat_sub(v_i_7015_, v_one_7023_);
        lean_inc(v_n_7024_);
        lean_inc_ref(v_as_7014_);
        lean_inc(v_f_7013_);
        v___f_7025_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed as *mut core::ffi::c_void, 6, 5);
        lean_closure_set(v___f_7025_, 0, v_inst_7012_);
        lean_closure_set(v___f_7025_, 1, v_f_7013_);
        lean_closure_set(v___f_7025_, 2, v_as_7014_);
        lean_closure_set(v___f_7025_, 3, v_n_7024_);
        lean_closure_set(v___f_7025_, 4, v_toPure_7018_);
        v___x_7026_ = lean_array_fget(v_as_7014_, v_n_7024_);
        lean_dec(v_n_7024_);
        lean_dec_ref(v_as_7014_);
        v___x_7027_ = lean_apply_1(v_f_7013_, v___x_7026_);
        v___x_7028_ = lean_apply_4(
            v_toBind_7017_,
            lean_box(0),
            lean_box(0),
            v___x_7027_,
            v___f_7025_,
        );
        return v___x_7028_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(
    mut v_inst_7029_: *mut LeanObject,
    mut v_f_7030_: *mut LeanObject,
    mut v_as_7031_: *mut LeanObject,
    mut v_n_7032_: *mut LeanObject,
    mut v_toPure_7033_: *mut LeanObject,
    mut v_r_7034_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_7034_) == 0 {
        let mut v___x_7035_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_7033_);
        v___x_7035_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(
            v_inst_7029_,
            v_f_7030_,
            v_as_7031_,
            v_n_7032_,
        );
        return v___x_7035_;
    } else {
        let mut v___x_7036_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_as_7031_);
        lean_dec(v_f_7030_);
        lean_dec_ref(v_inst_7029_);
        v___x_7036_ = lean_apply_2(v_toPure_7033_, lean_box(0), v_r_7034_);
        return v___x_7036_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___boxed(
    mut v_inst_7037_: *mut LeanObject,
    mut v_f_7038_: *mut LeanObject,
    mut v_as_7039_: *mut LeanObject,
    mut v_i_7040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7041_: *mut LeanObject = core::ptr::null_mut();
    v_res_7041_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(
        v_inst_7037_,
        v_f_7038_,
        v_as_7039_,
        v_i_7040_,
    );
    lean_dec(v_i_7040_);
    return v_res_7041_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(
    mut v_00_u03b1_7042_: *mut LeanObject,
    mut v_00_u03b2_7043_: *mut LeanObject,
    mut v_m_7044_: *mut LeanObject,
    mut v_inst_7045_: *mut LeanObject,
    mut v_f_7046_: *mut LeanObject,
    mut v_as_7047_: *mut LeanObject,
    mut v_i_7048_: *mut LeanObject,
    mut v_a_7049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7050_: *mut LeanObject = core::ptr::null_mut();
    v___x_7050_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(
        v_inst_7045_,
        v_f_7046_,
        v_as_7047_,
        v_i_7048_,
    );
    return v___x_7050_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___boxed(
    mut v_00_u03b1_7051_: *mut LeanObject,
    mut v_00_u03b2_7052_: *mut LeanObject,
    mut v_m_7053_: *mut LeanObject,
    mut v_inst_7054_: *mut LeanObject,
    mut v_f_7055_: *mut LeanObject,
    mut v_as_7056_: *mut LeanObject,
    mut v_i_7057_: *mut LeanObject,
    mut v_a_7058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7059_: *mut LeanObject = core::ptr::null_mut();
    v_res_7059_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(
        v_00_u03b1_7051_,
        v_00_u03b2_7052_,
        v_m_7053_,
        v_inst_7054_,
        v_f_7055_,
        v_as_7056_,
        v_i_7057_,
        v_a_7058_,
    );
    lean_dec(v_i_7057_);
    return v_res_7059_;
}
pub unsafe fn l_Array_findSomeRevM_x3f___redArg(
    mut v_inst_7060_: *mut LeanObject,
    mut v_f_7061_: *mut LeanObject,
    mut v_as_7062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut LeanObject = core::ptr::null_mut();
    v___x_7063_ = lean_array_get_size(v_as_7062_);
    v___x_7064_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(
        v_inst_7060_,
        v_f_7061_,
        v_as_7062_,
        v___x_7063_,
    );
    return v___x_7064_;
}
pub unsafe fn l_Array_findSomeRevM_x3f(
    mut v_00_u03b1_7065_: *mut LeanObject,
    mut v_00_u03b2_7066_: *mut LeanObject,
    mut v_m_7067_: *mut LeanObject,
    mut v_inst_7068_: *mut LeanObject,
    mut v_f_7069_: *mut LeanObject,
    mut v_as_7070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut LeanObject = core::ptr::null_mut();
    v___x_7071_ = lean_array_get_size(v_as_7070_);
    v___x_7072_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(
        v_inst_7068_,
        v_f_7069_,
        v_as_7070_,
        v___x_7071_,
    );
    return v___x_7072_;
}
pub unsafe fn l_Array_findRevM_x3f___redArg___lam__0(
    mut v_toPure_7073_: *mut LeanObject,
    mut v_a_7074_: *mut LeanObject,
    mut v_____do__lift_7075_: u8,
) -> *mut LeanObject {
    if v_____do__lift_7075_ == 0 {
        let mut v___x_7076_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7077_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_7074_);
        v___x_7076_ = lean_box(0);
        v___x_7077_ = lean_apply_2(v_toPure_7073_, lean_box(0), v___x_7076_);
        return v___x_7077_;
    } else {
        let mut v___x_7078_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7079_: *mut LeanObject = core::ptr::null_mut();
        v___x_7078_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_7078_, 0, v_a_7074_);
        v___x_7079_ = lean_apply_2(v_toPure_7073_, lean_box(0), v___x_7078_);
        return v___x_7079_;
    }
}
pub unsafe fn l_Array_findRevM_x3f___redArg___lam__0___boxed(
    mut v_toPure_7080_: *mut LeanObject,
    mut v_a_7081_: *mut LeanObject,
    mut v_____do__lift_7082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_74__boxed_7083_: u8 = 0;
    let mut v_res_7084_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_74__boxed_7083_ = (lean_unbox(v_____do__lift_7082_) as u8);
    v_res_7084_ = l_Array_findRevM_x3f___redArg___lam__0(
        v_toPure_7080_,
        v_a_7081_,
        v_____do__lift_74__boxed_7083_,
    );
    return v_res_7084_;
}
pub unsafe fn l_Array_findRevM_x3f___redArg___lam__1(
    mut v_toPure_7085_: *mut LeanObject,
    mut v_p_7086_: *mut LeanObject,
    mut v_toBind_7087_: *mut LeanObject,
    mut v_a_7088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_7088_);
    v___f_7089_ = lean_alloc_closure(
        l_Array_findRevM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_7089_, 0, v_toPure_7085_);
    lean_closure_set(v___f_7089_, 1, v_a_7088_);
    v___x_7090_ = lean_apply_1(v_p_7086_, v_a_7088_);
    v___x_7091_ = lean_apply_4(
        v_toBind_7087_,
        lean_box(0),
        lean_box(0),
        v___x_7090_,
        v___f_7089_,
    );
    return v___x_7091_;
}
pub unsafe fn l_Array_findRevM_x3f___redArg(
    mut v_inst_7092_: *mut LeanObject,
    mut v_p_7093_: *mut LeanObject,
    mut v_as_7094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7100_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7095_ = lean_ctor_get(v_inst_7092_, 0);
    v_toBind_7096_ = lean_ctor_get(v_inst_7092_, 1);
    v_toPure_7097_ = lean_ctor_get(v_toApplicative_7095_, 1);
    lean_inc(v_toBind_7096_);
    lean_inc(v_toPure_7097_);
    v___f_7098_ = lean_alloc_closure(
        l_Array_findRevM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_7098_, 0, v_toPure_7097_);
    lean_closure_set(v___f_7098_, 1, v_p_7093_);
    lean_closure_set(v___f_7098_, 2, v_toBind_7096_);
    v___x_7099_ = lean_array_get_size(v_as_7094_);
    v___x_7100_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(
        v_inst_7092_,
        v___f_7098_,
        v_as_7094_,
        v___x_7099_,
    );
    return v___x_7100_;
}
pub unsafe fn l_Array_findRevM_x3f(
    mut v_00_u03b1_7101_: *mut LeanObject,
    mut v_m_7102_: *mut LeanObject,
    mut v_inst_7103_: *mut LeanObject,
    mut v_p_7104_: *mut LeanObject,
    mut v_as_7105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7111_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7106_ = lean_ctor_get(v_inst_7103_, 0);
    v_toBind_7107_ = lean_ctor_get(v_inst_7103_, 1);
    v_toPure_7108_ = lean_ctor_get(v_toApplicative_7106_, 1);
    lean_inc(v_toBind_7107_);
    lean_inc(v_toPure_7108_);
    v___f_7109_ = lean_alloc_closure(
        l_Array_findRevM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_7109_, 0, v_toPure_7108_);
    lean_closure_set(v___f_7109_, 1, v_p_7104_);
    lean_closure_set(v___f_7109_, 2, v_toBind_7107_);
    v___x_7110_ = lean_array_get_size(v_as_7105_);
    v___x_7111_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(
        v_inst_7103_,
        v___f_7109_,
        v_as_7105_,
        v___x_7110_,
    );
    return v___x_7111_;
}
pub unsafe fn l_Array_forM___redArg___lam__0(
    mut v_f_7112_: *mut LeanObject,
    mut v_x_7113_: *mut LeanObject,
    mut v___y_7114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7115_: *mut LeanObject = core::ptr::null_mut();
    v___x_7115_ = lean_apply_1(v_f_7112_, v___y_7114_);
    return v___x_7115_;
}
pub unsafe fn l_Array_forM___redArg(
    mut v_inst_7116_: *mut LeanObject,
    mut v_f_7117_: *mut LeanObject,
    mut v_as_7118_: *mut LeanObject,
    mut v_start_7119_: *mut LeanObject,
    mut v_stop_7120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: u8 = 0;
    v___x_7121_ = lean_box(0);
    v___x_7122_ = lean_nat_dec_lt(v_start_7119_, v_stop_7120_);
    if v___x_7122_ == 0 {
        let mut v_toApplicative_7123_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_7124_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7125_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_as_7118_);
        lean_dec(v_f_7117_);
        v_toApplicative_7123_ = lean_ctor_get(v_inst_7116_, 0);
        lean_inc_ref(v_toApplicative_7123_);
        lean_dec_ref(v_inst_7116_);
        v_toPure_7124_ = lean_ctor_get(v_toApplicative_7123_, 1);
        lean_inc(v_toPure_7124_);
        lean_dec_ref(v_toApplicative_7123_);
        v___x_7125_ = lean_apply_2(v_toPure_7124_, lean_box(0), v___x_7121_);
        return v___x_7125_;
    } else {
        let mut v___f_7126_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7127_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7128_: u8 = 0;
        v___f_7126_ = lean_alloc_closure(
            l_Array_forM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_7126_, 0, v_f_7117_);
        v___x_7127_ = lean_array_get_size(v_as_7118_);
        v___x_7128_ = lean_nat_dec_le(v_stop_7120_, v___x_7127_);
        if v___x_7128_ == 0 {
            let mut v___x_7129_: u8 = 0;
            v___x_7129_ = lean_nat_dec_lt(v_start_7119_, v___x_7127_);
            if v___x_7129_ == 0 {
                let mut v_toApplicative_7130_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_7131_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7132_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_7126_);
                lean_dec_ref(v_as_7118_);
                v_toApplicative_7130_ = lean_ctor_get(v_inst_7116_, 0);
                lean_inc_ref(v_toApplicative_7130_);
                lean_dec_ref(v_inst_7116_);
                v_toPure_7131_ = lean_ctor_get(v_toApplicative_7130_, 1);
                lean_inc(v_toPure_7131_);
                lean_dec_ref(v_toApplicative_7130_);
                v___x_7132_ = lean_apply_2(v_toPure_7131_, lean_box(0), v___x_7121_);
                return v___x_7132_;
            } else {
                let mut v___x_7133_: usize = 0;
                let mut v___x_7134_: usize = 0;
                let mut v___x_7135_: *mut LeanObject = core::ptr::null_mut();
                v___x_7133_ = lean_usize_of_nat(v_start_7119_);
                v___x_7134_ = lean_usize_of_nat(v___x_7127_);
                v___x_7135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v_inst_7116_,
                    v___f_7126_,
                    v_as_7118_,
                    v___x_7133_,
                    v___x_7134_,
                    v___x_7121_,
                );
                return v___x_7135_;
            }
        } else {
            let mut v___x_7136_: usize = 0;
            let mut v___x_7137_: usize = 0;
            let mut v___x_7138_: *mut LeanObject = core::ptr::null_mut();
            v___x_7136_ = lean_usize_of_nat(v_start_7119_);
            v___x_7137_ = lean_usize_of_nat(v_stop_7120_);
            v___x_7138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v_inst_7116_,
                v___f_7126_,
                v_as_7118_,
                v___x_7136_,
                v___x_7137_,
                v___x_7121_,
            );
            return v___x_7138_;
        }
    }
}
pub unsafe fn l_Array_forM___redArg___boxed(
    mut v_inst_7139_: *mut LeanObject,
    mut v_f_7140_: *mut LeanObject,
    mut v_as_7141_: *mut LeanObject,
    mut v_start_7142_: *mut LeanObject,
    mut v_stop_7143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7144_: *mut LeanObject = core::ptr::null_mut();
    v_res_7144_ = l_Array_forM___redArg(
        v_inst_7139_,
        v_f_7140_,
        v_as_7141_,
        v_start_7142_,
        v_stop_7143_,
    );
    lean_dec(v_stop_7143_);
    lean_dec(v_start_7142_);
    return v_res_7144_;
}
pub unsafe fn l_Array_forM(
    mut v_00_u03b1_7145_: *mut LeanObject,
    mut v_m_7146_: *mut LeanObject,
    mut v_inst_7147_: *mut LeanObject,
    mut v_f_7148_: *mut LeanObject,
    mut v_as_7149_: *mut LeanObject,
    mut v_start_7150_: *mut LeanObject,
    mut v_stop_7151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7153_: u8 = 0;
    v___x_7152_ = lean_box(0);
    v___x_7153_ = lean_nat_dec_lt(v_start_7150_, v_stop_7151_);
    if v___x_7153_ == 0 {
        let mut v_toApplicative_7154_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_7155_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7156_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_as_7149_);
        lean_dec(v_f_7148_);
        v_toApplicative_7154_ = lean_ctor_get(v_inst_7147_, 0);
        lean_inc_ref(v_toApplicative_7154_);
        lean_dec_ref(v_inst_7147_);
        v_toPure_7155_ = lean_ctor_get(v_toApplicative_7154_, 1);
        lean_inc(v_toPure_7155_);
        lean_dec_ref(v_toApplicative_7154_);
        v___x_7156_ = lean_apply_2(v_toPure_7155_, lean_box(0), v___x_7152_);
        return v___x_7156_;
    } else {
        let mut v___f_7157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7158_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7159_: u8 = 0;
        v___f_7157_ = lean_alloc_closure(
            l_Array_forM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_7157_, 0, v_f_7148_);
        v___x_7158_ = lean_array_get_size(v_as_7149_);
        v___x_7159_ = lean_nat_dec_le(v_stop_7151_, v___x_7158_);
        if v___x_7159_ == 0 {
            let mut v___x_7160_: u8 = 0;
            v___x_7160_ = lean_nat_dec_lt(v_start_7150_, v___x_7158_);
            if v___x_7160_ == 0 {
                let mut v_toApplicative_7161_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_7162_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7163_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_7157_);
                lean_dec_ref(v_as_7149_);
                v_toApplicative_7161_ = lean_ctor_get(v_inst_7147_, 0);
                lean_inc_ref(v_toApplicative_7161_);
                lean_dec_ref(v_inst_7147_);
                v_toPure_7162_ = lean_ctor_get(v_toApplicative_7161_, 1);
                lean_inc(v_toPure_7162_);
                lean_dec_ref(v_toApplicative_7161_);
                v___x_7163_ = lean_apply_2(v_toPure_7162_, lean_box(0), v___x_7152_);
                return v___x_7163_;
            } else {
                let mut v___x_7164_: usize = 0;
                let mut v___x_7165_: usize = 0;
                let mut v___x_7166_: *mut LeanObject = core::ptr::null_mut();
                v___x_7164_ = lean_usize_of_nat(v_start_7150_);
                v___x_7165_ = lean_usize_of_nat(v___x_7158_);
                v___x_7166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v_inst_7147_,
                    v___f_7157_,
                    v_as_7149_,
                    v___x_7164_,
                    v___x_7165_,
                    v___x_7152_,
                );
                return v___x_7166_;
            }
        } else {
            let mut v___x_7167_: usize = 0;
            let mut v___x_7168_: usize = 0;
            let mut v___x_7169_: *mut LeanObject = core::ptr::null_mut();
            v___x_7167_ = lean_usize_of_nat(v_start_7150_);
            v___x_7168_ = lean_usize_of_nat(v_stop_7151_);
            v___x_7169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v_inst_7147_,
                v___f_7157_,
                v_as_7149_,
                v___x_7167_,
                v___x_7168_,
                v___x_7152_,
            );
            return v___x_7169_;
        }
    }
}
pub unsafe fn l_Array_forM___boxed(
    mut v_00_u03b1_7170_: *mut LeanObject,
    mut v_m_7171_: *mut LeanObject,
    mut v_inst_7172_: *mut LeanObject,
    mut v_f_7173_: *mut LeanObject,
    mut v_as_7174_: *mut LeanObject,
    mut v_start_7175_: *mut LeanObject,
    mut v_stop_7176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7177_: *mut LeanObject = core::ptr::null_mut();
    v_res_7177_ = l_Array_forM(
        v_00_u03b1_7170_,
        v_m_7171_,
        v_inst_7172_,
        v_f_7173_,
        v_as_7174_,
        v_start_7175_,
        v_stop_7176_,
    );
    lean_dec(v_stop_7176_);
    lean_dec(v_start_7175_);
    return v_res_7177_;
}
pub unsafe fn l_Array_instForMOfMonad___redArg___lam__1(
    mut v_inst_7178_: *mut LeanObject,
    mut v_xs_7179_: *mut LeanObject,
    mut v_f_7180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7184_: u8 = 0;
    v___x_7181_ = lean_unsigned_to_nat(0);
    v___x_7182_ = lean_array_get_size(v_xs_7179_);
    v___x_7183_ = lean_box(0);
    v___x_7184_ = lean_nat_dec_lt(v___x_7181_, v___x_7182_);
    if v___x_7184_ == 0 {
        let mut v_toApplicative_7185_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_7186_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7187_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_7180_);
        lean_dec_ref(v_xs_7179_);
        v_toApplicative_7185_ = lean_ctor_get(v_inst_7178_, 0);
        lean_inc_ref(v_toApplicative_7185_);
        lean_dec_ref(v_inst_7178_);
        v_toPure_7186_ = lean_ctor_get(v_toApplicative_7185_, 1);
        lean_inc(v_toPure_7186_);
        lean_dec_ref(v_toApplicative_7185_);
        v___x_7187_ = lean_apply_2(v_toPure_7186_, lean_box(0), v___x_7183_);
        return v___x_7187_;
    } else {
        let mut v___f_7188_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7189_: u8 = 0;
        v___f_7188_ = lean_alloc_closure(
            l_Array_forM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_7188_, 0, v_f_7180_);
        v___x_7189_ = lean_nat_dec_le(v___x_7182_, v___x_7182_);
        if v___x_7189_ == 0 {
            if v___x_7184_ == 0 {
                let mut v_toApplicative_7190_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_7191_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7192_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_7188_);
                lean_dec_ref(v_xs_7179_);
                v_toApplicative_7190_ = lean_ctor_get(v_inst_7178_, 0);
                lean_inc_ref(v_toApplicative_7190_);
                lean_dec_ref(v_inst_7178_);
                v_toPure_7191_ = lean_ctor_get(v_toApplicative_7190_, 1);
                lean_inc(v_toPure_7191_);
                lean_dec_ref(v_toApplicative_7190_);
                v___x_7192_ = lean_apply_2(v_toPure_7191_, lean_box(0), v___x_7183_);
                return v___x_7192_;
            } else {
                let mut v___x_7193_: usize = 0;
                let mut v___x_7194_: usize = 0;
                let mut v___x_7195_: *mut LeanObject = core::ptr::null_mut();
                v___x_7193_ = 0usize;
                v___x_7194_ = lean_usize_of_nat(v___x_7182_);
                v___x_7195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v_inst_7178_,
                    v___f_7188_,
                    v_xs_7179_,
                    v___x_7193_,
                    v___x_7194_,
                    v___x_7183_,
                );
                return v___x_7195_;
            }
        } else {
            let mut v___x_7196_: usize = 0;
            let mut v___x_7197_: usize = 0;
            let mut v___x_7198_: *mut LeanObject = core::ptr::null_mut();
            v___x_7196_ = 0usize;
            v___x_7197_ = lean_usize_of_nat(v___x_7182_);
            v___x_7198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v_inst_7178_,
                v___f_7188_,
                v_xs_7179_,
                v___x_7196_,
                v___x_7197_,
                v___x_7183_,
            );
            return v___x_7198_;
        }
    }
}
pub unsafe fn l_Array_instForMOfMonad___redArg(
    mut v_inst_7199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7200_: *mut LeanObject = core::ptr::null_mut();
    v___f_7200_ = lean_alloc_closure(
        l_Array_instForMOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7200_, 0, v_inst_7199_);
    return v___f_7200_;
}
pub unsafe fn l_Array_instForMOfMonad(
    mut v_00_u03b1_7201_: *mut LeanObject,
    mut v_m_7202_: *mut LeanObject,
    mut v_inst_7203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7204_: *mut LeanObject = core::ptr::null_mut();
    v___f_7204_ = lean_alloc_closure(
        l_Array_instForMOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7204_, 0, v_inst_7203_);
    return v___f_7204_;
}
pub unsafe fn l_Array_forRevM___redArg___lam__0(
    mut v_f_7205_: *mut LeanObject,
    mut v_a_7206_: *mut LeanObject,
    mut v_x_7207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7208_: *mut LeanObject = core::ptr::null_mut();
    v___x_7208_ = lean_apply_1(v_f_7205_, v_a_7206_);
    return v___x_7208_;
}
pub unsafe fn l_Array_forRevM___redArg(
    mut v_inst_7209_: *mut LeanObject,
    mut v_f_7210_: *mut LeanObject,
    mut v_as_7211_: *mut LeanObject,
    mut v_start_7212_: *mut LeanObject,
    mut v_stop_7213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7217_: u8 = 0;
    v___f_7214_ = lean_alloc_closure(
        l_Array_forRevM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7214_, 0, v_f_7210_);
    v___x_7215_ = lean_box(0);
    v___x_7216_ = lean_array_get_size(v_as_7211_);
    v___x_7217_ = lean_nat_dec_le(v_start_7212_, v___x_7216_);
    if v___x_7217_ == 0 {
        let mut v___x_7218_: u8 = 0;
        v___x_7218_ = lean_nat_dec_lt(v_stop_7213_, v___x_7216_);
        if v___x_7218_ == 0 {
            let mut v_toApplicative_7219_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_7220_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7221_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___f_7214_);
            lean_dec_ref(v_as_7211_);
            v_toApplicative_7219_ = lean_ctor_get(v_inst_7209_, 0);
            lean_inc_ref(v_toApplicative_7219_);
            lean_dec_ref(v_inst_7209_);
            v_toPure_7220_ = lean_ctor_get(v_toApplicative_7219_, 1);
            lean_inc(v_toPure_7220_);
            lean_dec_ref(v_toApplicative_7219_);
            v___x_7221_ = lean_apply_2(v_toPure_7220_, lean_box(0), v___x_7215_);
            return v___x_7221_;
        } else {
            let mut v___x_7222_: usize = 0;
            let mut v___x_7223_: usize = 0;
            let mut v___x_7224_: *mut LeanObject = core::ptr::null_mut();
            v___x_7222_ = lean_usize_of_nat(v___x_7216_);
            v___x_7223_ = lean_usize_of_nat(v_stop_7213_);
            v___x_7224_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
                v_inst_7209_,
                v___f_7214_,
                v_as_7211_,
                v___x_7222_,
                v___x_7223_,
                v___x_7215_,
            );
            return v___x_7224_;
        }
    } else {
        let mut v___x_7225_: u8 = 0;
        v___x_7225_ = lean_nat_dec_lt(v_stop_7213_, v_start_7212_);
        if v___x_7225_ == 0 {
            let mut v_toApplicative_7226_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_7227_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7228_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___f_7214_);
            lean_dec_ref(v_as_7211_);
            v_toApplicative_7226_ = lean_ctor_get(v_inst_7209_, 0);
            lean_inc_ref(v_toApplicative_7226_);
            lean_dec_ref(v_inst_7209_);
            v_toPure_7227_ = lean_ctor_get(v_toApplicative_7226_, 1);
            lean_inc(v_toPure_7227_);
            lean_dec_ref(v_toApplicative_7226_);
            v___x_7228_ = lean_apply_2(v_toPure_7227_, lean_box(0), v___x_7215_);
            return v___x_7228_;
        } else {
            let mut v___x_7229_: usize = 0;
            let mut v___x_7230_: usize = 0;
            let mut v___x_7231_: *mut LeanObject = core::ptr::null_mut();
            v___x_7229_ = lean_usize_of_nat(v_start_7212_);
            v___x_7230_ = lean_usize_of_nat(v_stop_7213_);
            v___x_7231_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
                v_inst_7209_,
                v___f_7214_,
                v_as_7211_,
                v___x_7229_,
                v___x_7230_,
                v___x_7215_,
            );
            return v___x_7231_;
        }
    }
}
pub unsafe fn l_Array_forRevM___redArg___boxed(
    mut v_inst_7232_: *mut LeanObject,
    mut v_f_7233_: *mut LeanObject,
    mut v_as_7234_: *mut LeanObject,
    mut v_start_7235_: *mut LeanObject,
    mut v_stop_7236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7237_: *mut LeanObject = core::ptr::null_mut();
    v_res_7237_ = l_Array_forRevM___redArg(
        v_inst_7232_,
        v_f_7233_,
        v_as_7234_,
        v_start_7235_,
        v_stop_7236_,
    );
    lean_dec(v_stop_7236_);
    lean_dec(v_start_7235_);
    return v_res_7237_;
}
pub unsafe fn l_Array_forRevM(
    mut v_00_u03b1_7238_: *mut LeanObject,
    mut v_m_7239_: *mut LeanObject,
    mut v_inst_7240_: *mut LeanObject,
    mut v_f_7241_: *mut LeanObject,
    mut v_as_7242_: *mut LeanObject,
    mut v_start_7243_: *mut LeanObject,
    mut v_stop_7244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7248_: u8 = 0;
    v___f_7245_ = lean_alloc_closure(
        l_Array_forRevM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7245_, 0, v_f_7241_);
    v___x_7246_ = lean_box(0);
    v___x_7247_ = lean_array_get_size(v_as_7242_);
    v___x_7248_ = lean_nat_dec_le(v_start_7243_, v___x_7247_);
    if v___x_7248_ == 0 {
        let mut v___x_7249_: u8 = 0;
        v___x_7249_ = lean_nat_dec_lt(v_stop_7244_, v___x_7247_);
        if v___x_7249_ == 0 {
            let mut v_toApplicative_7250_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_7251_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7252_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___f_7245_);
            lean_dec_ref(v_as_7242_);
            v_toApplicative_7250_ = lean_ctor_get(v_inst_7240_, 0);
            lean_inc_ref(v_toApplicative_7250_);
            lean_dec_ref(v_inst_7240_);
            v_toPure_7251_ = lean_ctor_get(v_toApplicative_7250_, 1);
            lean_inc(v_toPure_7251_);
            lean_dec_ref(v_toApplicative_7250_);
            v___x_7252_ = lean_apply_2(v_toPure_7251_, lean_box(0), v___x_7246_);
            return v___x_7252_;
        } else {
            let mut v___x_7253_: usize = 0;
            let mut v___x_7254_: usize = 0;
            let mut v___x_7255_: *mut LeanObject = core::ptr::null_mut();
            v___x_7253_ = lean_usize_of_nat(v___x_7247_);
            v___x_7254_ = lean_usize_of_nat(v_stop_7244_);
            v___x_7255_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
                v_inst_7240_,
                v___f_7245_,
                v_as_7242_,
                v___x_7253_,
                v___x_7254_,
                v___x_7246_,
            );
            return v___x_7255_;
        }
    } else {
        let mut v___x_7256_: u8 = 0;
        v___x_7256_ = lean_nat_dec_lt(v_stop_7244_, v_start_7243_);
        if v___x_7256_ == 0 {
            let mut v_toApplicative_7257_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_7258_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7259_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___f_7245_);
            lean_dec_ref(v_as_7242_);
            v_toApplicative_7257_ = lean_ctor_get(v_inst_7240_, 0);
            lean_inc_ref(v_toApplicative_7257_);
            lean_dec_ref(v_inst_7240_);
            v_toPure_7258_ = lean_ctor_get(v_toApplicative_7257_, 1);
            lean_inc(v_toPure_7258_);
            lean_dec_ref(v_toApplicative_7257_);
            v___x_7259_ = lean_apply_2(v_toPure_7258_, lean_box(0), v___x_7246_);
            return v___x_7259_;
        } else {
            let mut v___x_7260_: usize = 0;
            let mut v___x_7261_: usize = 0;
            let mut v___x_7262_: *mut LeanObject = core::ptr::null_mut();
            v___x_7260_ = lean_usize_of_nat(v_start_7243_);
            v___x_7261_ = lean_usize_of_nat(v_stop_7244_);
            v___x_7262_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
                v_inst_7240_,
                v___f_7245_,
                v_as_7242_,
                v___x_7260_,
                v___x_7261_,
                v___x_7246_,
            );
            return v___x_7262_;
        }
    }
}
pub unsafe fn l_Array_forRevM___boxed(
    mut v_00_u03b1_7263_: *mut LeanObject,
    mut v_m_7264_: *mut LeanObject,
    mut v_inst_7265_: *mut LeanObject,
    mut v_f_7266_: *mut LeanObject,
    mut v_as_7267_: *mut LeanObject,
    mut v_start_7268_: *mut LeanObject,
    mut v_stop_7269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7270_: *mut LeanObject = core::ptr::null_mut();
    v_res_7270_ = l_Array_forRevM(
        v_00_u03b1_7263_,
        v_m_7264_,
        v_inst_7265_,
        v_f_7266_,
        v_as_7267_,
        v_start_7268_,
        v_stop_7269_,
    );
    lean_dec(v_stop_7269_);
    lean_dec(v_start_7268_);
    return v_res_7270_;
}
pub unsafe fn l_Array_foldl___redArg___lam__0(
    mut v_f_7271_: *mut LeanObject,
    mut v_x1_7272_: *mut LeanObject,
    mut v_x2_7273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7274_: *mut LeanObject = core::ptr::null_mut();
    v___x_7274_ = lean_apply_2(v_f_7271_, v_x1_7272_, v_x2_7273_);
    return v___x_7274_;
}
pub unsafe fn l_Array_foldl___redArg(
    mut v_f_7294_: *mut LeanObject,
    mut v_init_7295_: *mut LeanObject,
    mut v_as_7296_: *mut LeanObject,
    mut v_start_7297_: *mut LeanObject,
    mut v_stop_7298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7300_: u8 = 0;
    v___x_7299_ = l_Array_foldl___redArg___closed__9;
    v___x_7300_ = lean_nat_dec_lt(v_start_7297_, v_stop_7298_);
    if v___x_7300_ == 0 {
        lean_dec_ref(v_as_7296_);
        lean_dec(v_f_7294_);
        return v_init_7295_;
    } else {
        let mut v___f_7301_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7302_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7303_: u8 = 0;
        v___f_7301_ = lean_alloc_closure(
            l_Array_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_7301_, 0, v_f_7294_);
        v___x_7302_ = lean_array_get_size(v_as_7296_);
        v___x_7303_ = lean_nat_dec_le(v_stop_7298_, v___x_7302_);
        if v___x_7303_ == 0 {
            let mut v___x_7304_: u8 = 0;
            v___x_7304_ = lean_nat_dec_lt(v_start_7297_, v___x_7302_);
            if v___x_7304_ == 0 {
                lean_dec_ref(v___f_7301_);
                lean_dec_ref(v_as_7296_);
                return v_init_7295_;
            } else {
                let mut v___x_7305_: usize = 0;
                let mut v___x_7306_: usize = 0;
                let mut v___x_7307_: *mut LeanObject = core::ptr::null_mut();
                v___x_7305_ = lean_usize_of_nat(v_start_7297_);
                v___x_7306_ = lean_usize_of_nat(v___x_7302_);
                v___x_7307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v___x_7299_,
                    v___f_7301_,
                    v_as_7296_,
                    v___x_7305_,
                    v___x_7306_,
                    v_init_7295_,
                );
                return v___x_7307_;
            }
        } else {
            let mut v___x_7308_: usize = 0;
            let mut v___x_7309_: usize = 0;
            let mut v___x_7310_: *mut LeanObject = core::ptr::null_mut();
            v___x_7308_ = lean_usize_of_nat(v_start_7297_);
            v___x_7309_ = lean_usize_of_nat(v_stop_7298_);
            v___x_7310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v___x_7299_,
                v___f_7301_,
                v_as_7296_,
                v___x_7308_,
                v___x_7309_,
                v_init_7295_,
            );
            return v___x_7310_;
        }
    }
}
pub unsafe fn l_Array_foldl___redArg___boxed(
    mut v_f_7311_: *mut LeanObject,
    mut v_init_7312_: *mut LeanObject,
    mut v_as_7313_: *mut LeanObject,
    mut v_start_7314_: *mut LeanObject,
    mut v_stop_7315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7316_: *mut LeanObject = core::ptr::null_mut();
    v_res_7316_ = l_Array_foldl___redArg(
        v_f_7311_,
        v_init_7312_,
        v_as_7313_,
        v_start_7314_,
        v_stop_7315_,
    );
    lean_dec(v_stop_7315_);
    lean_dec(v_start_7314_);
    return v_res_7316_;
}
pub unsafe fn l_Array_foldl(
    mut v_00_u03b1_7317_: *mut LeanObject,
    mut v_00_u03b2_7318_: *mut LeanObject,
    mut v_f_7319_: *mut LeanObject,
    mut v_init_7320_: *mut LeanObject,
    mut v_as_7321_: *mut LeanObject,
    mut v_start_7322_: *mut LeanObject,
    mut v_stop_7323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7325_: u8 = 0;
    v___x_7324_ = l_Array_foldl___redArg___closed__9;
    v___x_7325_ = lean_nat_dec_lt(v_start_7322_, v_stop_7323_);
    if v___x_7325_ == 0 {
        lean_dec_ref(v_as_7321_);
        lean_dec(v_f_7319_);
        return v_init_7320_;
    } else {
        let mut v___f_7326_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7327_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7328_: u8 = 0;
        v___f_7326_ = lean_alloc_closure(
            l_Array_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_7326_, 0, v_f_7319_);
        v___x_7327_ = lean_array_get_size(v_as_7321_);
        v___x_7328_ = lean_nat_dec_le(v_stop_7323_, v___x_7327_);
        if v___x_7328_ == 0 {
            let mut v___x_7329_: u8 = 0;
            v___x_7329_ = lean_nat_dec_lt(v_start_7322_, v___x_7327_);
            if v___x_7329_ == 0 {
                lean_dec_ref(v___f_7326_);
                lean_dec_ref(v_as_7321_);
                return v_init_7320_;
            } else {
                let mut v___x_7330_: usize = 0;
                let mut v___x_7331_: usize = 0;
                let mut v___x_7332_: *mut LeanObject = core::ptr::null_mut();
                v___x_7330_ = lean_usize_of_nat(v_start_7322_);
                v___x_7331_ = lean_usize_of_nat(v___x_7327_);
                v___x_7332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v___x_7324_,
                    v___f_7326_,
                    v_as_7321_,
                    v___x_7330_,
                    v___x_7331_,
                    v_init_7320_,
                );
                return v___x_7332_;
            }
        } else {
            let mut v___x_7333_: usize = 0;
            let mut v___x_7334_: usize = 0;
            let mut v___x_7335_: *mut LeanObject = core::ptr::null_mut();
            v___x_7333_ = lean_usize_of_nat(v_start_7322_);
            v___x_7334_ = lean_usize_of_nat(v_stop_7323_);
            v___x_7335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v___x_7324_,
                v___f_7326_,
                v_as_7321_,
                v___x_7333_,
                v___x_7334_,
                v_init_7320_,
            );
            return v___x_7335_;
        }
    }
}
pub unsafe fn l_Array_foldl___boxed(
    mut v_00_u03b1_7336_: *mut LeanObject,
    mut v_00_u03b2_7337_: *mut LeanObject,
    mut v_f_7338_: *mut LeanObject,
    mut v_init_7339_: *mut LeanObject,
    mut v_as_7340_: *mut LeanObject,
    mut v_start_7341_: *mut LeanObject,
    mut v_stop_7342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7343_: *mut LeanObject = core::ptr::null_mut();
    v_res_7343_ = l_Array_foldl(
        v_00_u03b1_7336_,
        v_00_u03b2_7337_,
        v_f_7338_,
        v_init_7339_,
        v_as_7340_,
        v_start_7341_,
        v_stop_7342_,
    );
    lean_dec(v_stop_7342_);
    lean_dec(v_start_7341_);
    return v_res_7343_;
}
pub unsafe fn l_Array_foldr___redArg(
    mut v_f_7344_: *mut LeanObject,
    mut v_init_7345_: *mut LeanObject,
    mut v_as_7346_: *mut LeanObject,
    mut v_start_7347_: *mut LeanObject,
    mut v_stop_7348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7352_: u8 = 0;
    v___f_7349_ = lean_alloc_closure(
        l_Array_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7349_, 0, v_f_7344_);
    v___x_7350_ = l_Array_foldl___redArg___closed__9;
    v___x_7351_ = lean_array_get_size(v_as_7346_);
    v___x_7352_ = lean_nat_dec_le(v_start_7347_, v___x_7351_);
    if v___x_7352_ == 0 {
        let mut v___x_7353_: u8 = 0;
        v___x_7353_ = lean_nat_dec_lt(v_stop_7348_, v___x_7351_);
        if v___x_7353_ == 0 {
            lean_dec_ref(v___f_7349_);
            lean_dec_ref(v_as_7346_);
            return v_init_7345_;
        } else {
            let mut v___x_7354_: usize = 0;
            let mut v___x_7355_: usize = 0;
            let mut v___x_7356_: *mut LeanObject = core::ptr::null_mut();
            v___x_7354_ = lean_usize_of_nat(v___x_7351_);
            v___x_7355_ = lean_usize_of_nat(v_stop_7348_);
            v___x_7356_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
                v___x_7350_,
                v___f_7349_,
                v_as_7346_,
                v___x_7354_,
                v___x_7355_,
                v_init_7345_,
            );
            return v___x_7356_;
        }
    } else {
        let mut v___x_7357_: u8 = 0;
        v___x_7357_ = lean_nat_dec_lt(v_stop_7348_, v_start_7347_);
        if v___x_7357_ == 0 {
            lean_dec_ref(v___f_7349_);
            lean_dec_ref(v_as_7346_);
            return v_init_7345_;
        } else {
            let mut v___x_7358_: usize = 0;
            let mut v___x_7359_: usize = 0;
            let mut v___x_7360_: *mut LeanObject = core::ptr::null_mut();
            v___x_7358_ = lean_usize_of_nat(v_start_7347_);
            v___x_7359_ = lean_usize_of_nat(v_stop_7348_);
            v___x_7360_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
                v___x_7350_,
                v___f_7349_,
                v_as_7346_,
                v___x_7358_,
                v___x_7359_,
                v_init_7345_,
            );
            return v___x_7360_;
        }
    }
}
pub unsafe fn l_Array_foldr___redArg___boxed(
    mut v_f_7361_: *mut LeanObject,
    mut v_init_7362_: *mut LeanObject,
    mut v_as_7363_: *mut LeanObject,
    mut v_start_7364_: *mut LeanObject,
    mut v_stop_7365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7366_: *mut LeanObject = core::ptr::null_mut();
    v_res_7366_ = l_Array_foldr___redArg(
        v_f_7361_,
        v_init_7362_,
        v_as_7363_,
        v_start_7364_,
        v_stop_7365_,
    );
    lean_dec(v_stop_7365_);
    lean_dec(v_start_7364_);
    return v_res_7366_;
}
pub unsafe fn l_Array_foldr(
    mut v_00_u03b1_7367_: *mut LeanObject,
    mut v_00_u03b2_7368_: *mut LeanObject,
    mut v_f_7369_: *mut LeanObject,
    mut v_init_7370_: *mut LeanObject,
    mut v_as_7371_: *mut LeanObject,
    mut v_start_7372_: *mut LeanObject,
    mut v_stop_7373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7377_: u8 = 0;
    v___f_7374_ = lean_alloc_closure(
        l_Array_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7374_, 0, v_f_7369_);
    v___x_7375_ = l_Array_foldl___redArg___closed__9;
    v___x_7376_ = lean_array_get_size(v_as_7371_);
    v___x_7377_ = lean_nat_dec_le(v_start_7372_, v___x_7376_);
    if v___x_7377_ == 0 {
        let mut v___x_7378_: u8 = 0;
        v___x_7378_ = lean_nat_dec_lt(v_stop_7373_, v___x_7376_);
        if v___x_7378_ == 0 {
            lean_dec_ref(v___f_7374_);
            lean_dec_ref(v_as_7371_);
            return v_init_7370_;
        } else {
            let mut v___x_7379_: usize = 0;
            let mut v___x_7380_: usize = 0;
            let mut v___x_7381_: *mut LeanObject = core::ptr::null_mut();
            v___x_7379_ = lean_usize_of_nat(v___x_7376_);
            v___x_7380_ = lean_usize_of_nat(v_stop_7373_);
            v___x_7381_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
                v___x_7375_,
                v___f_7374_,
                v_as_7371_,
                v___x_7379_,
                v___x_7380_,
                v_init_7370_,
            );
            return v___x_7381_;
        }
    } else {
        let mut v___x_7382_: u8 = 0;
        v___x_7382_ = lean_nat_dec_lt(v_stop_7373_, v_start_7372_);
        if v___x_7382_ == 0 {
            lean_dec_ref(v___f_7374_);
            lean_dec_ref(v_as_7371_);
            return v_init_7370_;
        } else {
            let mut v___x_7383_: usize = 0;
            let mut v___x_7384_: usize = 0;
            let mut v___x_7385_: *mut LeanObject = core::ptr::null_mut();
            v___x_7383_ = lean_usize_of_nat(v_start_7372_);
            v___x_7384_ = lean_usize_of_nat(v_stop_7373_);
            v___x_7385_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
                v___x_7375_,
                v___f_7374_,
                v_as_7371_,
                v___x_7383_,
                v___x_7384_,
                v_init_7370_,
            );
            return v___x_7385_;
        }
    }
}
pub unsafe fn l_Array_foldr___boxed(
    mut v_00_u03b1_7386_: *mut LeanObject,
    mut v_00_u03b2_7387_: *mut LeanObject,
    mut v_f_7388_: *mut LeanObject,
    mut v_init_7389_: *mut LeanObject,
    mut v_as_7390_: *mut LeanObject,
    mut v_start_7391_: *mut LeanObject,
    mut v_stop_7392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7393_: *mut LeanObject = core::ptr::null_mut();
    v_res_7393_ = l_Array_foldr(
        v_00_u03b1_7386_,
        v_00_u03b2_7387_,
        v_f_7388_,
        v_init_7389_,
        v_as_7390_,
        v_start_7391_,
        v_stop_7392_,
    );
    lean_dec(v_stop_7392_);
    lean_dec(v_start_7391_);
    return v_res_7393_;
}
pub unsafe fn l_Array_sum___redArg___lam__0(
    mut v_inst_7394_: *mut LeanObject,
    mut v_x1_7395_: *mut LeanObject,
    mut v_x2_7396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7397_: *mut LeanObject = core::ptr::null_mut();
    v___x_7397_ = lean_apply_2(v_inst_7394_, v_x1_7395_, v_x2_7396_);
    return v___x_7397_;
}
pub unsafe fn l_Array_sum___redArg(
    mut v_inst_7398_: *mut LeanObject,
    mut v_inst_7399_: *mut LeanObject,
    mut v_as_7400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7404_: u8 = 0;
    v___x_7401_ = lean_array_get_size(v_as_7400_);
    v___x_7402_ = lean_unsigned_to_nat(0);
    v___x_7403_ = l_Array_foldl___redArg___closed__9;
    v___x_7404_ = lean_nat_dec_lt(v___x_7402_, v___x_7401_);
    if v___x_7404_ == 0 {
        lean_dec_ref(v_as_7400_);
        lean_dec(v_inst_7398_);
        return v_inst_7399_;
    } else {
        let mut v___f_7405_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7406_: usize = 0;
        let mut v___x_7407_: usize = 0;
        let mut v___x_7408_: *mut LeanObject = core::ptr::null_mut();
        v___f_7405_ = lean_alloc_closure(
            l_Array_sum___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_7405_, 0, v_inst_7398_);
        v___x_7406_ = lean_usize_of_nat(v___x_7401_);
        v___x_7407_ = 0usize;
        v___x_7408_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
            v___x_7403_,
            v___f_7405_,
            v_as_7400_,
            v___x_7406_,
            v___x_7407_,
            v_inst_7399_,
        );
        return v___x_7408_;
    }
}
pub unsafe fn l_Array_sum(
    mut v_00_u03b1_7409_: *mut LeanObject,
    mut v_inst_7410_: *mut LeanObject,
    mut v_inst_7411_: *mut LeanObject,
    mut v_as_7412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7416_: u8 = 0;
    v___x_7413_ = lean_array_get_size(v_as_7412_);
    v___x_7414_ = lean_unsigned_to_nat(0);
    v___x_7415_ = l_Array_foldl___redArg___closed__9;
    v___x_7416_ = lean_nat_dec_lt(v___x_7414_, v___x_7413_);
    if v___x_7416_ == 0 {
        lean_dec_ref(v_as_7412_);
        lean_dec(v_inst_7410_);
        return v_inst_7411_;
    } else {
        let mut v___f_7417_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7418_: usize = 0;
        let mut v___x_7419_: usize = 0;
        let mut v___x_7420_: *mut LeanObject = core::ptr::null_mut();
        v___f_7417_ = lean_alloc_closure(
            l_Array_sum___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_7417_, 0, v_inst_7410_);
        v___x_7418_ = lean_usize_of_nat(v___x_7413_);
        v___x_7419_ = 0usize;
        v___x_7420_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
            v___x_7415_,
            v___f_7417_,
            v_as_7412_,
            v___x_7418_,
            v___x_7419_,
            v_inst_7411_,
        );
        return v___x_7420_;
    }
}
pub unsafe fn l_Array_prod___redArg(
    mut v_inst_7421_: *mut LeanObject,
    mut v_inst_7422_: *mut LeanObject,
    mut v_as_7423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7427_: u8 = 0;
    v___x_7424_ = lean_array_get_size(v_as_7423_);
    v___x_7425_ = lean_unsigned_to_nat(0);
    v___x_7426_ = l_Array_foldl___redArg___closed__9;
    v___x_7427_ = lean_nat_dec_lt(v___x_7425_, v___x_7424_);
    if v___x_7427_ == 0 {
        lean_dec_ref(v_as_7423_);
        lean_dec(v_inst_7421_);
        return v_inst_7422_;
    } else {
        let mut v___f_7428_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7429_: usize = 0;
        let mut v___x_7430_: usize = 0;
        let mut v___x_7431_: *mut LeanObject = core::ptr::null_mut();
        v___f_7428_ = lean_alloc_closure(
            l_Array_sum___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_7428_, 0, v_inst_7421_);
        v___x_7429_ = lean_usize_of_nat(v___x_7424_);
        v___x_7430_ = 0usize;
        v___x_7431_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
            v___x_7426_,
            v___f_7428_,
            v_as_7423_,
            v___x_7429_,
            v___x_7430_,
            v_inst_7422_,
        );
        return v___x_7431_;
    }
}
pub unsafe fn l_Array_prod(
    mut v_00_u03b1_7432_: *mut LeanObject,
    mut v_inst_7433_: *mut LeanObject,
    mut v_inst_7434_: *mut LeanObject,
    mut v_as_7435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7439_: u8 = 0;
    v___x_7436_ = lean_array_get_size(v_as_7435_);
    v___x_7437_ = lean_unsigned_to_nat(0);
    v___x_7438_ = l_Array_foldl___redArg___closed__9;
    v___x_7439_ = lean_nat_dec_lt(v___x_7437_, v___x_7436_);
    if v___x_7439_ == 0 {
        lean_dec_ref(v_as_7435_);
        lean_dec(v_inst_7433_);
        return v_inst_7434_;
    } else {
        let mut v___f_7440_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7441_: usize = 0;
        let mut v___x_7442_: usize = 0;
        let mut v___x_7443_: *mut LeanObject = core::ptr::null_mut();
        v___f_7440_ = lean_alloc_closure(
            l_Array_sum___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_7440_, 0, v_inst_7433_);
        v___x_7441_ = lean_usize_of_nat(v___x_7436_);
        v___x_7442_ = 0usize;
        v___x_7443_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
            v___x_7438_,
            v___f_7440_,
            v_as_7435_,
            v___x_7441_,
            v___x_7442_,
            v_inst_7434_,
        );
        return v___x_7443_;
    }
}
pub unsafe fn l_Array_countP___redArg___lam__0(
    mut v_p_7444_: *mut LeanObject,
    mut v_x1_7445_: *mut LeanObject,
    mut v_x2_7446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7448_: u8 = 0;
    v___x_7447_ = lean_apply_1(v_p_7444_, v_x1_7445_);
    v___x_7448_ = (lean_unbox(v___x_7447_) as u8);
    if v___x_7448_ == 0 {
        lean_inc(v_x2_7446_);
        return v_x2_7446_;
    } else {
        let mut v___x_7449_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7450_: *mut LeanObject = core::ptr::null_mut();
        v___x_7449_ = lean_unsigned_to_nat(1);
        v___x_7450_ = lean_nat_add(v_x2_7446_, v___x_7449_);
        return v___x_7450_;
    }
}
pub unsafe fn l_Array_countP___redArg___lam__0___boxed(
    mut v_p_7451_: *mut LeanObject,
    mut v_x1_7452_: *mut LeanObject,
    mut v_x2_7453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7454_: *mut LeanObject = core::ptr::null_mut();
    v_res_7454_ = l_Array_countP___redArg___lam__0(v_p_7451_, v_x1_7452_, v_x2_7453_);
    lean_dec(v_x2_7453_);
    return v_res_7454_;
}
pub unsafe fn l_Array_countP___redArg(
    mut v_p_7455_: *mut LeanObject,
    mut v_as_7456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7460_: u8 = 0;
    v___x_7457_ = lean_unsigned_to_nat(0);
    v___x_7458_ = lean_array_get_size(v_as_7456_);
    v___x_7459_ = l_Array_foldl___redArg___closed__9;
    v___x_7460_ = lean_nat_dec_lt(v___x_7457_, v___x_7458_);
    if v___x_7460_ == 0 {
        lean_dec_ref(v_as_7456_);
        lean_dec_ref(v_p_7455_);
        return v___x_7457_;
    } else {
        let mut v___f_7461_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7462_: usize = 0;
        let mut v___x_7463_: usize = 0;
        let mut v___x_7464_: *mut LeanObject = core::ptr::null_mut();
        v___f_7461_ = lean_alloc_closure(
            l_Array_countP___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_7461_, 0, v_p_7455_);
        v___x_7462_ = lean_usize_of_nat(v___x_7458_);
        v___x_7463_ = 0usize;
        v___x_7464_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
            v___x_7459_,
            v___f_7461_,
            v_as_7456_,
            v___x_7462_,
            v___x_7463_,
            v___x_7457_,
        );
        return v___x_7464_;
    }
}
pub unsafe fn l_Array_countP(
    mut v_00_u03b1_7465_: *mut LeanObject,
    mut v_p_7466_: *mut LeanObject,
    mut v_as_7467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7471_: u8 = 0;
    v___x_7468_ = lean_unsigned_to_nat(0);
    v___x_7469_ = lean_array_get_size(v_as_7467_);
    v___x_7470_ = l_Array_foldl___redArg___closed__9;
    v___x_7471_ = lean_nat_dec_lt(v___x_7468_, v___x_7469_);
    if v___x_7471_ == 0 {
        lean_dec_ref(v_as_7467_);
        lean_dec_ref(v_p_7466_);
        return v___x_7468_;
    } else {
        let mut v___f_7472_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7473_: usize = 0;
        let mut v___x_7474_: usize = 0;
        let mut v___x_7475_: *mut LeanObject = core::ptr::null_mut();
        v___f_7472_ = lean_alloc_closure(
            l_Array_countP___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_7472_, 0, v_p_7466_);
        v___x_7473_ = lean_usize_of_nat(v___x_7469_);
        v___x_7474_ = 0usize;
        v___x_7475_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
            v___x_7470_,
            v___f_7472_,
            v_as_7467_,
            v___x_7473_,
            v___x_7474_,
            v___x_7468_,
        );
        return v___x_7475_;
    }
}
pub unsafe fn l_Array_count___redArg___lam__0(
    mut v_inst_7476_: *mut LeanObject,
    mut v_a_7477_: *mut LeanObject,
    mut v_x1_7478_: *mut LeanObject,
    mut v_x2_7479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7481_: u8 = 0;
    v___x_7480_ = lean_apply_2(v_inst_7476_, v_x1_7478_, v_a_7477_);
    v___x_7481_ = (lean_unbox(v___x_7480_) as u8);
    if v___x_7481_ == 0 {
        lean_inc(v_x2_7479_);
        return v_x2_7479_;
    } else {
        let mut v___x_7482_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7483_: *mut LeanObject = core::ptr::null_mut();
        v___x_7482_ = lean_unsigned_to_nat(1);
        v___x_7483_ = lean_nat_add(v_x2_7479_, v___x_7482_);
        return v___x_7483_;
    }
}
pub unsafe fn l_Array_count___redArg___lam__0___boxed(
    mut v_inst_7484_: *mut LeanObject,
    mut v_a_7485_: *mut LeanObject,
    mut v_x1_7486_: *mut LeanObject,
    mut v_x2_7487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7488_: *mut LeanObject = core::ptr::null_mut();
    v_res_7488_ = l_Array_count___redArg___lam__0(v_inst_7484_, v_a_7485_, v_x1_7486_, v_x2_7487_);
    lean_dec(v_x2_7487_);
    return v_res_7488_;
}
pub unsafe fn l_Array_count___redArg(
    mut v_inst_7489_: *mut LeanObject,
    mut v_a_7490_: *mut LeanObject,
    mut v_as_7491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7495_: u8 = 0;
    v___x_7492_ = lean_unsigned_to_nat(0);
    v___x_7493_ = lean_array_get_size(v_as_7491_);
    v___x_7494_ = l_Array_foldl___redArg___closed__9;
    v___x_7495_ = lean_nat_dec_lt(v___x_7492_, v___x_7493_);
    if v___x_7495_ == 0 {
        lean_dec_ref(v_as_7491_);
        lean_dec(v_a_7490_);
        lean_dec_ref(v_inst_7489_);
        return v___x_7492_;
    } else {
        let mut v___f_7496_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7497_: usize = 0;
        let mut v___x_7498_: usize = 0;
        let mut v___x_7499_: *mut LeanObject = core::ptr::null_mut();
        v___f_7496_ = lean_alloc_closure(
            l_Array_count___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_7496_, 0, v_inst_7489_);
        lean_closure_set(v___f_7496_, 1, v_a_7490_);
        v___x_7497_ = lean_usize_of_nat(v___x_7493_);
        v___x_7498_ = 0usize;
        v___x_7499_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
            v___x_7494_,
            v___f_7496_,
            v_as_7491_,
            v___x_7497_,
            v___x_7498_,
            v___x_7492_,
        );
        return v___x_7499_;
    }
}
pub unsafe fn l_Array_count(
    mut v_00_u03b1_7500_: *mut LeanObject,
    mut v_inst_7501_: *mut LeanObject,
    mut v_a_7502_: *mut LeanObject,
    mut v_as_7503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7507_: u8 = 0;
    v___x_7504_ = lean_unsigned_to_nat(0);
    v___x_7505_ = lean_array_get_size(v_as_7503_);
    v___x_7506_ = l_Array_foldl___redArg___closed__9;
    v___x_7507_ = lean_nat_dec_lt(v___x_7504_, v___x_7505_);
    if v___x_7507_ == 0 {
        lean_dec_ref(v_as_7503_);
        lean_dec(v_a_7502_);
        lean_dec_ref(v_inst_7501_);
        return v___x_7504_;
    } else {
        let mut v___f_7508_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7509_: usize = 0;
        let mut v___x_7510_: usize = 0;
        let mut v___x_7511_: *mut LeanObject = core::ptr::null_mut();
        v___f_7508_ = lean_alloc_closure(
            l_Array_count___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_7508_, 0, v_inst_7501_);
        lean_closure_set(v___f_7508_, 1, v_a_7502_);
        v___x_7509_ = lean_usize_of_nat(v___x_7505_);
        v___x_7510_ = 0usize;
        v___x_7511_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
            v___x_7506_,
            v___f_7508_,
            v_as_7503_,
            v___x_7509_,
            v___x_7510_,
            v___x_7504_,
        );
        return v___x_7511_;
    }
}
pub unsafe fn l_Array_map___redArg___lam__0(
    mut v_f_7512_: *mut LeanObject,
    mut v_x_7513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7514_: *mut LeanObject = core::ptr::null_mut();
    v___x_7514_ = lean_apply_1(v_f_7512_, v_x_7513_);
    return v___x_7514_;
}
pub unsafe fn l_Array_map___redArg(
    mut v_f_7515_: *mut LeanObject,
    mut v_as_7516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7519_: usize = 0;
    let mut v___x_7520_: usize = 0;
    let mut v___x_7521_: *mut LeanObject = core::ptr::null_mut();
    v___f_7517_ = lean_alloc_closure(
        l_Array_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7517_, 0, v_f_7515_);
    v___x_7518_ = l_Array_foldl___redArg___closed__9;
    v_sz_7519_ = lean_array_size(v_as_7516_);
    v___x_7520_ = 0usize;
    v___x_7521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(
        v___x_7518_,
        v___f_7517_,
        v_sz_7519_,
        v___x_7520_,
        v_as_7516_,
    );
    return v___x_7521_;
}
pub unsafe fn l_Array_map(
    mut v_00_u03b1_7522_: *mut LeanObject,
    mut v_00_u03b2_7523_: *mut LeanObject,
    mut v_f_7524_: *mut LeanObject,
    mut v_as_7525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7528_: usize = 0;
    let mut v___x_7529_: usize = 0;
    let mut v___x_7530_: *mut LeanObject = core::ptr::null_mut();
    v___f_7526_ = lean_alloc_closure(
        l_Array_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7526_, 0, v_f_7524_);
    v___x_7527_ = l_Array_foldl___redArg___closed__9;
    v_sz_7528_ = lean_array_size(v_as_7525_);
    v___x_7529_ = 0usize;
    v___x_7530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(
        v___x_7527_,
        v___f_7526_,
        v_sz_7528_,
        v___x_7529_,
        v_as_7525_,
    );
    return v___x_7530_;
}
pub unsafe fn l_Array_instFunctor___lam__0(
    mut v___y_7531_: *mut LeanObject,
    mut v_x_7532_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v___y_7531_);
    return v___y_7531_;
}
pub unsafe fn l_Array_instFunctor___lam__0___boxed(
    mut v___y_7533_: *mut LeanObject,
    mut v_x_7534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7535_: *mut LeanObject = core::ptr::null_mut();
    v_res_7535_ = l_Array_instFunctor___lam__0(v___y_7533_, v_x_7534_);
    lean_dec(v_x_7534_);
    lean_dec(v___y_7533_);
    return v_res_7535_;
}
pub unsafe fn l_Array_instFunctor___lam__1(
    mut v_00_u03b1_7536_: *mut LeanObject,
    mut v_00_u03b2_7537_: *mut LeanObject,
    mut v___y_7538_: *mut LeanObject,
    mut v___y_7539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7542_: usize = 0;
    let mut v___x_7543_: usize = 0;
    let mut v___x_7544_: *mut LeanObject = core::ptr::null_mut();
    v___f_7540_ = lean_alloc_closure(
        l_Array_instFunctor___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7540_, 0, v___y_7538_);
    v___x_7541_ = l_Array_foldl___redArg___closed__9;
    v_sz_7542_ = lean_array_size(v___y_7539_);
    v___x_7543_ = 0usize;
    v___x_7544_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(
        v___x_7541_,
        v___f_7540_,
        v_sz_7542_,
        v___x_7543_,
        v___y_7539_,
    );
    return v___x_7544_;
}
pub unsafe fn l_Array_mapFinIdx___redArg___lam__0(
    mut v_f_7551_: *mut LeanObject,
    mut v_x1_7552_: *mut LeanObject,
    mut v_x2_7553_: *mut LeanObject,
    mut v_x3_7554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7555_: *mut LeanObject = core::ptr::null_mut();
    v___x_7555_ = lean_apply_3(v_f_7551_, v_x1_7552_, v_x2_7553_, lean_box(0));
    return v___x_7555_;
}
pub unsafe fn l_Array_mapFinIdx___redArg(
    mut v_as_7556_: *mut LeanObject,
    mut v_f_7557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7563_: *mut LeanObject = core::ptr::null_mut();
    v___f_7558_ = lean_alloc_closure(
        l_Array_mapFinIdx___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_7558_, 0, v_f_7557_);
    v___x_7559_ = l_Array_foldl___redArg___closed__9;
    v___x_7560_ = lean_array_get_size(v_as_7556_);
    v___x_7561_ = lean_unsigned_to_nat(0);
    v___x_7562_ = lean_mk_empty_array_with_capacity(v___x_7560_);
    v___x_7563_ = l_Array_mapFinIdxM_map___redArg(
        v___x_7559_,
        v_as_7556_,
        v___f_7558_,
        v___x_7560_,
        v___x_7561_,
        v___x_7562_,
    );
    return v___x_7563_;
}
pub unsafe fn l_Array_mapFinIdx(
    mut v_00_u03b1_7564_: *mut LeanObject,
    mut v_00_u03b2_7565_: *mut LeanObject,
    mut v_as_7566_: *mut LeanObject,
    mut v_f_7567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7573_: *mut LeanObject = core::ptr::null_mut();
    v___f_7568_ = lean_alloc_closure(
        l_Array_mapFinIdx___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_7568_, 0, v_f_7567_);
    v___x_7569_ = l_Array_foldl___redArg___closed__9;
    v___x_7570_ = lean_array_get_size(v_as_7566_);
    v___x_7571_ = lean_unsigned_to_nat(0);
    v___x_7572_ = lean_mk_empty_array_with_capacity(v___x_7570_);
    v___x_7573_ = l_Array_mapFinIdxM_map___redArg(
        v___x_7569_,
        v_as_7566_,
        v___f_7568_,
        v___x_7570_,
        v___x_7571_,
        v___x_7572_,
    );
    return v___x_7573_;
}
pub unsafe fn l_Array_mapIdx___redArg(
    mut v_f_7574_: *mut LeanObject,
    mut v_as_7575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7581_: *mut LeanObject = core::ptr::null_mut();
    v___f_7576_ = lean_alloc_closure(
        l_Array_mapIdxM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_7576_, 0, v_f_7574_);
    v___x_7577_ = l_Array_foldl___redArg___closed__9;
    v___x_7578_ = lean_array_get_size(v_as_7575_);
    v___x_7579_ = lean_unsigned_to_nat(0);
    v___x_7580_ = lean_mk_empty_array_with_capacity(v___x_7578_);
    v___x_7581_ = l_Array_mapFinIdxM_map___redArg(
        v___x_7577_,
        v_as_7575_,
        v___f_7576_,
        v___x_7578_,
        v___x_7579_,
        v___x_7580_,
    );
    return v___x_7581_;
}
pub unsafe fn l_Array_mapIdx(
    mut v_00_u03b1_7582_: *mut LeanObject,
    mut v_00_u03b2_7583_: *mut LeanObject,
    mut v_f_7584_: *mut LeanObject,
    mut v_as_7585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7591_: *mut LeanObject = core::ptr::null_mut();
    v___f_7586_ = lean_alloc_closure(
        l_Array_mapIdxM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_7586_, 0, v_f_7584_);
    v___x_7587_ = l_Array_foldl___redArg___closed__9;
    v___x_7588_ = lean_array_get_size(v_as_7585_);
    v___x_7589_ = lean_unsigned_to_nat(0);
    v___x_7590_ = lean_mk_empty_array_with_capacity(v___x_7588_);
    v___x_7591_ = l_Array_mapFinIdxM_map___redArg(
        v___x_7587_,
        v_as_7585_,
        v___f_7586_,
        v___x_7588_,
        v___x_7589_,
        v___x_7590_,
    );
    return v___x_7591_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(
    mut v_start_7592_: *mut LeanObject,
    mut v_as_7593_: *mut LeanObject,
    mut v_i_7594_: *mut LeanObject,
    mut v_j_7595_: *mut LeanObject,
    mut v_bs_7596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_7597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_7598_: u8 = 0;
    let mut v_one_7599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_7600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7605_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_7597_ = lean_unsigned_to_nat(0);
                v_isZero_7598_ = lean_nat_dec_eq(v_i_7594_, v_zero_7597_);
                if v_isZero_7598_ == 1 {
                    lean_dec(v_j_7595_);
                    lean_dec(v_i_7594_);
                    return v_bs_7596_;
                } else {
                    v_one_7599_ = lean_unsigned_to_nat(1);
                    v_n_7600_ = lean_nat_sub(v_i_7594_, v_one_7599_);
                    lean_dec(v_i_7594_);
                    v___x_7601_ = lean_array_fget_borrowed(v_as_7593_, v_j_7595_);
                    v___x_7602_ = lean_nat_add(v_start_7592_, v_j_7595_);
                    lean_inc(v___x_7601_);
                    v___x_7603_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_7603_, 0, v___x_7601_);
                    lean_ctor_set(v___x_7603_, 1, v___x_7602_);
                    v___x_7604_ = lean_nat_add(v_j_7595_, v_one_7599_);
                    lean_dec(v_j_7595_);
                    v___x_7605_ = lean_array_push(v_bs_7596_, v___x_7603_);
                    v_i_7594_ = v_n_7600_;
                    v_j_7595_ = v___x_7604_;
                    v_bs_7596_ = v___x_7605_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg___boxed(
    mut v_start_7607_: *mut LeanObject,
    mut v_as_7608_: *mut LeanObject,
    mut v_i_7609_: *mut LeanObject,
    mut v_j_7610_: *mut LeanObject,
    mut v_bs_7611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7612_: *mut LeanObject = core::ptr::null_mut();
    v_res_7612_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(
        v_start_7607_,
        v_as_7608_,
        v_i_7609_,
        v_j_7610_,
        v_bs_7611_,
    );
    lean_dec_ref(v_as_7608_);
    lean_dec(v_start_7607_);
    return v_res_7612_;
}
pub unsafe fn l_Array_zipIdx___redArg(
    mut v_xs_7613_: *mut LeanObject,
    mut v_start_7614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7618_: *mut LeanObject = core::ptr::null_mut();
    v___x_7615_ = lean_array_get_size(v_xs_7613_);
    v___x_7616_ = lean_unsigned_to_nat(0);
    v___x_7617_ = lean_mk_empty_array_with_capacity(v___x_7615_);
    v___x_7618_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(
        v_start_7614_,
        v_xs_7613_,
        v___x_7615_,
        v___x_7616_,
        v___x_7617_,
    );
    return v___x_7618_;
}
pub unsafe fn l_Array_zipIdx___redArg___boxed(
    mut v_xs_7619_: *mut LeanObject,
    mut v_start_7620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7621_: *mut LeanObject = core::ptr::null_mut();
    v_res_7621_ = l_Array_zipIdx___redArg(v_xs_7619_, v_start_7620_);
    lean_dec(v_start_7620_);
    lean_dec_ref(v_xs_7619_);
    return v_res_7621_;
}
pub unsafe fn l_Array_zipIdx(
    mut v_00_u03b1_7622_: *mut LeanObject,
    mut v_xs_7623_: *mut LeanObject,
    mut v_start_7624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7625_: *mut LeanObject = core::ptr::null_mut();
    v___x_7625_ = l_Array_zipIdx___redArg(v_xs_7623_, v_start_7624_);
    return v___x_7625_;
}
pub unsafe fn l_Array_zipIdx___boxed(
    mut v_00_u03b1_7626_: *mut LeanObject,
    mut v_xs_7627_: *mut LeanObject,
    mut v_start_7628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7629_: *mut LeanObject = core::ptr::null_mut();
    v_res_7629_ = l_Array_zipIdx(v_00_u03b1_7626_, v_xs_7627_, v_start_7628_);
    lean_dec(v_start_7628_);
    lean_dec_ref(v_xs_7627_);
    return v_res_7629_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0(
    mut v_00_u03b1_7630_: *mut LeanObject,
    mut v_start_7631_: *mut LeanObject,
    mut v_as_7632_: *mut LeanObject,
    mut v_i_7633_: *mut LeanObject,
    mut v_j_7634_: *mut LeanObject,
    mut v_inv_7635_: *mut LeanObject,
    mut v_bs_7636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7637_: *mut LeanObject = core::ptr::null_mut();
    v___x_7637_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(
        v_start_7631_,
        v_as_7632_,
        v_i_7633_,
        v_j_7634_,
        v_bs_7636_,
    );
    return v___x_7637_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___boxed(
    mut v_00_u03b1_7638_: *mut LeanObject,
    mut v_start_7639_: *mut LeanObject,
    mut v_as_7640_: *mut LeanObject,
    mut v_i_7641_: *mut LeanObject,
    mut v_j_7642_: *mut LeanObject,
    mut v_inv_7643_: *mut LeanObject,
    mut v_bs_7644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7645_: *mut LeanObject = core::ptr::null_mut();
    v_res_7645_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0(
        v_00_u03b1_7638_,
        v_start_7639_,
        v_as_7640_,
        v_i_7641_,
        v_j_7642_,
        v_inv_7643_,
        v_bs_7644_,
    );
    lean_dec_ref(v_as_7640_);
    lean_dec(v_start_7639_);
    return v_res_7645_;
}
pub unsafe fn l_Array_find_x3f___redArg___lam__0(
    mut v_p_7646_: *mut LeanObject,
    mut v___x_7647_: *mut LeanObject,
    mut v___x_7648_: *mut LeanObject,
    mut v_a_7649_: *mut LeanObject,
    mut v_x_7650_: *mut LeanObject,
    mut v___y_7651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7653_: u8 = 0;
    lean_inc(v_a_7649_);
    v___x_7652_ = lean_apply_1(v_p_7646_, v_a_7649_);
    v___x_7653_ = (lean_unbox(v___x_7652_) as u8);
    if v___x_7653_ == 0 {
        let mut v___x_7654_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_7649_);
        v___x_7654_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_7654_, 0, v___x_7647_);
        return v___x_7654_;
    } else {
        let mut v___x_7655_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7656_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7657_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7658_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_7647_);
        v___x_7655_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_7655_, 0, v_a_7649_);
        v___x_7656_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_7656_, 0, v___x_7655_);
        v___x_7657_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_7657_, 0, v___x_7656_);
        lean_ctor_set(v___x_7657_, 1, v___x_7648_);
        v___x_7658_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_7658_, 0, v___x_7657_);
        return v___x_7658_;
    }
}
pub unsafe fn l_Array_find_x3f___redArg___lam__0___boxed(
    mut v_p_7659_: *mut LeanObject,
    mut v___x_7660_: *mut LeanObject,
    mut v___x_7661_: *mut LeanObject,
    mut v_a_7662_: *mut LeanObject,
    mut v_x_7663_: *mut LeanObject,
    mut v___y_7664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7665_: *mut LeanObject = core::ptr::null_mut();
    v_res_7665_ = l_Array_find_x3f___redArg___lam__0(
        v_p_7659_,
        v___x_7660_,
        v___x_7661_,
        v_a_7662_,
        v_x_7663_,
        v___y_7664_,
    );
    lean_dec_ref(v___y_7664_);
    return v_res_7665_;
}
pub unsafe fn l_Array_find_x3f___redArg(
    mut v_p_7666_: *mut LeanObject,
    mut v_as_7667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7673_: usize = 0;
    let mut v___x_7674_: usize = 0;
    let mut v___x_7675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7676_: *mut LeanObject = core::ptr::null_mut();
    v___x_7668_ = l_Array_foldl___redArg___closed__9;
    v___x_7669_ = lean_box(0);
    v___x_7670_ = lean_box(0);
    v___x_7671_ = l_Array_findSomeM_x3f___redArg___closed__0;
    v___f_7672_ = lean_alloc_closure(
        l_Array_find_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_7672_, 0, v_p_7666_);
    lean_closure_set(v___f_7672_, 1, v___x_7671_);
    lean_closure_set(v___f_7672_, 2, v___x_7670_);
    v_sz_7673_ = lean_array_size(v_as_7667_);
    v___x_7674_ = 0usize;
    v___x_7675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
        v___x_7668_,
        v_as_7667_,
        v___f_7672_,
        v_sz_7673_,
        v___x_7674_,
        v___x_7671_,
    );
    v_fst_7676_ = lean_ctor_get(v___x_7675_, 0);
    lean_inc(v_fst_7676_);
    lean_dec(v___x_7675_);
    if lean_obj_tag(v_fst_7676_) == 0 {
        return v___x_7669_;
    } else {
        let mut v_val_7677_: *mut LeanObject = core::ptr::null_mut();
        v_val_7677_ = lean_ctor_get(v_fst_7676_, 0);
        lean_inc(v_val_7677_);
        lean_dec_ref_known(v_fst_7676_, 1);
        return v_val_7677_;
    }
}
pub unsafe fn l_Array_find_x3f(
    mut v_00_u03b1_7678_: *mut LeanObject,
    mut v_p_7679_: *mut LeanObject,
    mut v_as_7680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7686_: usize = 0;
    let mut v___x_7687_: usize = 0;
    let mut v___x_7688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7689_: *mut LeanObject = core::ptr::null_mut();
    v___x_7681_ = l_Array_foldl___redArg___closed__9;
    v___x_7682_ = lean_box(0);
    v___x_7683_ = lean_box(0);
    v___x_7684_ = l_Array_findSomeM_x3f___redArg___closed__0;
    v___f_7685_ = lean_alloc_closure(
        l_Array_find_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_7685_, 0, v_p_7679_);
    lean_closure_set(v___f_7685_, 1, v___x_7684_);
    lean_closure_set(v___f_7685_, 2, v___x_7683_);
    v_sz_7686_ = lean_array_size(v_as_7680_);
    v___x_7687_ = 0usize;
    v___x_7688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
        v___x_7681_,
        v_as_7680_,
        v___f_7685_,
        v_sz_7686_,
        v___x_7687_,
        v___x_7684_,
    );
    v_fst_7689_ = lean_ctor_get(v___x_7688_, 0);
    lean_inc(v_fst_7689_);
    lean_dec(v___x_7688_);
    if lean_obj_tag(v_fst_7689_) == 0 {
        return v___x_7682_;
    } else {
        let mut v_val_7690_: *mut LeanObject = core::ptr::null_mut();
        v_val_7690_ = lean_ctor_get(v_fst_7689_, 0);
        lean_inc(v_val_7690_);
        lean_dec_ref_known(v_fst_7689_, 1);
        return v_val_7690_;
    }
}
pub unsafe fn l_Array_findSome_x3f___redArg___lam__0(
    mut v_f_7691_: *mut LeanObject,
    mut v___x_7692_: *mut LeanObject,
    mut v___x_7693_: *mut LeanObject,
    mut v_a_7694_: *mut LeanObject,
    mut v_x_7695_: *mut LeanObject,
    mut v___y_7696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7697_: *mut LeanObject = core::ptr::null_mut();
    v___x_7697_ = lean_apply_1(v_f_7691_, v_a_7694_);
    if lean_obj_tag(v___x_7697_) == 1 {
        let mut v___x_7698_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7699_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7700_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_7693_);
        v___x_7698_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_7698_, 0, v___x_7697_);
        v___x_7699_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_7699_, 0, v___x_7698_);
        lean_ctor_set(v___x_7699_, 1, v___x_7692_);
        v___x_7700_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_7700_, 0, v___x_7699_);
        return v___x_7700_;
    } else {
        let mut v___x_7701_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_7697_);
        v___x_7701_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_7701_, 0, v___x_7693_);
        return v___x_7701_;
    }
}
pub unsafe fn l_Array_findSome_x3f___redArg___lam__0___boxed(
    mut v_f_7702_: *mut LeanObject,
    mut v___x_7703_: *mut LeanObject,
    mut v___x_7704_: *mut LeanObject,
    mut v_a_7705_: *mut LeanObject,
    mut v_x_7706_: *mut LeanObject,
    mut v___y_7707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7708_: *mut LeanObject = core::ptr::null_mut();
    v_res_7708_ = l_Array_findSome_x3f___redArg___lam__0(
        v_f_7702_,
        v___x_7703_,
        v___x_7704_,
        v_a_7705_,
        v_x_7706_,
        v___y_7707_,
    );
    lean_dec_ref(v___y_7707_);
    return v_res_7708_;
}
pub unsafe fn l_Array_findSome_x3f___redArg(
    mut v_f_7709_: *mut LeanObject,
    mut v_as_7710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7716_: usize = 0;
    let mut v___x_7717_: usize = 0;
    let mut v___x_7718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7719_: *mut LeanObject = core::ptr::null_mut();
    v___x_7711_ = l_Array_foldl___redArg___closed__9;
    v___x_7712_ = lean_box(0);
    v___x_7713_ = lean_box(0);
    v___x_7714_ = l_Array_findSomeM_x3f___redArg___closed__0;
    v___f_7715_ = lean_alloc_closure(
        l_Array_findSome_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_7715_, 0, v_f_7709_);
    lean_closure_set(v___f_7715_, 1, v___x_7713_);
    lean_closure_set(v___f_7715_, 2, v___x_7714_);
    v_sz_7716_ = lean_array_size(v_as_7710_);
    v___x_7717_ = 0usize;
    v___x_7718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
        v___x_7711_,
        v_as_7710_,
        v___f_7715_,
        v_sz_7716_,
        v___x_7717_,
        v___x_7714_,
    );
    v_fst_7719_ = lean_ctor_get(v___x_7718_, 0);
    lean_inc(v_fst_7719_);
    lean_dec(v___x_7718_);
    if lean_obj_tag(v_fst_7719_) == 0 {
        return v___x_7712_;
    } else {
        let mut v_val_7720_: *mut LeanObject = core::ptr::null_mut();
        v_val_7720_ = lean_ctor_get(v_fst_7719_, 0);
        lean_inc(v_val_7720_);
        lean_dec_ref_known(v_fst_7719_, 1);
        return v_val_7720_;
    }
}
pub unsafe fn l_Array_findSome_x3f(
    mut v_00_u03b1_7721_: *mut LeanObject,
    mut v_00_u03b2_7722_: *mut LeanObject,
    mut v_f_7723_: *mut LeanObject,
    mut v_as_7724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7730_: usize = 0;
    let mut v___x_7731_: usize = 0;
    let mut v___x_7732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7733_: *mut LeanObject = core::ptr::null_mut();
    v___x_7725_ = l_Array_foldl___redArg___closed__9;
    v___x_7726_ = lean_box(0);
    v___x_7727_ = lean_box(0);
    v___x_7728_ = l_Array_findSomeM_x3f___redArg___closed__0;
    v___f_7729_ = lean_alloc_closure(
        l_Array_findSome_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_7729_, 0, v_f_7723_);
    lean_closure_set(v___f_7729_, 1, v___x_7727_);
    lean_closure_set(v___f_7729_, 2, v___x_7728_);
    v_sz_7730_ = lean_array_size(v_as_7724_);
    v___x_7731_ = 0usize;
    v___x_7732_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
        v___x_7725_,
        v_as_7724_,
        v___f_7729_,
        v_sz_7730_,
        v___x_7731_,
        v___x_7728_,
    );
    v_fst_7733_ = lean_ctor_get(v___x_7732_, 0);
    lean_inc(v_fst_7733_);
    lean_dec(v___x_7732_);
    if lean_obj_tag(v_fst_7733_) == 0 {
        return v___x_7726_;
    } else {
        let mut v_val_7734_: *mut LeanObject = core::ptr::null_mut();
        v_val_7734_ = lean_ctor_get(v_fst_7733_, 0);
        lean_inc(v_val_7734_);
        lean_dec_ref_known(v_fst_7733_, 1);
        return v_val_7734_;
    }
}
pub unsafe fn _init_l_Array_findSome_x21___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_7737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7742_: *mut LeanObject = core::ptr::null_mut();
    v___x_7737_ = l_Array_findSome_x21___redArg___closed__1;
    v___x_7738_ = lean_unsigned_to_nat(14);
    v___x_7739_ = lean_unsigned_to_nat(1232);
    v___x_7740_ = l_Array_findSome_x21___redArg___closed__0;
    v___x_7741_ = l_Array_swapAt_x21___redArg___closed__0;
    v___x_7742_ = l_mkPanicMessageWithDecl(
        v___x_7741_,
        v___x_7740_,
        v___x_7739_,
        v___x_7738_,
        v___x_7737_,
    );
    return v___x_7742_;
}
pub unsafe fn l_Array_findSome_x21___redArg(
    mut v_inst_7743_: *mut LeanObject,
    mut v_f_7744_: *mut LeanObject,
    mut v_xs_7745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7753_: usize = 0;
    let mut v___x_7754_: usize = 0;
    let mut v___x_7755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7758_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7749_ = l_Array_foldl___redArg___closed__9;
                v___x_7750_ = lean_box(0);
                v___x_7751_ = l_Array_findSomeM_x3f___redArg___closed__0;
                v___f_7752_ = lean_alloc_closure(
                    l_Array_findSome_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_7752_, 0, v_f_7744_);
                lean_closure_set(v___f_7752_, 1, v___x_7750_);
                lean_closure_set(v___f_7752_, 2, v___x_7751_);
                v_sz_7753_ = lean_array_size(v_xs_7745_);
                v___x_7754_ = 0usize;
                v___x_7755_ =
                    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
                        v___x_7749_,
                        v_xs_7745_,
                        v___f_7752_,
                        v_sz_7753_,
                        v___x_7754_,
                        v___x_7751_,
                    );
                v_fst_7756_ = lean_ctor_get(v___x_7755_, 0);
                lean_inc(v_fst_7756_);
                lean_dec(v___x_7755_);
                if lean_obj_tag(v_fst_7756_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_7757_ = lean_ctor_get(v_fst_7756_, 0);
                    lean_inc(v_val_7757_);
                    lean_dec_ref_known(v_fst_7756_, 1);
                    if lean_obj_tag(v_val_7757_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_val_7758_ = lean_ctor_get(v_val_7757_, 0);
                        lean_inc(v_val_7758_);
                        lean_dec_ref_known(v_val_7757_, 1);
                        return v_val_7758_;
                    }
                }
            }
            1 => {
                v___x_7747_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Array_findSome_x21___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Array_findSome_x21___redArg___closed__2_once),
                    _init_l_Array_findSome_x21___redArg___closed__2,
                );
                v___x_7748_ = l_panic___redArg(v_inst_7743_, v___x_7747_);
                return v___x_7748_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_findSome_x21___redArg___boxed(
    mut v_inst_7759_: *mut LeanObject,
    mut v_f_7760_: *mut LeanObject,
    mut v_xs_7761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7762_: *mut LeanObject = core::ptr::null_mut();
    v_res_7762_ = l_Array_findSome_x21___redArg(v_inst_7759_, v_f_7760_, v_xs_7761_);
    lean_dec(v_inst_7759_);
    return v_res_7762_;
}
pub unsafe fn l_Array_findSome_x21(
    mut v_00_u03b1_7763_: *mut LeanObject,
    mut v_00_u03b2_7764_: *mut LeanObject,
    mut v_inst_7765_: *mut LeanObject,
    mut v_f_7766_: *mut LeanObject,
    mut v_xs_7767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7775_: usize = 0;
    let mut v___x_7776_: usize = 0;
    let mut v___x_7777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7780_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7771_ = l_Array_foldl___redArg___closed__9;
                v___x_7772_ = lean_box(0);
                v___x_7773_ = l_Array_findSomeM_x3f___redArg___closed__0;
                v___f_7774_ = lean_alloc_closure(
                    l_Array_findSome_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_7774_, 0, v_f_7766_);
                lean_closure_set(v___f_7774_, 1, v___x_7772_);
                lean_closure_set(v___f_7774_, 2, v___x_7773_);
                v_sz_7775_ = lean_array_size(v_xs_7767_);
                v___x_7776_ = 0usize;
                v___x_7777_ =
                    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
                        v___x_7771_,
                        v_xs_7767_,
                        v___f_7774_,
                        v_sz_7775_,
                        v___x_7776_,
                        v___x_7773_,
                    );
                v_fst_7778_ = lean_ctor_get(v___x_7777_, 0);
                lean_inc(v_fst_7778_);
                lean_dec(v___x_7777_);
                if lean_obj_tag(v_fst_7778_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_7779_ = lean_ctor_get(v_fst_7778_, 0);
                    lean_inc(v_val_7779_);
                    lean_dec_ref_known(v_fst_7778_, 1);
                    if lean_obj_tag(v_val_7779_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_val_7780_ = lean_ctor_get(v_val_7779_, 0);
                        lean_inc(v_val_7780_);
                        lean_dec_ref_known(v_val_7779_, 1);
                        return v_val_7780_;
                    }
                }
            }
            1 => {
                v___x_7769_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Array_findSome_x21___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Array_findSome_x21___redArg___closed__2_once),
                    _init_l_Array_findSome_x21___redArg___closed__2,
                );
                v___x_7770_ = l_panic___redArg(v_inst_7765_, v___x_7769_);
                return v___x_7770_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_findSome_x21___boxed(
    mut v_00_u03b1_7781_: *mut LeanObject,
    mut v_00_u03b2_7782_: *mut LeanObject,
    mut v_inst_7783_: *mut LeanObject,
    mut v_f_7784_: *mut LeanObject,
    mut v_xs_7785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7786_: *mut LeanObject = core::ptr::null_mut();
    v_res_7786_ = l_Array_findSome_x21(
        v_00_u03b1_7781_,
        v_00_u03b2_7782_,
        v_inst_7783_,
        v_f_7784_,
        v_xs_7785_,
    );
    lean_dec(v_inst_7783_);
    return v_res_7786_;
}
pub unsafe fn l_Array_findSomeRev_x3f___redArg___lam__0(
    mut v_f_7787_: *mut LeanObject,
    mut v_x_7788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7789_: *mut LeanObject = core::ptr::null_mut();
    v___x_7789_ = lean_apply_1(v_f_7787_, v_x_7788_);
    return v___x_7789_;
}
pub unsafe fn l_Array_findSomeRev_x3f___redArg(
    mut v_f_7790_: *mut LeanObject,
    mut v_as_7791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7795_: *mut LeanObject = core::ptr::null_mut();
    v___f_7792_ = lean_alloc_closure(
        l_Array_findSomeRev_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7792_, 0, v_f_7790_);
    v___x_7793_ = l_Array_foldl___redArg___closed__9;
    v___x_7794_ = lean_array_get_size(v_as_7791_);
    v___x_7795_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(
        v___x_7793_,
        v___f_7792_,
        v_as_7791_,
        v___x_7794_,
    );
    return v___x_7795_;
}
pub unsafe fn l_Array_findSomeRev_x3f(
    mut v_00_u03b1_7796_: *mut LeanObject,
    mut v_00_u03b2_7797_: *mut LeanObject,
    mut v_f_7798_: *mut LeanObject,
    mut v_as_7799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7803_: *mut LeanObject = core::ptr::null_mut();
    v___f_7800_ = lean_alloc_closure(
        l_Array_findSomeRev_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7800_, 0, v_f_7798_);
    v___x_7801_ = l_Array_foldl___redArg___closed__9;
    v___x_7802_ = lean_array_get_size(v_as_7799_);
    v___x_7803_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(
        v___x_7801_,
        v___f_7800_,
        v_as_7799_,
        v___x_7802_,
    );
    return v___x_7803_;
}
pub unsafe fn l_Array_findRev_x3f___redArg___lam__0(
    mut v_p_7804_: *mut LeanObject,
    mut v_a_7805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7807_: u8 = 0;
    lean_inc(v_a_7805_);
    v___x_7806_ = lean_apply_1(v_p_7804_, v_a_7805_);
    v___x_7807_ = (lean_unbox(v___x_7806_) as u8);
    if v___x_7807_ == 0 {
        let mut v___x_7808_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_7805_);
        v___x_7808_ = lean_box(0);
        return v___x_7808_;
    } else {
        let mut v___x_7809_: *mut LeanObject = core::ptr::null_mut();
        v___x_7809_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_7809_, 0, v_a_7805_);
        return v___x_7809_;
    }
}
pub unsafe fn l_Array_findRev_x3f___redArg(
    mut v_p_7810_: *mut LeanObject,
    mut v_as_7811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7815_: *mut LeanObject = core::ptr::null_mut();
    v___f_7812_ = lean_alloc_closure(
        l_Array_findRev_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7812_, 0, v_p_7810_);
    v___x_7813_ = l_Array_foldl___redArg___closed__9;
    v___x_7814_ = lean_array_get_size(v_as_7811_);
    v___x_7815_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(
        v___x_7813_,
        v___f_7812_,
        v_as_7811_,
        v___x_7814_,
    );
    return v___x_7815_;
}
pub unsafe fn l_Array_findRev_x3f(
    mut v_00_u03b1_7816_: *mut LeanObject,
    mut v_p_7817_: *mut LeanObject,
    mut v_as_7818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7822_: *mut LeanObject = core::ptr::null_mut();
    v___f_7819_ = lean_alloc_closure(
        l_Array_findRev_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7819_, 0, v_p_7817_);
    v___x_7820_ = l_Array_foldl___redArg___closed__9;
    v___x_7821_ = lean_array_get_size(v_as_7818_);
    v___x_7822_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(
        v___x_7820_,
        v___f_7819_,
        v_as_7818_,
        v___x_7821_,
    );
    return v___x_7822_;
}
pub unsafe fn l_Array_findIdx_x3f_loop___redArg(
    mut v_p_7823_: *mut LeanObject,
    mut v_as_7824_: *mut LeanObject,
    mut v_j_7825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7827_: u8 = 0;
    let mut v___x_7828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7831_: u8 = 0;
    let mut v___x_7832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7835_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7826_ = lean_array_get_size(v_as_7824_);
                v___x_7827_ = lean_nat_dec_lt(v_j_7825_, v___x_7826_);
                if v___x_7827_ == 0 {
                    lean_dec(v_j_7825_);
                    lean_dec_ref(v_p_7823_);
                    v___x_7828_ = lean_box(0);
                    return v___x_7828_;
                } else {
                    v___x_7829_ = lean_array_fget_borrowed(v_as_7824_, v_j_7825_);
                    lean_inc_ref(v_p_7823_);
                    lean_inc(v___x_7829_);
                    v___x_7830_ = lean_apply_1(v_p_7823_, v___x_7829_);
                    v___x_7831_ = (lean_unbox(v___x_7830_) as u8);
                    if v___x_7831_ == 0 {
                        v___x_7832_ = lean_unsigned_to_nat(1);
                        v___x_7833_ = lean_nat_add(v_j_7825_, v___x_7832_);
                        lean_dec(v_j_7825_);
                        v_j_7825_ = v___x_7833_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_p_7823_);
                        v___x_7835_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_7835_, 0, v_j_7825_);
                        return v___x_7835_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_findIdx_x3f_loop___redArg___boxed(
    mut v_p_7836_: *mut LeanObject,
    mut v_as_7837_: *mut LeanObject,
    mut v_j_7838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7839_: *mut LeanObject = core::ptr::null_mut();
    v_res_7839_ = l_Array_findIdx_x3f_loop___redArg(v_p_7836_, v_as_7837_, v_j_7838_);
    lean_dec_ref(v_as_7837_);
    return v_res_7839_;
}
pub unsafe fn l_Array_findIdx_x3f_loop(
    mut v_00_u03b1_7840_: *mut LeanObject,
    mut v_p_7841_: *mut LeanObject,
    mut v_as_7842_: *mut LeanObject,
    mut v_j_7843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7844_: *mut LeanObject = core::ptr::null_mut();
    v___x_7844_ = l_Array_findIdx_x3f_loop___redArg(v_p_7841_, v_as_7842_, v_j_7843_);
    return v___x_7844_;
}
pub unsafe fn l_Array_findIdx_x3f_loop___boxed(
    mut v_00_u03b1_7845_: *mut LeanObject,
    mut v_p_7846_: *mut LeanObject,
    mut v_as_7847_: *mut LeanObject,
    mut v_j_7848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7849_: *mut LeanObject = core::ptr::null_mut();
    v_res_7849_ = l_Array_findIdx_x3f_loop(v_00_u03b1_7845_, v_p_7846_, v_as_7847_, v_j_7848_);
    lean_dec_ref(v_as_7847_);
    return v_res_7849_;
}
pub unsafe fn l_Array_findIdx_x3f___redArg(
    mut v_p_7850_: *mut LeanObject,
    mut v_as_7851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7853_: *mut LeanObject = core::ptr::null_mut();
    v___x_7852_ = lean_unsigned_to_nat(0);
    v___x_7853_ = l_Array_findIdx_x3f_loop___redArg(v_p_7850_, v_as_7851_, v___x_7852_);
    return v___x_7853_;
}
pub unsafe fn l_Array_findIdx_x3f___redArg___boxed(
    mut v_p_7854_: *mut LeanObject,
    mut v_as_7855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7856_: *mut LeanObject = core::ptr::null_mut();
    v_res_7856_ = l_Array_findIdx_x3f___redArg(v_p_7854_, v_as_7855_);
    lean_dec_ref(v_as_7855_);
    return v_res_7856_;
}
pub unsafe fn l_Array_findIdx_x3f(
    mut v_00_u03b1_7857_: *mut LeanObject,
    mut v_p_7858_: *mut LeanObject,
    mut v_as_7859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7861_: *mut LeanObject = core::ptr::null_mut();
    v___x_7860_ = lean_unsigned_to_nat(0);
    v___x_7861_ = l_Array_findIdx_x3f_loop___redArg(v_p_7858_, v_as_7859_, v___x_7860_);
    return v___x_7861_;
}
pub unsafe fn l_Array_findIdx_x3f___boxed(
    mut v_00_u03b1_7862_: *mut LeanObject,
    mut v_p_7863_: *mut LeanObject,
    mut v_as_7864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7865_: *mut LeanObject = core::ptr::null_mut();
    v_res_7865_ = l_Array_findIdx_x3f(v_00_u03b1_7862_, v_p_7863_, v_as_7864_);
    lean_dec_ref(v_as_7864_);
    return v_res_7865_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(
    mut v_p_7866_: *mut LeanObject,
    mut v_as_7867_: *mut LeanObject,
    mut v_j_7868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7870_: u8 = 0;
    let mut v___x_7871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7874_: u8 = 0;
    let mut v___x_7875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7878_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7869_ = lean_array_get_size(v_as_7867_);
                v___x_7870_ = lean_nat_dec_lt(v_j_7868_, v___x_7869_);
                if v___x_7870_ == 0 {
                    lean_dec(v_j_7868_);
                    lean_dec_ref(v_p_7866_);
                    v___x_7871_ = lean_box(0);
                    return v___x_7871_;
                } else {
                    v___x_7872_ = lean_array_fget_borrowed(v_as_7867_, v_j_7868_);
                    lean_inc_ref(v_p_7866_);
                    lean_inc(v___x_7872_);
                    v___x_7873_ = lean_apply_1(v_p_7866_, v___x_7872_);
                    v___x_7874_ = (lean_unbox(v___x_7873_) as u8);
                    if v___x_7874_ == 0 {
                        v___x_7875_ = lean_unsigned_to_nat(1);
                        v___x_7876_ = lean_nat_add(v_j_7868_, v___x_7875_);
                        lean_dec(v_j_7868_);
                        v_j_7868_ = v___x_7876_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_p_7866_);
                        v___x_7878_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_7878_, 0, v_j_7868_);
                        return v___x_7878_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg___boxed(
    mut v_p_7879_: *mut LeanObject,
    mut v_as_7880_: *mut LeanObject,
    mut v_j_7881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7882_: *mut LeanObject = core::ptr::null_mut();
    v_res_7882_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(
        v_p_7879_, v_as_7880_, v_j_7881_,
    );
    lean_dec_ref(v_as_7880_);
    return v_res_7882_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(
    mut v_00_u03b1_7883_: *mut LeanObject,
    mut v_p_7884_: *mut LeanObject,
    mut v_as_7885_: *mut LeanObject,
    mut v_j_7886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7887_: *mut LeanObject = core::ptr::null_mut();
    v___x_7887_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(
        v_p_7884_, v_as_7885_, v_j_7886_,
    );
    return v___x_7887_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___boxed(
    mut v_00_u03b1_7888_: *mut LeanObject,
    mut v_p_7889_: *mut LeanObject,
    mut v_as_7890_: *mut LeanObject,
    mut v_j_7891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7892_: *mut LeanObject = core::ptr::null_mut();
    v_res_7892_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(
        v_00_u03b1_7888_,
        v_p_7889_,
        v_as_7890_,
        v_j_7891_,
    );
    lean_dec_ref(v_as_7890_);
    return v_res_7892_;
}
pub unsafe fn l_Array_findFinIdx_x3f___redArg(
    mut v_p_7893_: *mut LeanObject,
    mut v_as_7894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7896_: *mut LeanObject = core::ptr::null_mut();
    v___x_7895_ = lean_unsigned_to_nat(0);
    v___x_7896_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(
        v_p_7893_,
        v_as_7894_,
        v___x_7895_,
    );
    return v___x_7896_;
}
pub unsafe fn l_Array_findFinIdx_x3f___redArg___boxed(
    mut v_p_7897_: *mut LeanObject,
    mut v_as_7898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7899_: *mut LeanObject = core::ptr::null_mut();
    v_res_7899_ = l_Array_findFinIdx_x3f___redArg(v_p_7897_, v_as_7898_);
    lean_dec_ref(v_as_7898_);
    return v_res_7899_;
}
pub unsafe fn l_Array_findFinIdx_x3f(
    mut v_00_u03b1_7900_: *mut LeanObject,
    mut v_p_7901_: *mut LeanObject,
    mut v_as_7902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7904_: *mut LeanObject = core::ptr::null_mut();
    v___x_7903_ = lean_unsigned_to_nat(0);
    v___x_7904_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(
        v_p_7901_,
        v_as_7902_,
        v___x_7903_,
    );
    return v___x_7904_;
}
pub unsafe fn l_Array_findFinIdx_x3f___boxed(
    mut v_00_u03b1_7905_: *mut LeanObject,
    mut v_p_7906_: *mut LeanObject,
    mut v_as_7907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7908_: *mut LeanObject = core::ptr::null_mut();
    v_res_7908_ = l_Array_findFinIdx_x3f(v_00_u03b1_7905_, v_p_7906_, v_as_7907_);
    lean_dec_ref(v_as_7907_);
    return v_res_7908_;
}
pub unsafe fn l_Array_findIdx___redArg(
    mut v_p_7909_: *mut LeanObject,
    mut v_as_7910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7912_: *mut LeanObject = core::ptr::null_mut();
    v___x_7911_ = lean_unsigned_to_nat(0);
    v___x_7912_ = l_Array_findIdx_x3f_loop___redArg(v_p_7909_, v_as_7910_, v___x_7911_);
    if lean_obj_tag(v___x_7912_) == 0 {
        let mut v___x_7913_: *mut LeanObject = core::ptr::null_mut();
        v___x_7913_ = lean_array_get_size(v_as_7910_);
        return v___x_7913_;
    } else {
        let mut v_val_7914_: *mut LeanObject = core::ptr::null_mut();
        v_val_7914_ = lean_ctor_get(v___x_7912_, 0);
        lean_inc(v_val_7914_);
        lean_dec_ref_known(v___x_7912_, 1);
        return v_val_7914_;
    }
}
pub unsafe fn l_Array_findIdx___redArg___boxed(
    mut v_p_7915_: *mut LeanObject,
    mut v_as_7916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7917_: *mut LeanObject = core::ptr::null_mut();
    v_res_7917_ = l_Array_findIdx___redArg(v_p_7915_, v_as_7916_);
    lean_dec_ref(v_as_7916_);
    return v_res_7917_;
}
pub unsafe fn l_Array_findIdx(
    mut v_00_u03b1_7918_: *mut LeanObject,
    mut v_p_7919_: *mut LeanObject,
    mut v_as_7920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7922_: *mut LeanObject = core::ptr::null_mut();
    v___x_7921_ = lean_unsigned_to_nat(0);
    v___x_7922_ = l_Array_findIdx_x3f_loop___redArg(v_p_7919_, v_as_7920_, v___x_7921_);
    if lean_obj_tag(v___x_7922_) == 0 {
        let mut v___x_7923_: *mut LeanObject = core::ptr::null_mut();
        v___x_7923_ = lean_array_get_size(v_as_7920_);
        return v___x_7923_;
    } else {
        let mut v_val_7924_: *mut LeanObject = core::ptr::null_mut();
        v_val_7924_ = lean_ctor_get(v___x_7922_, 0);
        lean_inc(v_val_7924_);
        lean_dec_ref_known(v___x_7922_, 1);
        return v_val_7924_;
    }
}
pub unsafe fn l_Array_findIdx___boxed(
    mut v_00_u03b1_7925_: *mut LeanObject,
    mut v_p_7926_: *mut LeanObject,
    mut v_as_7927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7928_: *mut LeanObject = core::ptr::null_mut();
    v_res_7928_ = l_Array_findIdx(v_00_u03b1_7925_, v_p_7926_, v_as_7927_);
    lean_dec_ref(v_as_7927_);
    return v_res_7928_;
}
pub unsafe fn l_Array_idxOfAux___redArg(
    mut v_inst_7929_: *mut LeanObject,
    mut v_xs_7930_: *mut LeanObject,
    mut v_v_7931_: *mut LeanObject,
    mut v_i_7932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7934_: u8 = 0;
    let mut v___x_7935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7938_: u8 = 0;
    let mut v___x_7939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7942_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7933_ = lean_array_get_size(v_xs_7930_);
                v___x_7934_ = lean_nat_dec_lt(v_i_7932_, v___x_7933_);
                if v___x_7934_ == 0 {
                    lean_dec(v_i_7932_);
                    lean_dec(v_v_7931_);
                    lean_dec_ref(v_inst_7929_);
                    v___x_7935_ = lean_box(0);
                    return v___x_7935_;
                } else {
                    v___x_7936_ = lean_array_fget_borrowed(v_xs_7930_, v_i_7932_);
                    lean_inc_ref(v_inst_7929_);
                    lean_inc(v_v_7931_);
                    lean_inc(v___x_7936_);
                    v___x_7937_ = lean_apply_2(v_inst_7929_, v___x_7936_, v_v_7931_);
                    v___x_7938_ = (lean_unbox(v___x_7937_) as u8);
                    if v___x_7938_ == 0 {
                        v___x_7939_ = lean_unsigned_to_nat(1);
                        v___x_7940_ = lean_nat_add(v_i_7932_, v___x_7939_);
                        lean_dec(v_i_7932_);
                        v_i_7932_ = v___x_7940_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_v_7931_);
                        lean_dec_ref(v_inst_7929_);
                        v___x_7942_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_7942_, 0, v_i_7932_);
                        return v___x_7942_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___redArg___boxed(
    mut v_inst_7943_: *mut LeanObject,
    mut v_xs_7944_: *mut LeanObject,
    mut v_v_7945_: *mut LeanObject,
    mut v_i_7946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7947_: *mut LeanObject = core::ptr::null_mut();
    v_res_7947_ = l_Array_idxOfAux___redArg(v_inst_7943_, v_xs_7944_, v_v_7945_, v_i_7946_);
    lean_dec_ref(v_xs_7944_);
    return v_res_7947_;
}
pub unsafe fn l_Array_idxOfAux(
    mut v_00_u03b1_7948_: *mut LeanObject,
    mut v_inst_7949_: *mut LeanObject,
    mut v_xs_7950_: *mut LeanObject,
    mut v_v_7951_: *mut LeanObject,
    mut v_i_7952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7953_: *mut LeanObject = core::ptr::null_mut();
    v___x_7953_ = l_Array_idxOfAux___redArg(v_inst_7949_, v_xs_7950_, v_v_7951_, v_i_7952_);
    return v___x_7953_;
}
pub unsafe fn l_Array_idxOfAux___boxed(
    mut v_00_u03b1_7954_: *mut LeanObject,
    mut v_inst_7955_: *mut LeanObject,
    mut v_xs_7956_: *mut LeanObject,
    mut v_v_7957_: *mut LeanObject,
    mut v_i_7958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7959_: *mut LeanObject = core::ptr::null_mut();
    v_res_7959_ = l_Array_idxOfAux(
        v_00_u03b1_7954_,
        v_inst_7955_,
        v_xs_7956_,
        v_v_7957_,
        v_i_7958_,
    );
    lean_dec_ref(v_xs_7956_);
    return v_res_7959_;
}
pub unsafe fn l_Array_finIdxOf_x3f___redArg(
    mut v_inst_7960_: *mut LeanObject,
    mut v_xs_7961_: *mut LeanObject,
    mut v_v_7962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7964_: *mut LeanObject = core::ptr::null_mut();
    v___x_7963_ = lean_unsigned_to_nat(0);
    v___x_7964_ = l_Array_idxOfAux___redArg(v_inst_7960_, v_xs_7961_, v_v_7962_, v___x_7963_);
    return v___x_7964_;
}
pub unsafe fn l_Array_finIdxOf_x3f___redArg___boxed(
    mut v_inst_7965_: *mut LeanObject,
    mut v_xs_7966_: *mut LeanObject,
    mut v_v_7967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7968_: *mut LeanObject = core::ptr::null_mut();
    v_res_7968_ = l_Array_finIdxOf_x3f___redArg(v_inst_7965_, v_xs_7966_, v_v_7967_);
    lean_dec_ref(v_xs_7966_);
    return v_res_7968_;
}
pub unsafe fn l_Array_finIdxOf_x3f(
    mut v_00_u03b1_7969_: *mut LeanObject,
    mut v_inst_7970_: *mut LeanObject,
    mut v_xs_7971_: *mut LeanObject,
    mut v_v_7972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7973_: *mut LeanObject = core::ptr::null_mut();
    v___x_7973_ = l_Array_finIdxOf_x3f___redArg(v_inst_7970_, v_xs_7971_, v_v_7972_);
    return v___x_7973_;
}
pub unsafe fn l_Array_finIdxOf_x3f___boxed(
    mut v_00_u03b1_7974_: *mut LeanObject,
    mut v_inst_7975_: *mut LeanObject,
    mut v_xs_7976_: *mut LeanObject,
    mut v_v_7977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7978_: *mut LeanObject = core::ptr::null_mut();
    v_res_7978_ = l_Array_finIdxOf_x3f(v_00_u03b1_7974_, v_inst_7975_, v_xs_7976_, v_v_7977_);
    lean_dec_ref(v_xs_7976_);
    return v_res_7978_;
}
pub unsafe fn l_Array_idxOf___redArg___lam__0(
    mut v_inst_7979_: *mut LeanObject,
    mut v_a_7980_: *mut LeanObject,
    mut v_x_7981_: *mut LeanObject,
) -> u8 {
    let mut v___x_7982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7983_: u8 = 0;
    v___x_7982_ = lean_apply_2(v_inst_7979_, v_x_7981_, v_a_7980_);
    v___x_7983_ = (lean_unbox(v___x_7982_) as u8);
    return v___x_7983_;
}
pub unsafe fn l_Array_idxOf___redArg___lam__0___boxed(
    mut v_inst_7984_: *mut LeanObject,
    mut v_a_7985_: *mut LeanObject,
    mut v_x_7986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7987_: u8 = 0;
    let mut v_r_7988_: *mut LeanObject = core::ptr::null_mut();
    v_res_7987_ = l_Array_idxOf___redArg___lam__0(v_inst_7984_, v_a_7985_, v_x_7986_);
    v_r_7988_ = lean_box((v_res_7987_) as usize);
    return v_r_7988_;
}
pub unsafe fn l_Array_idxOf___redArg(
    mut v_inst_7989_: *mut LeanObject,
    mut v_a_7990_: *mut LeanObject,
    mut v_as_7991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7994_: *mut LeanObject = core::ptr::null_mut();
    v___f_7992_ = lean_alloc_closure(
        l_Array_idxOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_7992_, 0, v_inst_7989_);
    lean_closure_set(v___f_7992_, 1, v_a_7990_);
    v___x_7993_ = lean_unsigned_to_nat(0);
    v___x_7994_ = l_Array_findIdx_x3f_loop___redArg(v___f_7992_, v_as_7991_, v___x_7993_);
    if lean_obj_tag(v___x_7994_) == 0 {
        let mut v___x_7995_: *mut LeanObject = core::ptr::null_mut();
        v___x_7995_ = lean_array_get_size(v_as_7991_);
        return v___x_7995_;
    } else {
        let mut v_val_7996_: *mut LeanObject = core::ptr::null_mut();
        v_val_7996_ = lean_ctor_get(v___x_7994_, 0);
        lean_inc(v_val_7996_);
        lean_dec_ref_known(v___x_7994_, 1);
        return v_val_7996_;
    }
}
pub unsafe fn l_Array_idxOf___redArg___boxed(
    mut v_inst_7997_: *mut LeanObject,
    mut v_a_7998_: *mut LeanObject,
    mut v_as_7999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8000_: *mut LeanObject = core::ptr::null_mut();
    v_res_8000_ = l_Array_idxOf___redArg(v_inst_7997_, v_a_7998_, v_as_7999_);
    lean_dec_ref(v_as_7999_);
    return v_res_8000_;
}
pub unsafe fn l_Array_idxOf(
    mut v_00_u03b1_8001_: *mut LeanObject,
    mut v_inst_8002_: *mut LeanObject,
    mut v_a_8003_: *mut LeanObject,
    mut v_as_8004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8005_: *mut LeanObject = core::ptr::null_mut();
    v___x_8005_ = l_Array_idxOf___redArg(v_inst_8002_, v_a_8003_, v_as_8004_);
    return v___x_8005_;
}
pub unsafe fn l_Array_idxOf___boxed(
    mut v_00_u03b1_8006_: *mut LeanObject,
    mut v_inst_8007_: *mut LeanObject,
    mut v_a_8008_: *mut LeanObject,
    mut v_as_8009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8010_: *mut LeanObject = core::ptr::null_mut();
    v_res_8010_ = l_Array_idxOf(v_00_u03b1_8006_, v_inst_8007_, v_a_8008_, v_as_8009_);
    lean_dec_ref(v_as_8009_);
    return v_res_8010_;
}
pub unsafe fn l_Array_idxOf_x3f___redArg(
    mut v_inst_8011_: *mut LeanObject,
    mut v_xs_8012_: *mut LeanObject,
    mut v_v_8013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8019_: u8 = 0;
    let mut v___x_8021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8023_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8014_ = l_Array_finIdxOf_x3f___redArg(v_inst_8011_, v_xs_8012_, v_v_8013_);
                if lean_obj_tag(v___x_8014_) == 0 {
                    v___x_8015_ = lean_box(0);
                    return v___x_8015_;
                } else {
                    v_val_8016_ = lean_ctor_get(v___x_8014_, 0);
                    v_isSharedCheck_8023_ = (!lean_is_exclusive(v___x_8014_)) as u8;
                    if v_isSharedCheck_8023_ == 0 {
                        v___x_8018_ = v___x_8014_;
                        v_isShared_8019_ = v_isSharedCheck_8023_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_8016_);
                        lean_dec(v___x_8014_);
                        v___x_8018_ = lean_box(0);
                        v_isShared_8019_ = v_isSharedCheck_8023_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8019_ == 0 {
                    v___x_8021_ = v___x_8018_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8022_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8022_, 0, v_val_8016_);
                    v___x_8021_ = v_reuseFailAlloc_8022_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOf_x3f___redArg___boxed(
    mut v_inst_8024_: *mut LeanObject,
    mut v_xs_8025_: *mut LeanObject,
    mut v_v_8026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8027_: *mut LeanObject = core::ptr::null_mut();
    v_res_8027_ = l_Array_idxOf_x3f___redArg(v_inst_8024_, v_xs_8025_, v_v_8026_);
    lean_dec_ref(v_xs_8025_);
    return v_res_8027_;
}
pub unsafe fn l_Array_idxOf_x3f(
    mut v_00_u03b1_8028_: *mut LeanObject,
    mut v_inst_8029_: *mut LeanObject,
    mut v_xs_8030_: *mut LeanObject,
    mut v_v_8031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8032_: *mut LeanObject = core::ptr::null_mut();
    v___x_8032_ = l_Array_idxOf_x3f___redArg(v_inst_8029_, v_xs_8030_, v_v_8031_);
    return v___x_8032_;
}
pub unsafe fn l_Array_idxOf_x3f___boxed(
    mut v_00_u03b1_8033_: *mut LeanObject,
    mut v_inst_8034_: *mut LeanObject,
    mut v_xs_8035_: *mut LeanObject,
    mut v_v_8036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8037_: *mut LeanObject = core::ptr::null_mut();
    v_res_8037_ = l_Array_idxOf_x3f(v_00_u03b1_8033_, v_inst_8034_, v_xs_8035_, v_v_8036_);
    lean_dec_ref(v_xs_8035_);
    return v_res_8037_;
}
pub unsafe fn l_Array_any___redArg___lam__0(
    mut v_p_8038_: *mut LeanObject,
    mut v_x_8039_: *mut LeanObject,
) -> u8 {
    let mut v___x_8040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8041_: u8 = 0;
    v___x_8040_ = lean_apply_1(v_p_8038_, v_x_8039_);
    v___x_8041_ = (lean_unbox(v___x_8040_) as u8);
    return v___x_8041_;
}
pub unsafe fn l_Array_any___redArg___lam__0___boxed(
    mut v_p_8042_: *mut LeanObject,
    mut v_x_8043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8044_: u8 = 0;
    let mut v_r_8045_: *mut LeanObject = core::ptr::null_mut();
    v_res_8044_ = l_Array_any___redArg___lam__0(v_p_8042_, v_x_8043_);
    v_r_8045_ = lean_box((v_res_8044_) as usize);
    return v_r_8045_;
}
pub unsafe fn l_Array_any___redArg(
    mut v_as_8046_: *mut LeanObject,
    mut v_p_8047_: *mut LeanObject,
    mut v_start_8048_: *mut LeanObject,
    mut v_stop_8049_: *mut LeanObject,
) -> u8 {
    let mut v___x_8050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8051_: u8 = 0;
    let mut v___f_8052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8055_: u8 = 0;
    let mut v___x_8056_: usize = 0;
    let mut v___x_8057_: usize = 0;
    let mut v___x_8058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8059_: u8 = 0;
    let mut v___x_8060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8061_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8050_ = l_Array_foldl___redArg___closed__9;
                v___x_8051_ = lean_nat_dec_lt(v_start_8048_, v_stop_8049_);
                if v___x_8051_ == 0 {
                    lean_dec(v_stop_8049_);
                    lean_dec_ref(v_p_8047_);
                    lean_dec_ref(v_as_8046_);
                    return v___x_8051_;
                } else {
                    v___f_8052_ = lean_alloc_closure(
                        l_Array_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_8052_, 0, v_p_8047_);
                    v___x_8060_ = lean_array_get_size(v_as_8046_);
                    v___x_8061_ = lean_nat_dec_le(v_stop_8049_, v___x_8060_);
                    if v___x_8061_ == 0 {
                        lean_dec(v_stop_8049_);
                        v___y_8054_ = v___x_8060_;
                        state = 1;
                        continue;
                    } else {
                        v___y_8054_ = v_stop_8049_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8055_ = lean_nat_dec_lt(v_start_8048_, v___y_8054_);
                if v___x_8055_ == 0 {
                    lean_dec(v___y_8054_);
                    lean_dec_ref(v___f_8052_);
                    lean_dec_ref(v_as_8046_);
                    return v___x_8055_;
                } else {
                    v___x_8056_ = lean_usize_of_nat(v_start_8048_);
                    v___x_8057_ = lean_usize_of_nat(v___y_8054_);
                    lean_dec(v___y_8054_);
                    v___x_8058_ =
                        l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(
                            v___x_8050_,
                            v___f_8052_,
                            v_as_8046_,
                            v___x_8056_,
                            v___x_8057_,
                        );
                    v___x_8059_ = (lean_unbox(v___x_8058_) as u8);
                    lean_dec(v___x_8058_);
                    return v___x_8059_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_any___redArg___boxed(
    mut v_as_8062_: *mut LeanObject,
    mut v_p_8063_: *mut LeanObject,
    mut v_start_8064_: *mut LeanObject,
    mut v_stop_8065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8066_: u8 = 0;
    let mut v_r_8067_: *mut LeanObject = core::ptr::null_mut();
    v_res_8066_ = l_Array_any___redArg(v_as_8062_, v_p_8063_, v_start_8064_, v_stop_8065_);
    lean_dec(v_start_8064_);
    v_r_8067_ = lean_box((v_res_8066_) as usize);
    return v_r_8067_;
}
pub unsafe fn l_Array_any(
    mut v_00_u03b1_8068_: *mut LeanObject,
    mut v_as_8069_: *mut LeanObject,
    mut v_p_8070_: *mut LeanObject,
    mut v_start_8071_: *mut LeanObject,
    mut v_stop_8072_: *mut LeanObject,
) -> u8 {
    let mut v___x_8073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8074_: u8 = 0;
    let mut v___f_8075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8078_: u8 = 0;
    let mut v___x_8079_: usize = 0;
    let mut v___x_8080_: usize = 0;
    let mut v___x_8081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8082_: u8 = 0;
    let mut v___x_8083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8084_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8073_ = l_Array_foldl___redArg___closed__9;
                v___x_8074_ = lean_nat_dec_lt(v_start_8071_, v_stop_8072_);
                if v___x_8074_ == 0 {
                    lean_dec(v_stop_8072_);
                    lean_dec_ref(v_p_8070_);
                    lean_dec_ref(v_as_8069_);
                    return v___x_8074_;
                } else {
                    v___f_8075_ = lean_alloc_closure(
                        l_Array_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_8075_, 0, v_p_8070_);
                    v___x_8083_ = lean_array_get_size(v_as_8069_);
                    v___x_8084_ = lean_nat_dec_le(v_stop_8072_, v___x_8083_);
                    if v___x_8084_ == 0 {
                        lean_dec(v_stop_8072_);
                        v___y_8077_ = v___x_8083_;
                        state = 1;
                        continue;
                    } else {
                        v___y_8077_ = v_stop_8072_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8078_ = lean_nat_dec_lt(v_start_8071_, v___y_8077_);
                if v___x_8078_ == 0 {
                    lean_dec(v___y_8077_);
                    lean_dec_ref(v___f_8075_);
                    lean_dec_ref(v_as_8069_);
                    return v___x_8078_;
                } else {
                    v___x_8079_ = lean_usize_of_nat(v_start_8071_);
                    v___x_8080_ = lean_usize_of_nat(v___y_8077_);
                    lean_dec(v___y_8077_);
                    v___x_8081_ =
                        l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(
                            v___x_8073_,
                            v___f_8075_,
                            v_as_8069_,
                            v___x_8079_,
                            v___x_8080_,
                        );
                    v___x_8082_ = (lean_unbox(v___x_8081_) as u8);
                    lean_dec(v___x_8081_);
                    return v___x_8082_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_any___boxed(
    mut v_00_u03b1_8085_: *mut LeanObject,
    mut v_as_8086_: *mut LeanObject,
    mut v_p_8087_: *mut LeanObject,
    mut v_start_8088_: *mut LeanObject,
    mut v_stop_8089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8090_: u8 = 0;
    let mut v_r_8091_: *mut LeanObject = core::ptr::null_mut();
    v_res_8090_ = l_Array_any(
        v_00_u03b1_8085_,
        v_as_8086_,
        v_p_8087_,
        v_start_8088_,
        v_stop_8089_,
    );
    lean_dec(v_start_8088_);
    v_r_8091_ = lean_box((v_res_8090_) as usize);
    return v_r_8091_;
}
pub unsafe fn l_Array_all___redArg___lam__0(
    mut v_p_8092_: *mut LeanObject,
    mut v___x_8093_: u8,
    mut v_v_8094_: *mut LeanObject,
) -> u8 {
    let mut v___x_8095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8096_: u8 = 0;
    v___x_8095_ = lean_apply_1(v_p_8092_, v_v_8094_);
    v___x_8096_ = (lean_unbox(v___x_8095_) as u8);
    if v___x_8096_ == 0 {
        return v___x_8093_;
    } else {
        let mut v___x_8097_: u8 = 0;
        v___x_8097_ = 0;
        return v___x_8097_;
    }
}
pub unsafe fn l_Array_all___redArg___lam__0___boxed(
    mut v_p_8098_: *mut LeanObject,
    mut v___x_8099_: *mut LeanObject,
    mut v_v_8100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_339__boxed_8101_: u8 = 0;
    let mut v_res_8102_: u8 = 0;
    let mut v_r_8103_: *mut LeanObject = core::ptr::null_mut();
    v___x_339__boxed_8101_ = (lean_unbox(v___x_8099_) as u8);
    v_res_8102_ = l_Array_all___redArg___lam__0(v_p_8098_, v___x_339__boxed_8101_, v_v_8100_);
    v_r_8103_ = lean_box((v_res_8102_) as usize);
    return v_r_8103_;
}
pub unsafe fn l_Array_all___redArg(
    mut v_as_8104_: *mut LeanObject,
    mut v_p_8105_: *mut LeanObject,
    mut v_start_8106_: *mut LeanObject,
    mut v_stop_8107_: *mut LeanObject,
) -> u8 {
    let mut v___x_8108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8109_: u8 = 0;
    let mut v___x_8110_: u8 = 0;
    let mut v___x_8111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8115_: u8 = 0;
    let mut v___x_8116_: usize = 0;
    let mut v___x_8117_: usize = 0;
    let mut v___x_8118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8119_: u8 = 0;
    let mut v___x_8120_: u8 = 0;
    let mut v___x_8121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8108_ = l_Array_foldl___redArg___closed__9;
                v___x_8109_ = lean_nat_dec_lt(v_start_8106_, v_stop_8107_);
                if v___x_8109_ == 0 {
                    lean_dec(v_stop_8107_);
                    lean_dec_ref(v_p_8105_);
                    lean_dec_ref(v_as_8104_);
                    v___x_8110_ = 1;
                    return v___x_8110_;
                } else {
                    v___x_8111_ = lean_box((v___x_8109_) as usize);
                    v___f_8112_ = lean_alloc_closure(
                        l_Array_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    lean_closure_set(v___f_8112_, 0, v_p_8105_);
                    lean_closure_set(v___f_8112_, 1, v___x_8111_);
                    v___x_8121_ = lean_array_get_size(v_as_8104_);
                    v___x_8122_ = lean_nat_dec_le(v_stop_8107_, v___x_8121_);
                    if v___x_8122_ == 0 {
                        lean_dec(v_stop_8107_);
                        v___y_8114_ = v___x_8121_;
                        state = 1;
                        continue;
                    } else {
                        v___y_8114_ = v_stop_8107_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8115_ = lean_nat_dec_lt(v_start_8106_, v___y_8114_);
                if v___x_8115_ == 0 {
                    lean_dec(v___y_8114_);
                    lean_dec_ref(v___f_8112_);
                    lean_dec_ref(v_as_8104_);
                    return v___x_8109_;
                } else {
                    v___x_8116_ = lean_usize_of_nat(v_start_8106_);
                    v___x_8117_ = lean_usize_of_nat(v___y_8114_);
                    lean_dec(v___y_8114_);
                    v___x_8118_ =
                        l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(
                            v___x_8108_,
                            v___f_8112_,
                            v_as_8104_,
                            v___x_8116_,
                            v___x_8117_,
                        );
                    v___x_8119_ = (lean_unbox(v___x_8118_) as u8);
                    lean_dec(v___x_8118_);
                    if v___x_8119_ == 0 {
                        return v___x_8115_;
                    } else {
                        v___x_8120_ = 0;
                        return v___x_8120_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_all___redArg___boxed(
    mut v_as_8123_: *mut LeanObject,
    mut v_p_8124_: *mut LeanObject,
    mut v_start_8125_: *mut LeanObject,
    mut v_stop_8126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8127_: u8 = 0;
    let mut v_r_8128_: *mut LeanObject = core::ptr::null_mut();
    v_res_8127_ = l_Array_all___redArg(v_as_8123_, v_p_8124_, v_start_8125_, v_stop_8126_);
    lean_dec(v_start_8125_);
    v_r_8128_ = lean_box((v_res_8127_) as usize);
    return v_r_8128_;
}
pub unsafe fn l_Array_all(
    mut v_00_u03b1_8129_: *mut LeanObject,
    mut v_as_8130_: *mut LeanObject,
    mut v_p_8131_: *mut LeanObject,
    mut v_start_8132_: *mut LeanObject,
    mut v_stop_8133_: *mut LeanObject,
) -> u8 {
    let mut v___x_8134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8135_: u8 = 0;
    let mut v___x_8136_: u8 = 0;
    let mut v___x_8137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8141_: u8 = 0;
    let mut v___x_8142_: usize = 0;
    let mut v___x_8143_: usize = 0;
    let mut v___x_8144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8145_: u8 = 0;
    let mut v___x_8146_: u8 = 0;
    let mut v___x_8147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8148_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8134_ = l_Array_foldl___redArg___closed__9;
                v___x_8135_ = lean_nat_dec_lt(v_start_8132_, v_stop_8133_);
                if v___x_8135_ == 0 {
                    lean_dec(v_stop_8133_);
                    lean_dec_ref(v_p_8131_);
                    lean_dec_ref(v_as_8130_);
                    v___x_8136_ = 1;
                    return v___x_8136_;
                } else {
                    v___x_8137_ = lean_box((v___x_8135_) as usize);
                    v___f_8138_ = lean_alloc_closure(
                        l_Array_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    lean_closure_set(v___f_8138_, 0, v_p_8131_);
                    lean_closure_set(v___f_8138_, 1, v___x_8137_);
                    v___x_8147_ = lean_array_get_size(v_as_8130_);
                    v___x_8148_ = lean_nat_dec_le(v_stop_8133_, v___x_8147_);
                    if v___x_8148_ == 0 {
                        lean_dec(v_stop_8133_);
                        v___y_8140_ = v___x_8147_;
                        state = 1;
                        continue;
                    } else {
                        v___y_8140_ = v_stop_8133_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8141_ = lean_nat_dec_lt(v_start_8132_, v___y_8140_);
                if v___x_8141_ == 0 {
                    lean_dec(v___y_8140_);
                    lean_dec_ref(v___f_8138_);
                    lean_dec_ref(v_as_8130_);
                    return v___x_8135_;
                } else {
                    v___x_8142_ = lean_usize_of_nat(v_start_8132_);
                    v___x_8143_ = lean_usize_of_nat(v___y_8140_);
                    lean_dec(v___y_8140_);
                    v___x_8144_ =
                        l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(
                            v___x_8134_,
                            v___f_8138_,
                            v_as_8130_,
                            v___x_8142_,
                            v___x_8143_,
                        );
                    v___x_8145_ = (lean_unbox(v___x_8144_) as u8);
                    lean_dec(v___x_8144_);
                    if v___x_8145_ == 0 {
                        return v___x_8141_;
                    } else {
                        v___x_8146_ = 0;
                        return v___x_8146_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_all___boxed(
    mut v_00_u03b1_8149_: *mut LeanObject,
    mut v_as_8150_: *mut LeanObject,
    mut v_p_8151_: *mut LeanObject,
    mut v_start_8152_: *mut LeanObject,
    mut v_stop_8153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8154_: u8 = 0;
    let mut v_r_8155_: *mut LeanObject = core::ptr::null_mut();
    v_res_8154_ = l_Array_all(
        v_00_u03b1_8149_,
        v_as_8150_,
        v_p_8151_,
        v_start_8152_,
        v_stop_8153_,
    );
    lean_dec(v_start_8152_);
    v_r_8155_ = lean_box((v_res_8154_) as usize);
    return v_r_8155_;
}
pub unsafe fn l_Array_contains___redArg___lam__0(
    mut v_inst_8156_: *mut LeanObject,
    mut v_a_8157_: *mut LeanObject,
    mut v_x_8158_: *mut LeanObject,
) -> u8 {
    let mut v___x_8159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8160_: u8 = 0;
    v___x_8159_ = lean_apply_2(v_inst_8156_, v_a_8157_, v_x_8158_);
    v___x_8160_ = (lean_unbox(v___x_8159_) as u8);
    return v___x_8160_;
}
pub unsafe fn l_Array_contains___redArg___lam__0___boxed(
    mut v_inst_8161_: *mut LeanObject,
    mut v_a_8162_: *mut LeanObject,
    mut v_x_8163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8164_: u8 = 0;
    let mut v_r_8165_: *mut LeanObject = core::ptr::null_mut();
    v_res_8164_ = l_Array_contains___redArg___lam__0(v_inst_8161_, v_a_8162_, v_x_8163_);
    v_r_8165_ = lean_box((v_res_8164_) as usize);
    return v_r_8165_;
}
pub unsafe fn l_Array_contains___redArg(
    mut v_inst_8166_: *mut LeanObject,
    mut v_as_8167_: *mut LeanObject,
    mut v_a_8168_: *mut LeanObject,
) -> u8 {
    let mut v___x_8169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8172_: u8 = 0;
    v___x_8169_ = lean_unsigned_to_nat(0);
    v___x_8170_ = lean_array_get_size(v_as_8167_);
    v___x_8171_ = l_Array_foldl___redArg___closed__9;
    v___x_8172_ = lean_nat_dec_lt(v___x_8169_, v___x_8170_);
    if v___x_8172_ == 0 {
        lean_dec(v_a_8168_);
        lean_dec_ref(v_as_8167_);
        lean_dec_ref(v_inst_8166_);
        return v___x_8172_;
    } else {
        if v___x_8172_ == 0 {
            lean_dec(v_a_8168_);
            lean_dec_ref(v_as_8167_);
            lean_dec_ref(v_inst_8166_);
            return v___x_8172_;
        } else {
            let mut v___f_8173_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8174_: usize = 0;
            let mut v___x_8175_: usize = 0;
            let mut v___x_8176_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8177_: u8 = 0;
            v___f_8173_ = lean_alloc_closure(
                l_Array_contains___redArg___lam__0___boxed as *mut core::ffi::c_void,
                3,
                2,
            );
            lean_closure_set(v___f_8173_, 0, v_inst_8166_);
            lean_closure_set(v___f_8173_, 1, v_a_8168_);
            v___x_8174_ = 0usize;
            v___x_8175_ = lean_usize_of_nat(v___x_8170_);
            v___x_8176_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(
                v___x_8171_,
                v___f_8173_,
                v_as_8167_,
                v___x_8174_,
                v___x_8175_,
            );
            v___x_8177_ = (lean_unbox(v___x_8176_) as u8);
            lean_dec(v___x_8176_);
            return v___x_8177_;
        }
    }
}
pub unsafe fn l_Array_contains___redArg___boxed(
    mut v_inst_8178_: *mut LeanObject,
    mut v_as_8179_: *mut LeanObject,
    mut v_a_8180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8181_: u8 = 0;
    let mut v_r_8182_: *mut LeanObject = core::ptr::null_mut();
    v_res_8181_ = l_Array_contains___redArg(v_inst_8178_, v_as_8179_, v_a_8180_);
    v_r_8182_ = lean_box((v_res_8181_) as usize);
    return v_r_8182_;
}
pub unsafe fn l_Array_contains(
    mut v_00_u03b1_8183_: *mut LeanObject,
    mut v_inst_8184_: *mut LeanObject,
    mut v_as_8185_: *mut LeanObject,
    mut v_a_8186_: *mut LeanObject,
) -> u8 {
    let mut v___x_8187_: u8 = 0;
    v___x_8187_ = l_Array_contains___redArg(v_inst_8184_, v_as_8185_, v_a_8186_);
    return v___x_8187_;
}
pub unsafe fn l_Array_contains___boxed(
    mut v_00_u03b1_8188_: *mut LeanObject,
    mut v_inst_8189_: *mut LeanObject,
    mut v_as_8190_: *mut LeanObject,
    mut v_a_8191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8192_: u8 = 0;
    let mut v_r_8193_: *mut LeanObject = core::ptr::null_mut();
    v_res_8192_ = l_Array_contains(v_00_u03b1_8188_, v_inst_8189_, v_as_8190_, v_a_8191_);
    v_r_8193_ = lean_box((v_res_8192_) as usize);
    return v_r_8193_;
}
pub unsafe fn l_Array_elem___redArg(
    mut v_inst_8194_: *mut LeanObject,
    mut v_a_8195_: *mut LeanObject,
    mut v_as_8196_: *mut LeanObject,
) -> u8 {
    let mut v___x_8197_: u8 = 0;
    v___x_8197_ = l_Array_contains___redArg(v_inst_8194_, v_as_8196_, v_a_8195_);
    return v___x_8197_;
}
pub unsafe fn l_Array_elem___redArg___boxed(
    mut v_inst_8198_: *mut LeanObject,
    mut v_a_8199_: *mut LeanObject,
    mut v_as_8200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8201_: u8 = 0;
    let mut v_r_8202_: *mut LeanObject = core::ptr::null_mut();
    v_res_8201_ = l_Array_elem___redArg(v_inst_8198_, v_a_8199_, v_as_8200_);
    v_r_8202_ = lean_box((v_res_8201_) as usize);
    return v_r_8202_;
}
pub unsafe fn l_Array_elem(
    mut v_00_u03b1_8203_: *mut LeanObject,
    mut v_inst_8204_: *mut LeanObject,
    mut v_a_8205_: *mut LeanObject,
    mut v_as_8206_: *mut LeanObject,
) -> u8 {
    let mut v___x_8207_: u8 = 0;
    v___x_8207_ = l_Array_contains___redArg(v_inst_8204_, v_as_8206_, v_a_8205_);
    return v___x_8207_;
}
pub unsafe fn l_Array_elem___boxed(
    mut v_00_u03b1_8208_: *mut LeanObject,
    mut v_inst_8209_: *mut LeanObject,
    mut v_a_8210_: *mut LeanObject,
    mut v_as_8211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8212_: u8 = 0;
    let mut v_r_8213_: *mut LeanObject = core::ptr::null_mut();
    v_res_8212_ = l_Array_elem(v_00_u03b1_8208_, v_inst_8209_, v_a_8210_, v_as_8211_);
    v_r_8213_ = lean_box((v_res_8212_) as usize);
    return v_r_8213_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(
    mut v_as_8214_: *mut LeanObject,
    mut v_i_8215_: usize,
    mut v_stop_8216_: usize,
    mut v_b_8217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8218_: u8 = 0;
    let mut v___x_8219_: usize = 0;
    let mut v___x_8220_: usize = 0;
    let mut v___x_8221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8222_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8218_ = lean_usize_dec_eq(v_i_8215_, v_stop_8216_);
                if v___x_8218_ == 0 {
                    v___x_8219_ = 1usize;
                    v___x_8220_ = lean_usize_sub(v_i_8215_, v___x_8219_);
                    v___x_8221_ = lean_array_uget_borrowed(v_as_8214_, v___x_8220_);
                    lean_inc(v___x_8221_);
                    v___x_8222_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_8222_, 0, v___x_8221_);
                    lean_ctor_set(v___x_8222_, 1, v_b_8217_);
                    v_i_8215_ = v___x_8220_;
                    v_b_8217_ = v___x_8222_;
                    state = 0;
                    continue;
                } else {
                    return v_b_8217_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg___boxed(
    mut v_as_8224_: *mut LeanObject,
    mut v_i_8225_: *mut LeanObject,
    mut v_stop_8226_: *mut LeanObject,
    mut v_b_8227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_8228_: usize = 0;
    let mut v_stop_boxed_8229_: usize = 0;
    let mut v_res_8230_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_8228_ = lean_unbox_usize(v_i_8225_);
    lean_dec(v_i_8225_);
    v_stop_boxed_8229_ = lean_unbox_usize(v_stop_8226_);
    lean_dec(v_stop_8226_);
    v_res_8230_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_8224_, v_i_boxed_8228_, v_stop_boxed_8229_, v_b_8227_);
    lean_dec_ref(v_as_8224_);
    return v_res_8230_;
}
pub unsafe fn l_Array_toListImpl___redArg(mut v_as_8231_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8235_: u8 = 0;
    v___x_8232_ = lean_box(0);
    v___x_8233_ = lean_array_get_size(v_as_8231_);
    v___x_8234_ = lean_unsigned_to_nat(0);
    v___x_8235_ = lean_nat_dec_lt(v___x_8234_, v___x_8233_);
    if v___x_8235_ == 0 {
        return v___x_8232_;
    } else {
        let mut v___x_8236_: usize = 0;
        let mut v___x_8237_: usize = 0;
        let mut v___x_8238_: *mut LeanObject = core::ptr::null_mut();
        v___x_8236_ = lean_usize_of_nat(v___x_8233_);
        v___x_8237_ = 0usize;
        v___x_8238_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_8231_, v___x_8236_, v___x_8237_, v___x_8232_);
        return v___x_8238_;
    }
}
pub unsafe fn l_Array_toListImpl___redArg___boxed(
    mut v_as_8239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8240_: *mut LeanObject = core::ptr::null_mut();
    v_res_8240_ = l_Array_toListImpl___redArg(v_as_8239_);
    lean_dec_ref(v_as_8239_);
    return v_res_8240_;
}
pub unsafe fn lean_array_to_list_impl(
    mut v_00_u03b1_8241_: *mut LeanObject,
    mut v_as_8242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8243_: *mut LeanObject = core::ptr::null_mut();
    v___x_8243_ = l_Array_toListImpl___redArg(v_as_8242_);
    lean_dec_ref(v_as_8242_);
    return v___x_8243_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(
    mut v_00_u03b1_8244_: *mut LeanObject,
    mut v_as_8245_: *mut LeanObject,
    mut v_i_8246_: usize,
    mut v_stop_8247_: usize,
    mut v_b_8248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8249_: *mut LeanObject = core::ptr::null_mut();
    v___x_8249_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_8245_, v_i_8246_, v_stop_8247_, v_b_8248_);
    return v___x_8249_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___boxed(
    mut v_00_u03b1_8250_: *mut LeanObject,
    mut v_as_8251_: *mut LeanObject,
    mut v_i_8252_: *mut LeanObject,
    mut v_stop_8253_: *mut LeanObject,
    mut v_b_8254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_8255_: usize = 0;
    let mut v_stop_boxed_8256_: usize = 0;
    let mut v_res_8257_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_8255_ = lean_unbox_usize(v_i_8252_);
    lean_dec(v_i_8252_);
    v_stop_boxed_8256_ = lean_unbox_usize(v_stop_8253_);
    lean_dec(v_stop_8253_);
    v_res_8257_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(v_00_u03b1_8250_, v_as_8251_, v_i_boxed_8255_, v_stop_boxed_8256_, v_b_8254_);
    lean_dec_ref(v_as_8251_);
    return v_res_8257_;
}
pub unsafe fn l_Array_toListAppend___redArg___lam__0(
    mut v_x1_8258_: *mut LeanObject,
    mut v_x2_8259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8260_: *mut LeanObject = core::ptr::null_mut();
    v___x_8260_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_8260_, 0, v_x1_8258_);
    lean_ctor_set(v___x_8260_, 1, v_x2_8259_);
    return v___x_8260_;
}
pub unsafe fn l_Array_toListAppend___redArg(
    mut v_as_8262_: *mut LeanObject,
    mut v_l_8263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8267_: u8 = 0;
    v___x_8264_ = lean_array_get_size(v_as_8262_);
    v___x_8265_ = lean_unsigned_to_nat(0);
    v___x_8266_ = l_Array_foldl___redArg___closed__9;
    v___x_8267_ = lean_nat_dec_lt(v___x_8265_, v___x_8264_);
    if v___x_8267_ == 0 {
        lean_dec_ref(v_as_8262_);
        return v_l_8263_;
    } else {
        let mut v___f_8268_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8269_: usize = 0;
        let mut v___x_8270_: usize = 0;
        let mut v___x_8271_: *mut LeanObject = core::ptr::null_mut();
        v___f_8268_ = l_Array_toListAppend___redArg___closed__0;
        v___x_8269_ = lean_usize_of_nat(v___x_8264_);
        v___x_8270_ = 0usize;
        v___x_8271_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
            v___x_8266_,
            v___f_8268_,
            v_as_8262_,
            v___x_8269_,
            v___x_8270_,
            v_l_8263_,
        );
        return v___x_8271_;
    }
}
pub unsafe fn l_Array_toListAppend(
    mut v_00_u03b1_8272_: *mut LeanObject,
    mut v_as_8273_: *mut LeanObject,
    mut v_l_8274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8278_: u8 = 0;
    v___x_8275_ = lean_array_get_size(v_as_8273_);
    v___x_8276_ = lean_unsigned_to_nat(0);
    v___x_8277_ = l_Array_foldl___redArg___closed__9;
    v___x_8278_ = lean_nat_dec_lt(v___x_8276_, v___x_8275_);
    if v___x_8278_ == 0 {
        lean_dec_ref(v_as_8273_);
        return v_l_8274_;
    } else {
        let mut v___f_8279_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8280_: usize = 0;
        let mut v___x_8281_: usize = 0;
        let mut v___x_8282_: *mut LeanObject = core::ptr::null_mut();
        v___f_8279_ = l_Array_toListAppend___redArg___closed__0;
        v___x_8280_ = lean_usize_of_nat(v___x_8275_);
        v___x_8281_ = 0usize;
        v___x_8282_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
            v___x_8277_,
            v___f_8279_,
            v_as_8273_,
            v___x_8280_,
            v___x_8281_,
            v_l_8274_,
        );
        return v___x_8282_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(
    mut v_as_8283_: *mut LeanObject,
    mut v_i_8284_: usize,
    mut v_stop_8285_: usize,
    mut v_b_8286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8287_: u8 = 0;
    let mut v___x_8288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8290_: usize = 0;
    let mut v___x_8291_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8287_ = lean_usize_dec_eq(v_i_8284_, v_stop_8285_);
                if v___x_8287_ == 0 {
                    v___x_8288_ = lean_array_uget_borrowed(v_as_8283_, v_i_8284_);
                    lean_inc(v___x_8288_);
                    v___x_8289_ = lean_array_push(v_b_8286_, v___x_8288_);
                    v___x_8290_ = 1usize;
                    v___x_8291_ = lean_usize_add(v_i_8284_, v___x_8290_);
                    v_i_8284_ = v___x_8291_;
                    v_b_8286_ = v___x_8289_;
                    state = 0;
                    continue;
                } else {
                    return v_b_8286_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg___boxed(
    mut v_as_8293_: *mut LeanObject,
    mut v_i_8294_: *mut LeanObject,
    mut v_stop_8295_: *mut LeanObject,
    mut v_b_8296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_8297_: usize = 0;
    let mut v_stop_boxed_8298_: usize = 0;
    let mut v_res_8299_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_8297_ = lean_unbox_usize(v_i_8294_);
    lean_dec(v_i_8294_);
    v_stop_boxed_8298_ = lean_unbox_usize(v_stop_8295_);
    lean_dec(v_stop_8295_);
    v_res_8299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_8293_, v_i_boxed_8297_, v_stop_boxed_8298_, v_b_8296_);
    lean_dec_ref(v_as_8293_);
    return v_res_8299_;
}
pub unsafe fn l_Array_append___redArg(
    mut v_as_8300_: *mut LeanObject,
    mut v_bs_8301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8304_: u8 = 0;
    v___x_8302_ = lean_unsigned_to_nat(0);
    v___x_8303_ = lean_array_get_size(v_bs_8301_);
    v___x_8304_ = lean_nat_dec_lt(v___x_8302_, v___x_8303_);
    if v___x_8304_ == 0 {
        return v_as_8300_;
    } else {
        let mut v___x_8305_: u8 = 0;
        v___x_8305_ = lean_nat_dec_le(v___x_8303_, v___x_8303_);
        if v___x_8305_ == 0 {
            if v___x_8304_ == 0 {
                return v_as_8300_;
            } else {
                let mut v___x_8306_: usize = 0;
                let mut v___x_8307_: usize = 0;
                let mut v___x_8308_: *mut LeanObject = core::ptr::null_mut();
                v___x_8306_ = 0usize;
                v___x_8307_ = lean_usize_of_nat(v___x_8303_);
                v___x_8308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_8301_, v___x_8306_, v___x_8307_, v_as_8300_);
                return v___x_8308_;
            }
        } else {
            let mut v___x_8309_: usize = 0;
            let mut v___x_8310_: usize = 0;
            let mut v___x_8311_: *mut LeanObject = core::ptr::null_mut();
            v___x_8309_ = 0usize;
            v___x_8310_ = lean_usize_of_nat(v___x_8303_);
            v___x_8311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_8301_, v___x_8309_, v___x_8310_, v_as_8300_);
            return v___x_8311_;
        }
    }
}
pub unsafe fn l_Array_append___redArg___boxed(
    mut v_as_8312_: *mut LeanObject,
    mut v_bs_8313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8314_: *mut LeanObject = core::ptr::null_mut();
    v_res_8314_ = l_Array_append___redArg(v_as_8312_, v_bs_8313_);
    lean_dec_ref(v_bs_8313_);
    return v_res_8314_;
}
pub unsafe fn l_Array_append(
    mut v_00_u03b1_8315_: *mut LeanObject,
    mut v_as_8316_: *mut LeanObject,
    mut v_bs_8317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8318_: *mut LeanObject = core::ptr::null_mut();
    v___x_8318_ = l_Array_append___redArg(v_as_8316_, v_bs_8317_);
    return v___x_8318_;
}
pub unsafe fn l_Array_append___boxed(
    mut v_00_u03b1_8319_: *mut LeanObject,
    mut v_as_8320_: *mut LeanObject,
    mut v_bs_8321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8322_: *mut LeanObject = core::ptr::null_mut();
    v_res_8322_ = l_Array_append(v_00_u03b1_8319_, v_as_8320_, v_bs_8321_);
    lean_dec_ref(v_bs_8321_);
    return v_res_8322_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(
    mut v_00_u03b1_8323_: *mut LeanObject,
    mut v_as_8324_: *mut LeanObject,
    mut v_i_8325_: usize,
    mut v_stop_8326_: usize,
    mut v_b_8327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8328_: *mut LeanObject = core::ptr::null_mut();
    v___x_8328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_8324_, v_i_8325_, v_stop_8326_, v_b_8327_);
    return v___x_8328_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___boxed(
    mut v_00_u03b1_8329_: *mut LeanObject,
    mut v_as_8330_: *mut LeanObject,
    mut v_i_8331_: *mut LeanObject,
    mut v_stop_8332_: *mut LeanObject,
    mut v_b_8333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_8334_: usize = 0;
    let mut v_stop_boxed_8335_: usize = 0;
    let mut v_res_8336_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_8334_ = lean_unbox_usize(v_i_8331_);
    lean_dec(v_i_8331_);
    v_stop_boxed_8335_ = lean_unbox_usize(v_stop_8332_);
    lean_dec(v_stop_8332_);
    v_res_8336_ =
        l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(
            v_00_u03b1_8329_,
            v_as_8330_,
            v_i_boxed_8334_,
            v_stop_boxed_8335_,
            v_b_8333_,
        );
    lean_dec_ref(v_as_8330_);
    return v_res_8336_;
}
pub unsafe fn l_Array_instAppend(mut v_00_u03b1_8338_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8339_: *mut LeanObject = core::ptr::null_mut();
    v___x_8339_ = l_Array_instAppend___closed__0;
    return v___x_8339_;
}
pub unsafe fn l_List_foldl___at___00Array_appendList_spec__0___redArg(
    mut v_x_8340_: *mut LeanObject,
    mut v_x_8341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_8342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_8343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8344_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_8341_) == 0 {
                    return v_x_8340_;
                } else {
                    v_head_8342_ = lean_ctor_get(v_x_8341_, 0);
                    lean_inc(v_head_8342_);
                    v_tail_8343_ = lean_ctor_get(v_x_8341_, 1);
                    lean_inc(v_tail_8343_);
                    lean_dec_ref_known(v_x_8341_, 2);
                    v___x_8344_ = lean_array_push(v_x_8340_, v_head_8342_);
                    v_x_8340_ = v___x_8344_;
                    v_x_8341_ = v_tail_8343_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_appendList___redArg(
    mut v_as_8346_: *mut LeanObject,
    mut v_bs_8347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8348_: *mut LeanObject = core::ptr::null_mut();
    v___x_8348_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_8346_, v_bs_8347_);
    return v___x_8348_;
}
pub unsafe fn l_Array_appendList(
    mut v_00_u03b1_8349_: *mut LeanObject,
    mut v_as_8350_: *mut LeanObject,
    mut v_bs_8351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8352_: *mut LeanObject = core::ptr::null_mut();
    v___x_8352_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_8350_, v_bs_8351_);
    return v___x_8352_;
}
pub unsafe fn l_List_foldl___at___00Array_appendList_spec__0(
    mut v_00_u03b1_8353_: *mut LeanObject,
    mut v_x_8354_: *mut LeanObject,
    mut v_x_8355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8356_: *mut LeanObject = core::ptr::null_mut();
    v___x_8356_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_8354_, v_x_8355_);
    return v___x_8356_;
}
pub unsafe fn l_Array_instHAppendList(mut v_00_u03b1_8358_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8359_: *mut LeanObject = core::ptr::null_mut();
    v___x_8359_ = l_Array_instHAppendList___closed__0;
    return v___x_8359_;
}
pub unsafe fn l_Array_flatMapM___redArg___lam__0(
    mut v_bs_8360_: *mut LeanObject,
    mut v_toPure_8361_: *mut LeanObject,
    mut v_____do__lift_8362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8364_: *mut LeanObject = core::ptr::null_mut();
    v___x_8363_ = l_Array_append___redArg(v_bs_8360_, v_____do__lift_8362_);
    v___x_8364_ = lean_apply_2(v_toPure_8361_, lean_box(0), v___x_8363_);
    return v___x_8364_;
}
pub unsafe fn l_Array_flatMapM___redArg___lam__0___boxed(
    mut v_bs_8365_: *mut LeanObject,
    mut v_toPure_8366_: *mut LeanObject,
    mut v_____do__lift_8367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8368_: *mut LeanObject = core::ptr::null_mut();
    v_res_8368_ =
        l_Array_flatMapM___redArg___lam__0(v_bs_8365_, v_toPure_8366_, v_____do__lift_8367_);
    lean_dec_ref(v_____do__lift_8367_);
    return v_res_8368_;
}
pub unsafe fn l_Array_flatMapM___redArg___lam__1(
    mut v_toPure_8369_: *mut LeanObject,
    mut v_f_8370_: *mut LeanObject,
    mut v_toBind_8371_: *mut LeanObject,
    mut v_bs_8372_: *mut LeanObject,
    mut v_a_8373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8376_: *mut LeanObject = core::ptr::null_mut();
    v___f_8374_ = lean_alloc_closure(
        l_Array_flatMapM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_8374_, 0, v_bs_8372_);
    lean_closure_set(v___f_8374_, 1, v_toPure_8369_);
    v___x_8375_ = lean_apply_1(v_f_8370_, v_a_8373_);
    v___x_8376_ = lean_apply_4(
        v_toBind_8371_,
        lean_box(0),
        lean_box(0),
        v___x_8375_,
        v___f_8374_,
    );
    return v___x_8376_;
}
pub unsafe fn l_Array_flatMapM___redArg(
    mut v_inst_8377_: *mut LeanObject,
    mut v_f_8378_: *mut LeanObject,
    mut v_as_8379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_8382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8386_: u8 = 0;
    v_toApplicative_8380_ = lean_ctor_get(v_inst_8377_, 0);
    v_toBind_8381_ = lean_ctor_get(v_inst_8377_, 1);
    v_toPure_8382_ = lean_ctor_get(v_toApplicative_8380_, 1);
    v___x_8383_ = lean_unsigned_to_nat(0);
    v___x_8384_ = l_Array_instEmptyCollection___closed__0;
    v___x_8385_ = lean_array_get_size(v_as_8379_);
    v___x_8386_ = lean_nat_dec_lt(v___x_8383_, v___x_8385_);
    if v___x_8386_ == 0 {
        let mut v___x_8387_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_toPure_8382_);
        lean_dec_ref(v_as_8379_);
        lean_dec(v_f_8378_);
        lean_dec_ref(v_inst_8377_);
        v___x_8387_ = lean_apply_2(v_toPure_8382_, lean_box(0), v___x_8384_);
        return v___x_8387_;
    } else {
        let mut v___f_8388_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8389_: u8 = 0;
        lean_inc(v_toBind_8381_);
        lean_inc(v_toPure_8382_);
        v___f_8388_ = lean_alloc_closure(
            l_Array_flatMapM___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            3,
        );
        lean_closure_set(v___f_8388_, 0, v_toPure_8382_);
        lean_closure_set(v___f_8388_, 1, v_f_8378_);
        lean_closure_set(v___f_8388_, 2, v_toBind_8381_);
        v___x_8389_ = lean_nat_dec_le(v___x_8385_, v___x_8385_);
        if v___x_8389_ == 0 {
            if v___x_8386_ == 0 {
                let mut v___x_8390_: *mut LeanObject = core::ptr::null_mut();
                lean_inc(v_toPure_8382_);
                lean_dec_ref(v___f_8388_);
                lean_dec_ref(v_as_8379_);
                lean_dec_ref(v_inst_8377_);
                v___x_8390_ = lean_apply_2(v_toPure_8382_, lean_box(0), v___x_8384_);
                return v___x_8390_;
            } else {
                let mut v___x_8391_: usize = 0;
                let mut v___x_8392_: usize = 0;
                let mut v___x_8393_: *mut LeanObject = core::ptr::null_mut();
                v___x_8391_ = 0usize;
                v___x_8392_ = lean_usize_of_nat(v___x_8385_);
                v___x_8393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v_inst_8377_,
                    v___f_8388_,
                    v_as_8379_,
                    v___x_8391_,
                    v___x_8392_,
                    v___x_8384_,
                );
                return v___x_8393_;
            }
        } else {
            let mut v___x_8394_: usize = 0;
            let mut v___x_8395_: usize = 0;
            let mut v___x_8396_: *mut LeanObject = core::ptr::null_mut();
            v___x_8394_ = 0usize;
            v___x_8395_ = lean_usize_of_nat(v___x_8385_);
            v___x_8396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v_inst_8377_,
                v___f_8388_,
                v_as_8379_,
                v___x_8394_,
                v___x_8395_,
                v___x_8384_,
            );
            return v___x_8396_;
        }
    }
}
pub unsafe fn l_Array_flatMapM(
    mut v_00_u03b1_8397_: *mut LeanObject,
    mut v_m_8398_: *mut LeanObject,
    mut v_00_u03b2_8399_: *mut LeanObject,
    mut v_inst_8400_: *mut LeanObject,
    mut v_f_8401_: *mut LeanObject,
    mut v_as_8402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_8405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8409_: u8 = 0;
    v_toApplicative_8403_ = lean_ctor_get(v_inst_8400_, 0);
    v_toBind_8404_ = lean_ctor_get(v_inst_8400_, 1);
    v_toPure_8405_ = lean_ctor_get(v_toApplicative_8403_, 1);
    v___x_8406_ = lean_unsigned_to_nat(0);
    v___x_8407_ = l_Array_instEmptyCollection___closed__0;
    v___x_8408_ = lean_array_get_size(v_as_8402_);
    v___x_8409_ = lean_nat_dec_lt(v___x_8406_, v___x_8408_);
    if v___x_8409_ == 0 {
        let mut v___x_8410_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_toPure_8405_);
        lean_dec_ref(v_as_8402_);
        lean_dec(v_f_8401_);
        lean_dec_ref(v_inst_8400_);
        v___x_8410_ = lean_apply_2(v_toPure_8405_, lean_box(0), v___x_8407_);
        return v___x_8410_;
    } else {
        let mut v___f_8411_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8412_: u8 = 0;
        lean_inc(v_toBind_8404_);
        lean_inc(v_toPure_8405_);
        v___f_8411_ = lean_alloc_closure(
            l_Array_flatMapM___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            3,
        );
        lean_closure_set(v___f_8411_, 0, v_toPure_8405_);
        lean_closure_set(v___f_8411_, 1, v_f_8401_);
        lean_closure_set(v___f_8411_, 2, v_toBind_8404_);
        v___x_8412_ = lean_nat_dec_le(v___x_8408_, v___x_8408_);
        if v___x_8412_ == 0 {
            if v___x_8409_ == 0 {
                let mut v___x_8413_: *mut LeanObject = core::ptr::null_mut();
                lean_inc(v_toPure_8405_);
                lean_dec_ref(v___f_8411_);
                lean_dec_ref(v_as_8402_);
                lean_dec_ref(v_inst_8400_);
                v___x_8413_ = lean_apply_2(v_toPure_8405_, lean_box(0), v___x_8407_);
                return v___x_8413_;
            } else {
                let mut v___x_8414_: usize = 0;
                let mut v___x_8415_: usize = 0;
                let mut v___x_8416_: *mut LeanObject = core::ptr::null_mut();
                v___x_8414_ = 0usize;
                v___x_8415_ = lean_usize_of_nat(v___x_8408_);
                v___x_8416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v_inst_8400_,
                    v___f_8411_,
                    v_as_8402_,
                    v___x_8414_,
                    v___x_8415_,
                    v___x_8407_,
                );
                return v___x_8416_;
            }
        } else {
            let mut v___x_8417_: usize = 0;
            let mut v___x_8418_: usize = 0;
            let mut v___x_8419_: *mut LeanObject = core::ptr::null_mut();
            v___x_8417_ = 0usize;
            v___x_8418_ = lean_usize_of_nat(v___x_8408_);
            v___x_8419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v_inst_8400_,
                v___f_8411_,
                v_as_8402_,
                v___x_8417_,
                v___x_8418_,
                v___x_8407_,
            );
            return v___x_8419_;
        }
    }
}
pub unsafe fn l_Array_flatMap___redArg___lam__0(
    mut v_f_8420_: *mut LeanObject,
    mut v_x1_8421_: *mut LeanObject,
    mut v_x2_8422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8424_: *mut LeanObject = core::ptr::null_mut();
    v___x_8423_ = lean_apply_1(v_f_8420_, v_x2_8422_);
    v___x_8424_ = l_Array_append___redArg(v_x1_8421_, v___x_8423_);
    lean_dec_ref(v___x_8423_);
    return v___x_8424_;
}
pub unsafe fn l_Array_flatMap___redArg(
    mut v_f_8425_: *mut LeanObject,
    mut v_as_8426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8431_: u8 = 0;
    v___x_8427_ = lean_unsigned_to_nat(0);
    v___x_8428_ = l_Array_instEmptyCollection___closed__0;
    v___x_8429_ = lean_array_get_size(v_as_8426_);
    v___x_8430_ = l_Array_foldl___redArg___closed__9;
    v___x_8431_ = lean_nat_dec_lt(v___x_8427_, v___x_8429_);
    if v___x_8431_ == 0 {
        lean_dec_ref(v_as_8426_);
        lean_dec_ref(v_f_8425_);
        return v___x_8428_;
    } else {
        let mut v___f_8432_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8433_: u8 = 0;
        v___f_8432_ = lean_alloc_closure(
            l_Array_flatMap___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_8432_, 0, v_f_8425_);
        v___x_8433_ = lean_nat_dec_le(v___x_8429_, v___x_8429_);
        if v___x_8433_ == 0 {
            if v___x_8431_ == 0 {
                lean_dec_ref(v___f_8432_);
                lean_dec_ref(v_as_8426_);
                return v___x_8428_;
            } else {
                let mut v___x_8434_: usize = 0;
                let mut v___x_8435_: usize = 0;
                let mut v___x_8436_: *mut LeanObject = core::ptr::null_mut();
                v___x_8434_ = 0usize;
                v___x_8435_ = lean_usize_of_nat(v___x_8429_);
                v___x_8436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v___x_8430_,
                    v___f_8432_,
                    v_as_8426_,
                    v___x_8434_,
                    v___x_8435_,
                    v___x_8428_,
                );
                return v___x_8436_;
            }
        } else {
            let mut v___x_8437_: usize = 0;
            let mut v___x_8438_: usize = 0;
            let mut v___x_8439_: *mut LeanObject = core::ptr::null_mut();
            v___x_8437_ = 0usize;
            v___x_8438_ = lean_usize_of_nat(v___x_8429_);
            v___x_8439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v___x_8430_,
                v___f_8432_,
                v_as_8426_,
                v___x_8437_,
                v___x_8438_,
                v___x_8428_,
            );
            return v___x_8439_;
        }
    }
}
pub unsafe fn l_Array_flatMap(
    mut v_00_u03b1_8440_: *mut LeanObject,
    mut v_00_u03b2_8441_: *mut LeanObject,
    mut v_f_8442_: *mut LeanObject,
    mut v_as_8443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8448_: u8 = 0;
    v___x_8444_ = lean_unsigned_to_nat(0);
    v___x_8445_ = l_Array_instEmptyCollection___closed__0;
    v___x_8446_ = lean_array_get_size(v_as_8443_);
    v___x_8447_ = l_Array_foldl___redArg___closed__9;
    v___x_8448_ = lean_nat_dec_lt(v___x_8444_, v___x_8446_);
    if v___x_8448_ == 0 {
        lean_dec_ref(v_as_8443_);
        lean_dec_ref(v_f_8442_);
        return v___x_8445_;
    } else {
        let mut v___f_8449_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8450_: u8 = 0;
        v___f_8449_ = lean_alloc_closure(
            l_Array_flatMap___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_8449_, 0, v_f_8442_);
        v___x_8450_ = lean_nat_dec_le(v___x_8446_, v___x_8446_);
        if v___x_8450_ == 0 {
            if v___x_8448_ == 0 {
                lean_dec_ref(v___f_8449_);
                lean_dec_ref(v_as_8443_);
                return v___x_8445_;
            } else {
                let mut v___x_8451_: usize = 0;
                let mut v___x_8452_: usize = 0;
                let mut v___x_8453_: *mut LeanObject = core::ptr::null_mut();
                v___x_8451_ = 0usize;
                v___x_8452_ = lean_usize_of_nat(v___x_8446_);
                v___x_8453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v___x_8447_,
                    v___f_8449_,
                    v_as_8443_,
                    v___x_8451_,
                    v___x_8452_,
                    v___x_8445_,
                );
                return v___x_8453_;
            }
        } else {
            let mut v___x_8454_: usize = 0;
            let mut v___x_8455_: usize = 0;
            let mut v___x_8456_: *mut LeanObject = core::ptr::null_mut();
            v___x_8454_ = 0usize;
            v___x_8455_ = lean_usize_of_nat(v___x_8446_);
            v___x_8456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v___x_8447_,
                v___f_8449_,
                v_as_8443_,
                v___x_8454_,
                v___x_8455_,
                v___x_8445_,
            );
            return v___x_8456_;
        }
    }
}
pub unsafe fn l_Array_flatten___redArg(mut v_xss_8458_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8463_: u8 = 0;
    v___x_8459_ = lean_unsigned_to_nat(0);
    v___x_8460_ = l_Array_instEmptyCollection___closed__0;
    v___x_8461_ = lean_array_get_size(v_xss_8458_);
    v___x_8462_ = l_Array_foldl___redArg___closed__9;
    v___x_8463_ = lean_nat_dec_lt(v___x_8459_, v___x_8461_);
    if v___x_8463_ == 0 {
        lean_dec_ref(v_xss_8458_);
        return v___x_8460_;
    } else {
        let mut v___f_8464_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8465_: u8 = 0;
        v___f_8464_ = l_Array_flatten___redArg___closed__0;
        v___x_8465_ = lean_nat_dec_le(v___x_8461_, v___x_8461_);
        if v___x_8465_ == 0 {
            if v___x_8463_ == 0 {
                lean_dec_ref(v_xss_8458_);
                return v___x_8460_;
            } else {
                let mut v___x_8466_: usize = 0;
                let mut v___x_8467_: usize = 0;
                let mut v___x_8468_: *mut LeanObject = core::ptr::null_mut();
                v___x_8466_ = 0usize;
                v___x_8467_ = lean_usize_of_nat(v___x_8461_);
                v___x_8468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v___x_8462_,
                    v___f_8464_,
                    v_xss_8458_,
                    v___x_8466_,
                    v___x_8467_,
                    v___x_8460_,
                );
                return v___x_8468_;
            }
        } else {
            let mut v___x_8469_: usize = 0;
            let mut v___x_8470_: usize = 0;
            let mut v___x_8471_: *mut LeanObject = core::ptr::null_mut();
            v___x_8469_ = 0usize;
            v___x_8470_ = lean_usize_of_nat(v___x_8461_);
            v___x_8471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v___x_8462_,
                v___f_8464_,
                v_xss_8458_,
                v___x_8469_,
                v___x_8470_,
                v___x_8460_,
            );
            return v___x_8471_;
        }
    }
}
pub unsafe fn l_Array_flatten(
    mut v_00_u03b1_8472_: *mut LeanObject,
    mut v_xss_8473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8478_: u8 = 0;
    v___x_8474_ = lean_unsigned_to_nat(0);
    v___x_8475_ = l_Array_instEmptyCollection___closed__0;
    v___x_8476_ = lean_array_get_size(v_xss_8473_);
    v___x_8477_ = l_Array_foldl___redArg___closed__9;
    v___x_8478_ = lean_nat_dec_lt(v___x_8474_, v___x_8476_);
    if v___x_8478_ == 0 {
        lean_dec_ref(v_xss_8473_);
        return v___x_8475_;
    } else {
        let mut v___f_8479_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8480_: u8 = 0;
        v___f_8479_ = l_Array_flatten___redArg___closed__0;
        v___x_8480_ = lean_nat_dec_le(v___x_8476_, v___x_8476_);
        if v___x_8480_ == 0 {
            if v___x_8478_ == 0 {
                lean_dec_ref(v_xss_8473_);
                return v___x_8475_;
            } else {
                let mut v___x_8481_: usize = 0;
                let mut v___x_8482_: usize = 0;
                let mut v___x_8483_: *mut LeanObject = core::ptr::null_mut();
                v___x_8481_ = 0usize;
                v___x_8482_ = lean_usize_of_nat(v___x_8476_);
                v___x_8483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v___x_8477_,
                    v___f_8479_,
                    v_xss_8473_,
                    v___x_8481_,
                    v___x_8482_,
                    v___x_8475_,
                );
                return v___x_8483_;
            }
        } else {
            let mut v___x_8484_: usize = 0;
            let mut v___x_8485_: usize = 0;
            let mut v___x_8486_: *mut LeanObject = core::ptr::null_mut();
            v___x_8484_ = 0usize;
            v___x_8485_ = lean_usize_of_nat(v___x_8476_);
            v___x_8486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v___x_8477_,
                v___f_8479_,
                v_xss_8473_,
                v___x_8484_,
                v___x_8485_,
                v___x_8475_,
            );
            return v___x_8486_;
        }
    }
}
pub unsafe fn l_Array_reverse_loop___redArg(
    mut v_as_8487_: *mut LeanObject,
    mut v_i_8488_: *mut LeanObject,
    mut v_j_8489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8490_: u8 = 0;
    let mut v_as_8491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8494_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8490_ = lean_nat_dec_lt(v_i_8488_, v_j_8489_);
                if v___x_8490_ == 0 {
                    lean_dec(v_j_8489_);
                    lean_dec(v_i_8488_);
                    return v_as_8487_;
                } else {
                    v_as_8491_ = lean_array_fswap(v_as_8487_, v_i_8488_, v_j_8489_);
                    v___x_8492_ = lean_unsigned_to_nat(1);
                    v___x_8493_ = lean_nat_add(v_i_8488_, v___x_8492_);
                    lean_dec(v_i_8488_);
                    v___x_8494_ = lean_nat_sub(v_j_8489_, v___x_8492_);
                    lean_dec(v_j_8489_);
                    v_as_8487_ = v_as_8491_;
                    v_i_8488_ = v___x_8493_;
                    v_j_8489_ = v___x_8494_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_reverse_loop(
    mut v_00_u03b1_8496_: *mut LeanObject,
    mut v_as_8497_: *mut LeanObject,
    mut v_i_8498_: *mut LeanObject,
    mut v_j_8499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8500_: *mut LeanObject = core::ptr::null_mut();
    v___x_8500_ = l_Array_reverse_loop___redArg(v_as_8497_, v_i_8498_, v_j_8499_);
    return v___x_8500_;
}
pub unsafe fn l_Array_reverse___redArg(mut v_as_8501_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8504_: u8 = 0;
    v___x_8502_ = lean_array_get_size(v_as_8501_);
    v___x_8503_ = lean_unsigned_to_nat(1);
    v___x_8504_ = lean_nat_dec_le(v___x_8502_, v___x_8503_);
    if v___x_8504_ == 0 {
        let mut v___x_8505_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8506_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8507_: *mut LeanObject = core::ptr::null_mut();
        v___x_8505_ = lean_unsigned_to_nat(0);
        v___x_8506_ = lean_nat_sub(v___x_8502_, v___x_8503_);
        v___x_8507_ = l_Array_reverse_loop___redArg(v_as_8501_, v___x_8505_, v___x_8506_);
        return v___x_8507_;
    } else {
        return v_as_8501_;
    }
}
pub unsafe fn l_Array_reverse(
    mut v_00_u03b1_8508_: *mut LeanObject,
    mut v_as_8509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8510_: *mut LeanObject = core::ptr::null_mut();
    v___x_8510_ = l_Array_reverse___redArg(v_as_8509_);
    return v___x_8510_;
}
pub unsafe fn l_Array_filter___redArg___lam__0(
    mut v_p_8511_: *mut LeanObject,
    mut v_x1_8512_: *mut LeanObject,
    mut v_x2_8513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8515_: u8 = 0;
    lean_inc(v_x2_8513_);
    v___x_8514_ = lean_apply_1(v_p_8511_, v_x2_8513_);
    v___x_8515_ = (lean_unbox(v___x_8514_) as u8);
    if v___x_8515_ == 0 {
        lean_dec(v_x2_8513_);
        return v_x1_8512_;
    } else {
        let mut v___x_8516_: *mut LeanObject = core::ptr::null_mut();
        v___x_8516_ = lean_array_push(v_x1_8512_, v_x2_8513_);
        return v___x_8516_;
    }
}
pub unsafe fn l_Array_filter___redArg(
    mut v_p_8519_: *mut LeanObject,
    mut v_as_8520_: *mut LeanObject,
    mut v_start_8521_: *mut LeanObject,
    mut v_stop_8522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8525_: u8 = 0;
    v___x_8523_ = l_Array_filter___redArg___closed__0;
    v___x_8524_ = l_Array_foldl___redArg___closed__9;
    v___x_8525_ = lean_nat_dec_lt(v_start_8521_, v_stop_8522_);
    if v___x_8525_ == 0 {
        lean_dec_ref(v_as_8520_);
        lean_dec_ref(v_p_8519_);
        return v___x_8523_;
    } else {
        let mut v___f_8526_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8527_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8528_: u8 = 0;
        v___f_8526_ = lean_alloc_closure(
            l_Array_filter___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_8526_, 0, v_p_8519_);
        v___x_8527_ = lean_array_get_size(v_as_8520_);
        v___x_8528_ = lean_nat_dec_le(v_stop_8522_, v___x_8527_);
        if v___x_8528_ == 0 {
            let mut v___x_8529_: u8 = 0;
            v___x_8529_ = lean_nat_dec_lt(v_start_8521_, v___x_8527_);
            if v___x_8529_ == 0 {
                lean_dec_ref(v___f_8526_);
                lean_dec_ref(v_as_8520_);
                return v___x_8523_;
            } else {
                let mut v___x_8530_: usize = 0;
                let mut v___x_8531_: usize = 0;
                let mut v___x_8532_: *mut LeanObject = core::ptr::null_mut();
                v___x_8530_ = lean_usize_of_nat(v_start_8521_);
                v___x_8531_ = lean_usize_of_nat(v___x_8527_);
                v___x_8532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v___x_8524_,
                    v___f_8526_,
                    v_as_8520_,
                    v___x_8530_,
                    v___x_8531_,
                    v___x_8523_,
                );
                return v___x_8532_;
            }
        } else {
            let mut v___x_8533_: usize = 0;
            let mut v___x_8534_: usize = 0;
            let mut v___x_8535_: *mut LeanObject = core::ptr::null_mut();
            v___x_8533_ = lean_usize_of_nat(v_start_8521_);
            v___x_8534_ = lean_usize_of_nat(v_stop_8522_);
            v___x_8535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v___x_8524_,
                v___f_8526_,
                v_as_8520_,
                v___x_8533_,
                v___x_8534_,
                v___x_8523_,
            );
            return v___x_8535_;
        }
    }
}
pub unsafe fn l_Array_filter___redArg___boxed(
    mut v_p_8536_: *mut LeanObject,
    mut v_as_8537_: *mut LeanObject,
    mut v_start_8538_: *mut LeanObject,
    mut v_stop_8539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8540_: *mut LeanObject = core::ptr::null_mut();
    v_res_8540_ = l_Array_filter___redArg(v_p_8536_, v_as_8537_, v_start_8538_, v_stop_8539_);
    lean_dec(v_stop_8539_);
    lean_dec(v_start_8538_);
    return v_res_8540_;
}
pub unsafe fn l_Array_filter(
    mut v_00_u03b1_8541_: *mut LeanObject,
    mut v_p_8542_: *mut LeanObject,
    mut v_as_8543_: *mut LeanObject,
    mut v_start_8544_: *mut LeanObject,
    mut v_stop_8545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8548_: u8 = 0;
    v___x_8546_ = l_Array_filter___redArg___closed__0;
    v___x_8547_ = l_Array_foldl___redArg___closed__9;
    v___x_8548_ = lean_nat_dec_lt(v_start_8544_, v_stop_8545_);
    if v___x_8548_ == 0 {
        lean_dec_ref(v_as_8543_);
        lean_dec_ref(v_p_8542_);
        return v___x_8546_;
    } else {
        let mut v___f_8549_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8550_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8551_: u8 = 0;
        v___f_8549_ = lean_alloc_closure(
            l_Array_filter___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_8549_, 0, v_p_8542_);
        v___x_8550_ = lean_array_get_size(v_as_8543_);
        v___x_8551_ = lean_nat_dec_le(v_stop_8545_, v___x_8550_);
        if v___x_8551_ == 0 {
            let mut v___x_8552_: u8 = 0;
            v___x_8552_ = lean_nat_dec_lt(v_start_8544_, v___x_8550_);
            if v___x_8552_ == 0 {
                lean_dec_ref(v___f_8549_);
                lean_dec_ref(v_as_8543_);
                return v___x_8546_;
            } else {
                let mut v___x_8553_: usize = 0;
                let mut v___x_8554_: usize = 0;
                let mut v___x_8555_: *mut LeanObject = core::ptr::null_mut();
                v___x_8553_ = lean_usize_of_nat(v_start_8544_);
                v___x_8554_ = lean_usize_of_nat(v___x_8550_);
                v___x_8555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v___x_8547_,
                    v___f_8549_,
                    v_as_8543_,
                    v___x_8553_,
                    v___x_8554_,
                    v___x_8546_,
                );
                return v___x_8555_;
            }
        } else {
            let mut v___x_8556_: usize = 0;
            let mut v___x_8557_: usize = 0;
            let mut v___x_8558_: *mut LeanObject = core::ptr::null_mut();
            v___x_8556_ = lean_usize_of_nat(v_start_8544_);
            v___x_8557_ = lean_usize_of_nat(v_stop_8545_);
            v___x_8558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v___x_8547_,
                v___f_8549_,
                v_as_8543_,
                v___x_8556_,
                v___x_8557_,
                v___x_8546_,
            );
            return v___x_8558_;
        }
    }
}
pub unsafe fn l_Array_filter___boxed(
    mut v_00_u03b1_8559_: *mut LeanObject,
    mut v_p_8560_: *mut LeanObject,
    mut v_as_8561_: *mut LeanObject,
    mut v_start_8562_: *mut LeanObject,
    mut v_stop_8563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8564_: *mut LeanObject = core::ptr::null_mut();
    v_res_8564_ = l_Array_filter(
        v_00_u03b1_8559_,
        v_p_8560_,
        v_as_8561_,
        v_start_8562_,
        v_stop_8563_,
    );
    lean_dec(v_stop_8563_);
    lean_dec(v_start_8562_);
    return v_res_8564_;
}
pub unsafe fn l_Array_filterM___redArg___lam__0(
    mut v_toApplicative_8565_: *mut LeanObject,
    mut v_acc_8566_: *mut LeanObject,
    mut v_a_8567_: *mut LeanObject,
    mut v_____do__lift_8568_: u8,
) -> *mut LeanObject {
    if v_____do__lift_8568_ == 0 {
        let mut v_toPure_8569_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8570_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_8567_);
        v_toPure_8569_ = lean_ctor_get(v_toApplicative_8565_, 1);
        lean_inc(v_toPure_8569_);
        lean_dec_ref(v_toApplicative_8565_);
        v___x_8570_ = lean_apply_2(v_toPure_8569_, lean_box(0), v_acc_8566_);
        return v___x_8570_;
    } else {
        let mut v_toPure_8571_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8572_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8573_: *mut LeanObject = core::ptr::null_mut();
        v_toPure_8571_ = lean_ctor_get(v_toApplicative_8565_, 1);
        lean_inc(v_toPure_8571_);
        lean_dec_ref(v_toApplicative_8565_);
        v___x_8572_ = lean_array_push(v_acc_8566_, v_a_8567_);
        v___x_8573_ = lean_apply_2(v_toPure_8571_, lean_box(0), v___x_8572_);
        return v___x_8573_;
    }
}
pub unsafe fn l_Array_filterM___redArg___lam__0___boxed(
    mut v_toApplicative_8574_: *mut LeanObject,
    mut v_acc_8575_: *mut LeanObject,
    mut v_a_8576_: *mut LeanObject,
    mut v_____do__lift_8577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_119__boxed_8578_: u8 = 0;
    let mut v_res_8579_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_119__boxed_8578_ = (lean_unbox(v_____do__lift_8577_) as u8);
    v_res_8579_ = l_Array_filterM___redArg___lam__0(
        v_toApplicative_8574_,
        v_acc_8575_,
        v_a_8576_,
        v_____do__lift_119__boxed_8578_,
    );
    return v_res_8579_;
}
pub unsafe fn l_Array_filterM___redArg___lam__1(
    mut v_toApplicative_8580_: *mut LeanObject,
    mut v_p_8581_: *mut LeanObject,
    mut v_toBind_8582_: *mut LeanObject,
    mut v_acc_8583_: *mut LeanObject,
    mut v_a_8584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8587_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_8584_);
    v___f_8585_ = lean_alloc_closure(
        l_Array_filterM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_8585_, 0, v_toApplicative_8580_);
    lean_closure_set(v___f_8585_, 1, v_acc_8583_);
    lean_closure_set(v___f_8585_, 2, v_a_8584_);
    v___x_8586_ = lean_apply_1(v_p_8581_, v_a_8584_);
    v___x_8587_ = lean_apply_4(
        v_toBind_8582_,
        lean_box(0),
        lean_box(0),
        v___x_8586_,
        v___f_8585_,
    );
    return v___x_8587_;
}
pub unsafe fn l_Array_filterM___redArg(
    mut v_inst_8588_: *mut LeanObject,
    mut v_p_8589_: *mut LeanObject,
    mut v_as_8590_: *mut LeanObject,
    mut v_start_8591_: *mut LeanObject,
    mut v_stop_8592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8596_: u8 = 0;
    v_toApplicative_8593_ = lean_ctor_get(v_inst_8588_, 0);
    v_toBind_8594_ = lean_ctor_get(v_inst_8588_, 1);
    v___x_8595_ = l_Array_filter___redArg___closed__0;
    v___x_8596_ = lean_nat_dec_lt(v_start_8591_, v_stop_8592_);
    if v___x_8596_ == 0 {
        let mut v_toPure_8597_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8598_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_toApplicative_8593_);
        lean_dec_ref(v_as_8590_);
        lean_dec(v_p_8589_);
        lean_dec_ref(v_inst_8588_);
        v_toPure_8597_ = lean_ctor_get(v_toApplicative_8593_, 1);
        lean_inc(v_toPure_8597_);
        lean_dec_ref(v_toApplicative_8593_);
        v___x_8598_ = lean_apply_2(v_toPure_8597_, lean_box(0), v___x_8595_);
        return v___x_8598_;
    } else {
        let mut v___f_8599_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8600_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8601_: u8 = 0;
        lean_inc(v_toBind_8594_);
        lean_inc_ref(v_toApplicative_8593_);
        v___f_8599_ = lean_alloc_closure(
            l_Array_filterM___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            3,
        );
        lean_closure_set(v___f_8599_, 0, v_toApplicative_8593_);
        lean_closure_set(v___f_8599_, 1, v_p_8589_);
        lean_closure_set(v___f_8599_, 2, v_toBind_8594_);
        v___x_8600_ = lean_array_get_size(v_as_8590_);
        v___x_8601_ = lean_nat_dec_le(v_stop_8592_, v___x_8600_);
        if v___x_8601_ == 0 {
            let mut v___x_8602_: u8 = 0;
            v___x_8602_ = lean_nat_dec_lt(v_start_8591_, v___x_8600_);
            if v___x_8602_ == 0 {
                let mut v_toPure_8603_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_8604_: *mut LeanObject = core::ptr::null_mut();
                lean_inc_ref(v_toApplicative_8593_);
                lean_dec_ref(v___f_8599_);
                lean_dec_ref(v_as_8590_);
                lean_dec_ref(v_inst_8588_);
                v_toPure_8603_ = lean_ctor_get(v_toApplicative_8593_, 1);
                lean_inc(v_toPure_8603_);
                lean_dec_ref(v_toApplicative_8593_);
                v___x_8604_ = lean_apply_2(v_toPure_8603_, lean_box(0), v___x_8595_);
                return v___x_8604_;
            } else {
                let mut v___x_8605_: usize = 0;
                let mut v___x_8606_: usize = 0;
                let mut v___x_8607_: *mut LeanObject = core::ptr::null_mut();
                v___x_8605_ = lean_usize_of_nat(v_start_8591_);
                v___x_8606_ = lean_usize_of_nat(v___x_8600_);
                v___x_8607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v_inst_8588_,
                    v___f_8599_,
                    v_as_8590_,
                    v___x_8605_,
                    v___x_8606_,
                    v___x_8595_,
                );
                return v___x_8607_;
            }
        } else {
            let mut v___x_8608_: usize = 0;
            let mut v___x_8609_: usize = 0;
            let mut v___x_8610_: *mut LeanObject = core::ptr::null_mut();
            v___x_8608_ = lean_usize_of_nat(v_start_8591_);
            v___x_8609_ = lean_usize_of_nat(v_stop_8592_);
            v___x_8610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v_inst_8588_,
                v___f_8599_,
                v_as_8590_,
                v___x_8608_,
                v___x_8609_,
                v___x_8595_,
            );
            return v___x_8610_;
        }
    }
}
pub unsafe fn l_Array_filterM___redArg___boxed(
    mut v_inst_8611_: *mut LeanObject,
    mut v_p_8612_: *mut LeanObject,
    mut v_as_8613_: *mut LeanObject,
    mut v_start_8614_: *mut LeanObject,
    mut v_stop_8615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8616_: *mut LeanObject = core::ptr::null_mut();
    v_res_8616_ = l_Array_filterM___redArg(
        v_inst_8611_,
        v_p_8612_,
        v_as_8613_,
        v_start_8614_,
        v_stop_8615_,
    );
    lean_dec(v_stop_8615_);
    lean_dec(v_start_8614_);
    return v_res_8616_;
}
pub unsafe fn l_Array_filterM(
    mut v_m_8617_: *mut LeanObject,
    mut v_00_u03b1_8618_: *mut LeanObject,
    mut v_inst_8619_: *mut LeanObject,
    mut v_p_8620_: *mut LeanObject,
    mut v_as_8621_: *mut LeanObject,
    mut v_start_8622_: *mut LeanObject,
    mut v_stop_8623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8627_: u8 = 0;
    v_toApplicative_8624_ = lean_ctor_get(v_inst_8619_, 0);
    v_toBind_8625_ = lean_ctor_get(v_inst_8619_, 1);
    v___x_8626_ = l_Array_filter___redArg___closed__0;
    v___x_8627_ = lean_nat_dec_lt(v_start_8622_, v_stop_8623_);
    if v___x_8627_ == 0 {
        let mut v_toPure_8628_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8629_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_toApplicative_8624_);
        lean_dec_ref(v_as_8621_);
        lean_dec(v_p_8620_);
        lean_dec_ref(v_inst_8619_);
        v_toPure_8628_ = lean_ctor_get(v_toApplicative_8624_, 1);
        lean_inc(v_toPure_8628_);
        lean_dec_ref(v_toApplicative_8624_);
        v___x_8629_ = lean_apply_2(v_toPure_8628_, lean_box(0), v___x_8626_);
        return v___x_8629_;
    } else {
        let mut v___f_8630_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8631_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8632_: u8 = 0;
        lean_inc(v_toBind_8625_);
        lean_inc_ref(v_toApplicative_8624_);
        v___f_8630_ = lean_alloc_closure(
            l_Array_filterM___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            3,
        );
        lean_closure_set(v___f_8630_, 0, v_toApplicative_8624_);
        lean_closure_set(v___f_8630_, 1, v_p_8620_);
        lean_closure_set(v___f_8630_, 2, v_toBind_8625_);
        v___x_8631_ = lean_array_get_size(v_as_8621_);
        v___x_8632_ = lean_nat_dec_le(v_stop_8623_, v___x_8631_);
        if v___x_8632_ == 0 {
            let mut v___x_8633_: u8 = 0;
            v___x_8633_ = lean_nat_dec_lt(v_start_8622_, v___x_8631_);
            if v___x_8633_ == 0 {
                let mut v_toPure_8634_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_8635_: *mut LeanObject = core::ptr::null_mut();
                lean_inc_ref(v_toApplicative_8624_);
                lean_dec_ref(v___f_8630_);
                lean_dec_ref(v_as_8621_);
                lean_dec_ref(v_inst_8619_);
                v_toPure_8634_ = lean_ctor_get(v_toApplicative_8624_, 1);
                lean_inc(v_toPure_8634_);
                lean_dec_ref(v_toApplicative_8624_);
                v___x_8635_ = lean_apply_2(v_toPure_8634_, lean_box(0), v___x_8626_);
                return v___x_8635_;
            } else {
                let mut v___x_8636_: usize = 0;
                let mut v___x_8637_: usize = 0;
                let mut v___x_8638_: *mut LeanObject = core::ptr::null_mut();
                v___x_8636_ = lean_usize_of_nat(v_start_8622_);
                v___x_8637_ = lean_usize_of_nat(v___x_8631_);
                v___x_8638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v_inst_8619_,
                    v___f_8630_,
                    v_as_8621_,
                    v___x_8636_,
                    v___x_8637_,
                    v___x_8626_,
                );
                return v___x_8638_;
            }
        } else {
            let mut v___x_8639_: usize = 0;
            let mut v___x_8640_: usize = 0;
            let mut v___x_8641_: *mut LeanObject = core::ptr::null_mut();
            v___x_8639_ = lean_usize_of_nat(v_start_8622_);
            v___x_8640_ = lean_usize_of_nat(v_stop_8623_);
            v___x_8641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v_inst_8619_,
                v___f_8630_,
                v_as_8621_,
                v___x_8639_,
                v___x_8640_,
                v___x_8626_,
            );
            return v___x_8641_;
        }
    }
}
pub unsafe fn l_Array_filterM___boxed(
    mut v_m_8642_: *mut LeanObject,
    mut v_00_u03b1_8643_: *mut LeanObject,
    mut v_inst_8644_: *mut LeanObject,
    mut v_p_8645_: *mut LeanObject,
    mut v_as_8646_: *mut LeanObject,
    mut v_start_8647_: *mut LeanObject,
    mut v_stop_8648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8649_: *mut LeanObject = core::ptr::null_mut();
    v_res_8649_ = l_Array_filterM(
        v_m_8642_,
        v_00_u03b1_8643_,
        v_inst_8644_,
        v_p_8645_,
        v_as_8646_,
        v_start_8647_,
        v_stop_8648_,
    );
    lean_dec(v_stop_8648_);
    lean_dec(v_start_8647_);
    return v_res_8649_;
}
pub unsafe fn l_Array_filterRevM___redArg___lam__0(
    mut v_toPure_8650_: *mut LeanObject,
    mut v_acc_8651_: *mut LeanObject,
    mut v_a_8652_: *mut LeanObject,
    mut v_____do__lift_8653_: u8,
) -> *mut LeanObject {
    if v_____do__lift_8653_ == 0 {
        let mut v___x_8654_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_8652_);
        v___x_8654_ = lean_apply_2(v_toPure_8650_, lean_box(0), v_acc_8651_);
        return v___x_8654_;
    } else {
        let mut v___x_8655_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8656_: *mut LeanObject = core::ptr::null_mut();
        v___x_8655_ = lean_array_push(v_acc_8651_, v_a_8652_);
        v___x_8656_ = lean_apply_2(v_toPure_8650_, lean_box(0), v___x_8655_);
        return v___x_8656_;
    }
}
pub unsafe fn l_Array_filterRevM___redArg___lam__0___boxed(
    mut v_toPure_8657_: *mut LeanObject,
    mut v_acc_8658_: *mut LeanObject,
    mut v_a_8659_: *mut LeanObject,
    mut v_____do__lift_8660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_129__boxed_8661_: u8 = 0;
    let mut v_res_8662_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_129__boxed_8661_ = (lean_unbox(v_____do__lift_8660_) as u8);
    v_res_8662_ = l_Array_filterRevM___redArg___lam__0(
        v_toPure_8657_,
        v_acc_8658_,
        v_a_8659_,
        v_____do__lift_129__boxed_8661_,
    );
    return v_res_8662_;
}
pub unsafe fn l_Array_filterRevM___redArg___lam__1(
    mut v_toPure_8663_: *mut LeanObject,
    mut v_p_8664_: *mut LeanObject,
    mut v_toBind_8665_: *mut LeanObject,
    mut v_a_8666_: *mut LeanObject,
    mut v_acc_8667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8670_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_8666_);
    v___f_8668_ = lean_alloc_closure(
        l_Array_filterRevM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_8668_, 0, v_toPure_8663_);
    lean_closure_set(v___f_8668_, 1, v_acc_8667_);
    lean_closure_set(v___f_8668_, 2, v_a_8666_);
    v___x_8669_ = lean_apply_1(v_p_8664_, v_a_8666_);
    v___x_8670_ = lean_apply_4(
        v_toBind_8665_,
        lean_box(0),
        lean_box(0),
        v___x_8669_,
        v___f_8668_,
    );
    return v___x_8670_;
}
pub unsafe fn l_Array_filterRevM___redArg(
    mut v_inst_8672_: *mut LeanObject,
    mut v_p_8673_: *mut LeanObject,
    mut v_as_8674_: *mut LeanObject,
    mut v_start_8675_: *mut LeanObject,
    mut v_stop_8676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_8678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_8680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_8681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8686_: u8 = 0;
    v_toApplicative_8677_ = lean_ctor_get(v_inst_8672_, 0);
    v_toFunctor_8678_ = lean_ctor_get(v_toApplicative_8677_, 0);
    v_toBind_8679_ = lean_ctor_get(v_inst_8672_, 1);
    v_toPure_8680_ = lean_ctor_get(v_toApplicative_8677_, 1);
    v_map_8681_ = lean_ctor_get(v_toFunctor_8678_, 0);
    lean_inc(v_map_8681_);
    lean_inc(v_toBind_8679_);
    lean_inc(v_toPure_8680_);
    v___f_8682_ = lean_alloc_closure(
        l_Array_filterRevM___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_8682_, 0, v_toPure_8680_);
    lean_closure_set(v___f_8682_, 1, v_p_8673_);
    lean_closure_set(v___f_8682_, 2, v_toBind_8679_);
    v___x_8683_ = l_Array_filterRevM___redArg___closed__0;
    v___x_8684_ = l_Array_filter___redArg___closed__0;
    v___x_8685_ = lean_array_get_size(v_as_8674_);
    v___x_8686_ = lean_nat_dec_le(v_start_8675_, v___x_8685_);
    if v___x_8686_ == 0 {
        let mut v___x_8687_: u8 = 0;
        v___x_8687_ = lean_nat_dec_lt(v_stop_8676_, v___x_8685_);
        if v___x_8687_ == 0 {
            let mut v___x_8688_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8689_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_toPure_8680_);
            lean_dec_ref(v___f_8682_);
            lean_dec_ref(v_as_8674_);
            lean_dec_ref(v_inst_8672_);
            v___x_8688_ = lean_apply_2(v_toPure_8680_, lean_box(0), v___x_8684_);
            v___x_8689_ = lean_apply_4(
                v_map_8681_,
                lean_box(0),
                lean_box(0),
                v___x_8683_,
                v___x_8688_,
            );
            return v___x_8689_;
        } else {
            let mut v___x_8690_: usize = 0;
            let mut v___x_8691_: usize = 0;
            let mut v___x_8692_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8693_: *mut LeanObject = core::ptr::null_mut();
            v___x_8690_ = lean_usize_of_nat(v___x_8685_);
            v___x_8691_ = lean_usize_of_nat(v_stop_8676_);
            v___x_8692_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
                v_inst_8672_,
                v___f_8682_,
                v_as_8674_,
                v___x_8690_,
                v___x_8691_,
                v___x_8684_,
            );
            v___x_8693_ = lean_apply_4(
                v_map_8681_,
                lean_box(0),
                lean_box(0),
                v___x_8683_,
                v___x_8692_,
            );
            return v___x_8693_;
        }
    } else {
        let mut v___x_8694_: u8 = 0;
        v___x_8694_ = lean_nat_dec_lt(v_stop_8676_, v_start_8675_);
        if v___x_8694_ == 0 {
            let mut v___x_8695_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8696_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_toPure_8680_);
            lean_dec_ref(v___f_8682_);
            lean_dec_ref(v_as_8674_);
            lean_dec_ref(v_inst_8672_);
            v___x_8695_ = lean_apply_2(v_toPure_8680_, lean_box(0), v___x_8684_);
            v___x_8696_ = lean_apply_4(
                v_map_8681_,
                lean_box(0),
                lean_box(0),
                v___x_8683_,
                v___x_8695_,
            );
            return v___x_8696_;
        } else {
            let mut v___x_8697_: usize = 0;
            let mut v___x_8698_: usize = 0;
            let mut v___x_8699_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8700_: *mut LeanObject = core::ptr::null_mut();
            v___x_8697_ = lean_usize_of_nat(v_start_8675_);
            v___x_8698_ = lean_usize_of_nat(v_stop_8676_);
            v___x_8699_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
                v_inst_8672_,
                v___f_8682_,
                v_as_8674_,
                v___x_8697_,
                v___x_8698_,
                v___x_8684_,
            );
            v___x_8700_ = lean_apply_4(
                v_map_8681_,
                lean_box(0),
                lean_box(0),
                v___x_8683_,
                v___x_8699_,
            );
            return v___x_8700_;
        }
    }
}
pub unsafe fn l_Array_filterRevM___redArg___boxed(
    mut v_inst_8701_: *mut LeanObject,
    mut v_p_8702_: *mut LeanObject,
    mut v_as_8703_: *mut LeanObject,
    mut v_start_8704_: *mut LeanObject,
    mut v_stop_8705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8706_: *mut LeanObject = core::ptr::null_mut();
    v_res_8706_ = l_Array_filterRevM___redArg(
        v_inst_8701_,
        v_p_8702_,
        v_as_8703_,
        v_start_8704_,
        v_stop_8705_,
    );
    lean_dec(v_stop_8705_);
    lean_dec(v_start_8704_);
    return v_res_8706_;
}
pub unsafe fn l_Array_filterRevM(
    mut v_m_8707_: *mut LeanObject,
    mut v_00_u03b1_8708_: *mut LeanObject,
    mut v_inst_8709_: *mut LeanObject,
    mut v_p_8710_: *mut LeanObject,
    mut v_as_8711_: *mut LeanObject,
    mut v_start_8712_: *mut LeanObject,
    mut v_stop_8713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_8715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_8717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_8718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8723_: u8 = 0;
    v_toApplicative_8714_ = lean_ctor_get(v_inst_8709_, 0);
    v_toFunctor_8715_ = lean_ctor_get(v_toApplicative_8714_, 0);
    v_toBind_8716_ = lean_ctor_get(v_inst_8709_, 1);
    v_toPure_8717_ = lean_ctor_get(v_toApplicative_8714_, 1);
    v_map_8718_ = lean_ctor_get(v_toFunctor_8715_, 0);
    lean_inc(v_map_8718_);
    lean_inc(v_toBind_8716_);
    lean_inc(v_toPure_8717_);
    v___f_8719_ = lean_alloc_closure(
        l_Array_filterRevM___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_8719_, 0, v_toPure_8717_);
    lean_closure_set(v___f_8719_, 1, v_p_8710_);
    lean_closure_set(v___f_8719_, 2, v_toBind_8716_);
    v___x_8720_ = l_Array_filterRevM___redArg___closed__0;
    v___x_8721_ = l_Array_filter___redArg___closed__0;
    v___x_8722_ = lean_array_get_size(v_as_8711_);
    v___x_8723_ = lean_nat_dec_le(v_start_8712_, v___x_8722_);
    if v___x_8723_ == 0 {
        let mut v___x_8724_: u8 = 0;
        v___x_8724_ = lean_nat_dec_lt(v_stop_8713_, v___x_8722_);
        if v___x_8724_ == 0 {
            let mut v___x_8725_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8726_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_toPure_8717_);
            lean_dec_ref(v___f_8719_);
            lean_dec_ref(v_as_8711_);
            lean_dec_ref(v_inst_8709_);
            v___x_8725_ = lean_apply_2(v_toPure_8717_, lean_box(0), v___x_8721_);
            v___x_8726_ = lean_apply_4(
                v_map_8718_,
                lean_box(0),
                lean_box(0),
                v___x_8720_,
                v___x_8725_,
            );
            return v___x_8726_;
        } else {
            let mut v___x_8727_: usize = 0;
            let mut v___x_8728_: usize = 0;
            let mut v___x_8729_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8730_: *mut LeanObject = core::ptr::null_mut();
            v___x_8727_ = lean_usize_of_nat(v___x_8722_);
            v___x_8728_ = lean_usize_of_nat(v_stop_8713_);
            v___x_8729_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
                v_inst_8709_,
                v___f_8719_,
                v_as_8711_,
                v___x_8727_,
                v___x_8728_,
                v___x_8721_,
            );
            v___x_8730_ = lean_apply_4(
                v_map_8718_,
                lean_box(0),
                lean_box(0),
                v___x_8720_,
                v___x_8729_,
            );
            return v___x_8730_;
        }
    } else {
        let mut v___x_8731_: u8 = 0;
        v___x_8731_ = lean_nat_dec_lt(v_stop_8713_, v_start_8712_);
        if v___x_8731_ == 0 {
            let mut v___x_8732_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8733_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_toPure_8717_);
            lean_dec_ref(v___f_8719_);
            lean_dec_ref(v_as_8711_);
            lean_dec_ref(v_inst_8709_);
            v___x_8732_ = lean_apply_2(v_toPure_8717_, lean_box(0), v___x_8721_);
            v___x_8733_ = lean_apply_4(
                v_map_8718_,
                lean_box(0),
                lean_box(0),
                v___x_8720_,
                v___x_8732_,
            );
            return v___x_8733_;
        } else {
            let mut v___x_8734_: usize = 0;
            let mut v___x_8735_: usize = 0;
            let mut v___x_8736_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8737_: *mut LeanObject = core::ptr::null_mut();
            v___x_8734_ = lean_usize_of_nat(v_start_8712_);
            v___x_8735_ = lean_usize_of_nat(v_stop_8713_);
            v___x_8736_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(
                v_inst_8709_,
                v___f_8719_,
                v_as_8711_,
                v___x_8734_,
                v___x_8735_,
                v___x_8721_,
            );
            v___x_8737_ = lean_apply_4(
                v_map_8718_,
                lean_box(0),
                lean_box(0),
                v___x_8720_,
                v___x_8736_,
            );
            return v___x_8737_;
        }
    }
}
pub unsafe fn l_Array_filterRevM___boxed(
    mut v_m_8738_: *mut LeanObject,
    mut v_00_u03b1_8739_: *mut LeanObject,
    mut v_inst_8740_: *mut LeanObject,
    mut v_p_8741_: *mut LeanObject,
    mut v_as_8742_: *mut LeanObject,
    mut v_start_8743_: *mut LeanObject,
    mut v_stop_8744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8745_: *mut LeanObject = core::ptr::null_mut();
    v_res_8745_ = l_Array_filterRevM(
        v_m_8738_,
        v_00_u03b1_8739_,
        v_inst_8740_,
        v_p_8741_,
        v_as_8742_,
        v_start_8743_,
        v_stop_8744_,
    );
    lean_dec(v_stop_8744_);
    lean_dec(v_start_8743_);
    return v_res_8745_;
}
pub unsafe fn l_Array_filterMapM___redArg___lam__0(
    mut v_toPure_8746_: *mut LeanObject,
    mut v_bs_8747_: *mut LeanObject,
    mut v_____do__lift_8748_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_8748_) == 0 {
        let mut v___x_8749_: *mut LeanObject = core::ptr::null_mut();
        v___x_8749_ = lean_apply_2(v_toPure_8746_, lean_box(0), v_bs_8747_);
        return v___x_8749_;
    } else {
        let mut v_val_8750_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8751_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8752_: *mut LeanObject = core::ptr::null_mut();
        v_val_8750_ = lean_ctor_get(v_____do__lift_8748_, 0);
        lean_inc(v_val_8750_);
        lean_dec_ref_known(v_____do__lift_8748_, 1);
        v___x_8751_ = lean_array_push(v_bs_8747_, v_val_8750_);
        v___x_8752_ = lean_apply_2(v_toPure_8746_, lean_box(0), v___x_8751_);
        return v___x_8752_;
    }
}
pub unsafe fn l_Array_filterMapM___redArg___lam__1(
    mut v_toPure_8753_: *mut LeanObject,
    mut v_f_8754_: *mut LeanObject,
    mut v_toBind_8755_: *mut LeanObject,
    mut v_bs_8756_: *mut LeanObject,
    mut v_a_8757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8760_: *mut LeanObject = core::ptr::null_mut();
    v___f_8758_ = lean_alloc_closure(
        l_Array_filterMapM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_8758_, 0, v_toPure_8753_);
    lean_closure_set(v___f_8758_, 1, v_bs_8756_);
    v___x_8759_ = lean_apply_1(v_f_8754_, v_a_8757_);
    v___x_8760_ = lean_apply_4(
        v_toBind_8755_,
        lean_box(0),
        lean_box(0),
        v___x_8759_,
        v___f_8758_,
    );
    return v___x_8760_;
}
pub unsafe fn l_Array_filterMapM___redArg(
    mut v_inst_8761_: *mut LeanObject,
    mut v_f_8762_: *mut LeanObject,
    mut v_as_8763_: *mut LeanObject,
    mut v_start_8764_: *mut LeanObject,
    mut v_stop_8765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_8768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8770_: u8 = 0;
    v_toApplicative_8766_ = lean_ctor_get(v_inst_8761_, 0);
    v_toBind_8767_ = lean_ctor_get(v_inst_8761_, 1);
    v_toPure_8768_ = lean_ctor_get(v_toApplicative_8766_, 1);
    v___x_8769_ = l_Array_filter___redArg___closed__0;
    v___x_8770_ = lean_nat_dec_lt(v_start_8764_, v_stop_8765_);
    if v___x_8770_ == 0 {
        let mut v___x_8771_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_toPure_8768_);
        lean_dec_ref(v_as_8763_);
        lean_dec(v_f_8762_);
        lean_dec_ref(v_inst_8761_);
        v___x_8771_ = lean_apply_2(v_toPure_8768_, lean_box(0), v___x_8769_);
        return v___x_8771_;
    } else {
        let mut v___f_8772_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8773_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8774_: u8 = 0;
        lean_inc(v_toBind_8767_);
        lean_inc(v_toPure_8768_);
        v___f_8772_ = lean_alloc_closure(
            l_Array_filterMapM___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            3,
        );
        lean_closure_set(v___f_8772_, 0, v_toPure_8768_);
        lean_closure_set(v___f_8772_, 1, v_f_8762_);
        lean_closure_set(v___f_8772_, 2, v_toBind_8767_);
        v___x_8773_ = lean_array_get_size(v_as_8763_);
        v___x_8774_ = lean_nat_dec_le(v_stop_8765_, v___x_8773_);
        if v___x_8774_ == 0 {
            let mut v___x_8775_: u8 = 0;
            v___x_8775_ = lean_nat_dec_lt(v_start_8764_, v___x_8773_);
            if v___x_8775_ == 0 {
                let mut v___x_8776_: *mut LeanObject = core::ptr::null_mut();
                lean_inc(v_toPure_8768_);
                lean_dec_ref(v___f_8772_);
                lean_dec_ref(v_as_8763_);
                lean_dec_ref(v_inst_8761_);
                v___x_8776_ = lean_apply_2(v_toPure_8768_, lean_box(0), v___x_8769_);
                return v___x_8776_;
            } else {
                let mut v___x_8777_: usize = 0;
                let mut v___x_8778_: usize = 0;
                let mut v___x_8779_: *mut LeanObject = core::ptr::null_mut();
                v___x_8777_ = lean_usize_of_nat(v_start_8764_);
                v___x_8778_ = lean_usize_of_nat(v___x_8773_);
                v___x_8779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v_inst_8761_,
                    v___f_8772_,
                    v_as_8763_,
                    v___x_8777_,
                    v___x_8778_,
                    v___x_8769_,
                );
                return v___x_8779_;
            }
        } else {
            let mut v___x_8780_: usize = 0;
            let mut v___x_8781_: usize = 0;
            let mut v___x_8782_: *mut LeanObject = core::ptr::null_mut();
            v___x_8780_ = lean_usize_of_nat(v_start_8764_);
            v___x_8781_ = lean_usize_of_nat(v_stop_8765_);
            v___x_8782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v_inst_8761_,
                v___f_8772_,
                v_as_8763_,
                v___x_8780_,
                v___x_8781_,
                v___x_8769_,
            );
            return v___x_8782_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___redArg___boxed(
    mut v_inst_8783_: *mut LeanObject,
    mut v_f_8784_: *mut LeanObject,
    mut v_as_8785_: *mut LeanObject,
    mut v_start_8786_: *mut LeanObject,
    mut v_stop_8787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8788_: *mut LeanObject = core::ptr::null_mut();
    v_res_8788_ = l_Array_filterMapM___redArg(
        v_inst_8783_,
        v_f_8784_,
        v_as_8785_,
        v_start_8786_,
        v_stop_8787_,
    );
    lean_dec(v_stop_8787_);
    lean_dec(v_start_8786_);
    return v_res_8788_;
}
pub unsafe fn l_Array_filterMapM(
    mut v_00_u03b1_8789_: *mut LeanObject,
    mut v_m_8790_: *mut LeanObject,
    mut v_00_u03b2_8791_: *mut LeanObject,
    mut v_inst_8792_: *mut LeanObject,
    mut v_f_8793_: *mut LeanObject,
    mut v_as_8794_: *mut LeanObject,
    mut v_start_8795_: *mut LeanObject,
    mut v_stop_8796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8797_: *mut LeanObject = core::ptr::null_mut();
    v___x_8797_ = l_Array_filterMapM___redArg(
        v_inst_8792_,
        v_f_8793_,
        v_as_8794_,
        v_start_8795_,
        v_stop_8796_,
    );
    return v___x_8797_;
}
pub unsafe fn l_Array_filterMapM___boxed(
    mut v_00_u03b1_8798_: *mut LeanObject,
    mut v_m_8799_: *mut LeanObject,
    mut v_00_u03b2_8800_: *mut LeanObject,
    mut v_inst_8801_: *mut LeanObject,
    mut v_f_8802_: *mut LeanObject,
    mut v_as_8803_: *mut LeanObject,
    mut v_start_8804_: *mut LeanObject,
    mut v_stop_8805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8806_: *mut LeanObject = core::ptr::null_mut();
    v_res_8806_ = l_Array_filterMapM(
        v_00_u03b1_8798_,
        v_m_8799_,
        v_00_u03b2_8800_,
        v_inst_8801_,
        v_f_8802_,
        v_as_8803_,
        v_start_8804_,
        v_stop_8805_,
    );
    lean_dec(v_stop_8805_);
    lean_dec(v_start_8804_);
    return v_res_8806_;
}
pub unsafe fn l_Array_filterMap___redArg(
    mut v_f_8807_: *mut LeanObject,
    mut v_as_8808_: *mut LeanObject,
    mut v_start_8809_: *mut LeanObject,
    mut v_stop_8810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8813_: *mut LeanObject = core::ptr::null_mut();
    v___f_8811_ = lean_alloc_closure(
        l_Array_findSomeRev_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_8811_, 0, v_f_8807_);
    v___x_8812_ = l_Array_foldl___redArg___closed__9;
    v___x_8813_ = l_Array_filterMapM___redArg(
        v___x_8812_,
        v___f_8811_,
        v_as_8808_,
        v_start_8809_,
        v_stop_8810_,
    );
    return v___x_8813_;
}
pub unsafe fn l_Array_filterMap___redArg___boxed(
    mut v_f_8814_: *mut LeanObject,
    mut v_as_8815_: *mut LeanObject,
    mut v_start_8816_: *mut LeanObject,
    mut v_stop_8817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8818_: *mut LeanObject = core::ptr::null_mut();
    v_res_8818_ = l_Array_filterMap___redArg(v_f_8814_, v_as_8815_, v_start_8816_, v_stop_8817_);
    lean_dec(v_stop_8817_);
    lean_dec(v_start_8816_);
    return v_res_8818_;
}
pub unsafe fn l_Array_filterMap(
    mut v_00_u03b1_8819_: *mut LeanObject,
    mut v_00_u03b2_8820_: *mut LeanObject,
    mut v_f_8821_: *mut LeanObject,
    mut v_as_8822_: *mut LeanObject,
    mut v_start_8823_: *mut LeanObject,
    mut v_stop_8824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8827_: *mut LeanObject = core::ptr::null_mut();
    v___f_8825_ = lean_alloc_closure(
        l_Array_findSomeRev_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_8825_, 0, v_f_8821_);
    v___x_8826_ = l_Array_foldl___redArg___closed__9;
    v___x_8827_ = l_Array_filterMapM___redArg(
        v___x_8826_,
        v___f_8825_,
        v_as_8822_,
        v_start_8823_,
        v_stop_8824_,
    );
    return v___x_8827_;
}
pub unsafe fn l_Array_filterMap___boxed(
    mut v_00_u03b1_8828_: *mut LeanObject,
    mut v_00_u03b2_8829_: *mut LeanObject,
    mut v_f_8830_: *mut LeanObject,
    mut v_as_8831_: *mut LeanObject,
    mut v_start_8832_: *mut LeanObject,
    mut v_stop_8833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8834_: *mut LeanObject = core::ptr::null_mut();
    v_res_8834_ = l_Array_filterMap(
        v_00_u03b1_8828_,
        v_00_u03b2_8829_,
        v_f_8830_,
        v_as_8831_,
        v_start_8832_,
        v_stop_8833_,
    );
    lean_dec(v_stop_8833_);
    lean_dec(v_start_8832_);
    return v_res_8834_;
}
pub unsafe fn l_Array_getMax_x3f___redArg___lam__0(
    mut v_lt_8835_: *mut LeanObject,
    mut v_x1_8836_: *mut LeanObject,
    mut v_x2_8837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8839_: u8 = 0;
    lean_inc(v_x2_8837_);
    lean_inc(v_x1_8836_);
    v___x_8838_ = lean_apply_2(v_lt_8835_, v_x1_8836_, v_x2_8837_);
    v___x_8839_ = (lean_unbox(v___x_8838_) as u8);
    if v___x_8839_ == 0 {
        lean_dec(v_x2_8837_);
        return v_x1_8836_;
    } else {
        lean_dec(v_x1_8836_);
        return v_x2_8837_;
    }
}
pub unsafe fn l_Array_getMax_x3f___redArg(
    mut v_as_8840_: *mut LeanObject,
    mut v_lt_8841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8844_: u8 = 0;
    v___x_8842_ = lean_unsigned_to_nat(0);
    v___x_8843_ = lean_array_get_size(v_as_8840_);
    v___x_8844_ = lean_nat_dec_lt(v___x_8842_, v___x_8843_);
    if v___x_8844_ == 0 {
        let mut v___x_8845_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_lt_8841_);
        lean_dec_ref(v_as_8840_);
        v___x_8845_ = lean_box(0);
        return v___x_8845_;
    } else {
        let mut v_a0_8846_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8847_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8848_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8849_: u8 = 0;
        v_a0_8846_ = lean_array_fget(v_as_8840_, v___x_8842_);
        v___x_8847_ = lean_unsigned_to_nat(1);
        v___x_8848_ = l_Array_foldl___redArg___closed__9;
        v___x_8849_ = lean_nat_dec_lt(v___x_8847_, v___x_8843_);
        if v___x_8849_ == 0 {
            let mut v___x_8850_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_lt_8841_);
            lean_dec_ref(v_as_8840_);
            v___x_8850_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_8850_, 0, v_a0_8846_);
            return v___x_8850_;
        } else {
            let mut v___f_8851_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8852_: u8 = 0;
            v___f_8851_ = lean_alloc_closure(
                l_Array_getMax_x3f___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                1,
            );
            lean_closure_set(v___f_8851_, 0, v_lt_8841_);
            v___x_8852_ = lean_nat_dec_le(v___x_8843_, v___x_8843_);
            if v___x_8852_ == 0 {
                if v___x_8849_ == 0 {
                    let mut v___x_8853_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref(v___f_8851_);
                    lean_dec_ref(v_as_8840_);
                    v___x_8853_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_8853_, 0, v_a0_8846_);
                    return v___x_8853_;
                } else {
                    let mut v___x_8854_: usize = 0;
                    let mut v___x_8855_: usize = 0;
                    let mut v___x_8856_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_8857_: *mut LeanObject = core::ptr::null_mut();
                    v___x_8854_ = 1usize;
                    v___x_8855_ = lean_usize_of_nat(v___x_8843_);
                    v___x_8856_ =
                        l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                            v___x_8848_,
                            v___f_8851_,
                            v_as_8840_,
                            v___x_8854_,
                            v___x_8855_,
                            v_a0_8846_,
                        );
                    v___x_8857_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_8857_, 0, v___x_8856_);
                    return v___x_8857_;
                }
            } else {
                let mut v___x_8858_: usize = 0;
                let mut v___x_8859_: usize = 0;
                let mut v___x_8860_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_8861_: *mut LeanObject = core::ptr::null_mut();
                v___x_8858_ = 1usize;
                v___x_8859_ = lean_usize_of_nat(v___x_8843_);
                v___x_8860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v___x_8848_,
                    v___f_8851_,
                    v_as_8840_,
                    v___x_8858_,
                    v___x_8859_,
                    v_a0_8846_,
                );
                v___x_8861_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_8861_, 0, v___x_8860_);
                return v___x_8861_;
            }
        }
    }
}
pub unsafe fn l_Array_getMax_x3f(
    mut v_00_u03b1_8862_: *mut LeanObject,
    mut v_as_8863_: *mut LeanObject,
    mut v_lt_8864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8865_: *mut LeanObject = core::ptr::null_mut();
    v___x_8865_ = l_Array_getMax_x3f___redArg(v_as_8863_, v_lt_8864_);
    return v___x_8865_;
}
pub unsafe fn l_Array_partition___redArg___lam__0(
    mut v_p_8866_: *mut LeanObject,
    mut v_a_8867_: *mut LeanObject,
    mut v_x_8868_: *mut LeanObject,
    mut v___y_8869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_8870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8874_: u8 = 0;
    let mut v___x_8875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8876_: u8 = 0;
    let mut v___x_8877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8887_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_8870_ = lean_ctor_get(v___y_8869_, 0);
                v_snd_8871_ = lean_ctor_get(v___y_8869_, 1);
                v_isSharedCheck_8887_ = (!lean_is_exclusive(v___y_8869_)) as u8;
                if v_isSharedCheck_8887_ == 0 {
                    v___x_8873_ = v___y_8869_;
                    v_isShared_8874_ = v_isSharedCheck_8887_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_8871_);
                    lean_inc(v_fst_8870_);
                    lean_dec(v___y_8869_);
                    v___x_8873_ = lean_box(0);
                    v_isShared_8874_ = v_isSharedCheck_8887_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_a_8867_);
                v___x_8875_ = lean_apply_1(v_p_8866_, v_a_8867_);
                v___x_8876_ = (lean_unbox(v___x_8875_) as u8);
                if v___x_8876_ == 0 {
                    v___x_8877_ = lean_array_push(v_snd_8871_, v_a_8867_);
                    if v_isShared_8874_ == 0 {
                        lean_ctor_set(v___x_8873_, 1, v___x_8877_);
                        v___x_8879_ = v___x_8873_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8881_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8881_, 0, v_fst_8870_);
                        lean_ctor_set(v_reuseFailAlloc_8881_, 1, v___x_8877_);
                        v___x_8879_ = v_reuseFailAlloc_8881_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_8882_ = lean_array_push(v_fst_8870_, v_a_8867_);
                    if v_isShared_8874_ == 0 {
                        lean_ctor_set(v___x_8873_, 0, v___x_8882_);
                        v___x_8884_ = v___x_8873_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8886_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8886_, 0, v___x_8882_);
                        lean_ctor_set(v_reuseFailAlloc_8886_, 1, v_snd_8871_);
                        v___x_8884_ = v_reuseFailAlloc_8886_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_8880_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_8880_, 0, v___x_8879_);
                return v___x_8880_;
            }
            3 => {
                v___x_8885_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_8885_, 0, v___x_8884_);
                return v___x_8885_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_partition___redArg(
    mut v_p_8890_: *mut LeanObject,
    mut v_as_8891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8895_: usize = 0;
    let mut v___x_8896_: usize = 0;
    let mut v___x_8897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8902_: u8 = 0;
    let mut v___x_8904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8906_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_8892_ = lean_alloc_closure(
                    l_Array_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___f_8892_, 0, v_p_8890_);
                v___x_8893_ = l_Array_foldl___redArg___closed__9;
                v___x_8894_ = l_Array_partition___redArg___closed__0;
                v_sz_8895_ = lean_array_size(v_as_8891_);
                v___x_8896_ = 0usize;
                v___x_8897_ =
                    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
                        v___x_8893_,
                        v_as_8891_,
                        v___f_8892_,
                        v_sz_8895_,
                        v___x_8896_,
                        v___x_8894_,
                    );
                v_fst_8898_ = lean_ctor_get(v___x_8897_, 0);
                v_snd_8899_ = lean_ctor_get(v___x_8897_, 1);
                v_isSharedCheck_8906_ = (!lean_is_exclusive(v___x_8897_)) as u8;
                if v_isSharedCheck_8906_ == 0 {
                    v___x_8901_ = v___x_8897_;
                    v_isShared_8902_ = v_isSharedCheck_8906_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_8899_);
                    lean_inc(v_fst_8898_);
                    lean_dec(v___x_8897_);
                    v___x_8901_ = lean_box(0);
                    v_isShared_8902_ = v_isSharedCheck_8906_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_8902_ == 0 {
                    v___x_8904_ = v___x_8901_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8905_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8905_, 0, v_fst_8898_);
                    lean_ctor_set(v_reuseFailAlloc_8905_, 1, v_snd_8899_);
                    v___x_8904_ = v_reuseFailAlloc_8905_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8904_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_partition(
    mut v_00_u03b1_8907_: *mut LeanObject,
    mut v_p_8908_: *mut LeanObject,
    mut v_as_8909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8913_: usize = 0;
    let mut v___x_8914_: usize = 0;
    let mut v___x_8915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8920_: u8 = 0;
    let mut v___x_8922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8924_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_8910_ = lean_alloc_closure(
                    l_Array_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___f_8910_, 0, v_p_8908_);
                v___x_8911_ = l_Array_foldl___redArg___closed__9;
                v___x_8912_ = l_Array_partition___redArg___closed__0;
                v_sz_8913_ = lean_array_size(v_as_8909_);
                v___x_8914_ = 0usize;
                v___x_8915_ =
                    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(
                        v___x_8911_,
                        v_as_8909_,
                        v___f_8910_,
                        v_sz_8913_,
                        v___x_8914_,
                        v___x_8912_,
                    );
                v_fst_8916_ = lean_ctor_get(v___x_8915_, 0);
                v_snd_8917_ = lean_ctor_get(v___x_8915_, 1);
                v_isSharedCheck_8924_ = (!lean_is_exclusive(v___x_8915_)) as u8;
                if v_isSharedCheck_8924_ == 0 {
                    v___x_8919_ = v___x_8915_;
                    v_isShared_8920_ = v_isSharedCheck_8924_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_8917_);
                    lean_inc(v_fst_8916_);
                    lean_dec(v___x_8915_);
                    v___x_8919_ = lean_box(0);
                    v_isShared_8920_ = v_isSharedCheck_8924_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_8920_ == 0 {
                    v___x_8922_ = v___x_8919_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8923_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8923_, 0, v_fst_8916_);
                    lean_ctor_set(v_reuseFailAlloc_8923_, 1, v_snd_8917_);
                    v___x_8922_ = v_reuseFailAlloc_8923_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8922_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_popWhile___redArg(
    mut v_p_8925_: *mut LeanObject,
    mut v_as_8926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8929_: u8 = 0;
    let mut v___x_8930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8934_: u8 = 0;
    let mut v___x_8935_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8927_ = lean_unsigned_to_nat(0);
                v___x_8928_ = lean_array_get_size(v_as_8926_);
                v___x_8929_ = lean_nat_dec_lt(v___x_8927_, v___x_8928_);
                if v___x_8929_ == 0 {
                    lean_dec_ref(v_p_8925_);
                    return v_as_8926_;
                } else {
                    v___x_8930_ = lean_unsigned_to_nat(1);
                    v___x_8931_ = lean_nat_sub(v___x_8928_, v___x_8930_);
                    v___x_8932_ = lean_array_fget_borrowed(v_as_8926_, v___x_8931_);
                    lean_dec(v___x_8931_);
                    lean_inc_ref(v_p_8925_);
                    lean_inc(v___x_8932_);
                    v___x_8933_ = lean_apply_1(v_p_8925_, v___x_8932_);
                    v___x_8934_ = (lean_unbox(v___x_8933_) as u8);
                    if v___x_8934_ == 0 {
                        lean_dec_ref(v_p_8925_);
                        return v_as_8926_;
                    } else {
                        v___x_8935_ = lean_array_pop(v_as_8926_);
                        v_as_8926_ = v___x_8935_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_popWhile(
    mut v_00_u03b1_8937_: *mut LeanObject,
    mut v_p_8938_: *mut LeanObject,
    mut v_as_8939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8940_: *mut LeanObject = core::ptr::null_mut();
    v___x_8940_ = l_Array_popWhile___redArg(v_p_8938_, v_as_8939_);
    return v___x_8940_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(
    mut v_p_8941_: *mut LeanObject,
    mut v_as_8942_: *mut LeanObject,
    mut v_i_8943_: *mut LeanObject,
    mut v_acc_8944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8946_: u8 = 0;
    let mut v_a_8947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8949_: u8 = 0;
    let mut v___x_8950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8952_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8945_ = lean_array_get_size(v_as_8942_);
                v___x_8946_ = lean_nat_dec_lt(v_i_8943_, v___x_8945_);
                if v___x_8946_ == 0 {
                    lean_dec(v_i_8943_);
                    lean_dec_ref(v_p_8941_);
                    return v_acc_8944_;
                } else {
                    v_a_8947_ = lean_array_fget_borrowed(v_as_8942_, v_i_8943_);
                    lean_inc_ref(v_p_8941_);
                    lean_inc(v_a_8947_);
                    v___x_8948_ = lean_apply_1(v_p_8941_, v_a_8947_);
                    v___x_8949_ = (lean_unbox(v___x_8948_) as u8);
                    if v___x_8949_ == 0 {
                        lean_dec(v_i_8943_);
                        lean_dec_ref(v_p_8941_);
                        return v_acc_8944_;
                    } else {
                        v___x_8950_ = lean_unsigned_to_nat(1);
                        v___x_8951_ = lean_nat_add(v_i_8943_, v___x_8950_);
                        lean_dec(v_i_8943_);
                        lean_inc(v_a_8947_);
                        v___x_8952_ = lean_array_push(v_acc_8944_, v_a_8947_);
                        v_i_8943_ = v___x_8951_;
                        v_acc_8944_ = v___x_8952_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg___boxed(
    mut v_p_8954_: *mut LeanObject,
    mut v_as_8955_: *mut LeanObject,
    mut v_i_8956_: *mut LeanObject,
    mut v_acc_8957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8958_: *mut LeanObject = core::ptr::null_mut();
    v_res_8958_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(
        v_p_8954_,
        v_as_8955_,
        v_i_8956_,
        v_acc_8957_,
    );
    lean_dec_ref(v_as_8955_);
    return v_res_8958_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(
    mut v_00_u03b1_8959_: *mut LeanObject,
    mut v_p_8960_: *mut LeanObject,
    mut v_as_8961_: *mut LeanObject,
    mut v_i_8962_: *mut LeanObject,
    mut v_acc_8963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8964_: *mut LeanObject = core::ptr::null_mut();
    v___x_8964_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(
        v_p_8960_,
        v_as_8961_,
        v_i_8962_,
        v_acc_8963_,
    );
    return v___x_8964_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___boxed(
    mut v_00_u03b1_8965_: *mut LeanObject,
    mut v_p_8966_: *mut LeanObject,
    mut v_as_8967_: *mut LeanObject,
    mut v_i_8968_: *mut LeanObject,
    mut v_acc_8969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8970_: *mut LeanObject = core::ptr::null_mut();
    v_res_8970_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(
        v_00_u03b1_8965_,
        v_p_8966_,
        v_as_8967_,
        v_i_8968_,
        v_acc_8969_,
    );
    lean_dec_ref(v_as_8967_);
    return v_res_8970_;
}
pub unsafe fn l_Array_takeWhile___redArg(
    mut v_p_8971_: *mut LeanObject,
    mut v_as_8972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8975_: *mut LeanObject = core::ptr::null_mut();
    v___x_8973_ = lean_unsigned_to_nat(0);
    v___x_8974_ = l_Array_filter___redArg___closed__0;
    v___x_8975_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(
        v_p_8971_,
        v_as_8972_,
        v___x_8973_,
        v___x_8974_,
    );
    return v___x_8975_;
}
pub unsafe fn l_Array_takeWhile___redArg___boxed(
    mut v_p_8976_: *mut LeanObject,
    mut v_as_8977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8978_: *mut LeanObject = core::ptr::null_mut();
    v_res_8978_ = l_Array_takeWhile___redArg(v_p_8976_, v_as_8977_);
    lean_dec_ref(v_as_8977_);
    return v_res_8978_;
}
pub unsafe fn l_Array_takeWhile(
    mut v_00_u03b1_8979_: *mut LeanObject,
    mut v_p_8980_: *mut LeanObject,
    mut v_as_8981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8982_: *mut LeanObject = core::ptr::null_mut();
    v___x_8982_ = l_Array_takeWhile___redArg(v_p_8980_, v_as_8981_);
    return v___x_8982_;
}
pub unsafe fn l_Array_takeWhile___boxed(
    mut v_00_u03b1_8983_: *mut LeanObject,
    mut v_p_8984_: *mut LeanObject,
    mut v_as_8985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8986_: *mut LeanObject = core::ptr::null_mut();
    v_res_8986_ = l_Array_takeWhile(v_00_u03b1_8983_, v_p_8984_, v_as_8985_);
    lean_dec_ref(v_as_8985_);
    return v_res_8986_;
}
pub unsafe fn _init_l_Array_eraseIdx___auto__1() -> *mut LeanObject {
    let mut v___x_8987_: *mut LeanObject = core::ptr::null_mut();
    v___x_8987_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__17_once),
        _init_l_Array_swap___auto__1___closed__17,
    );
    return v___x_8987_;
}
pub unsafe fn l_Array_eraseIdx___redArg(
    mut v_xs_8988_: *mut LeanObject,
    mut v_i_8989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8993_: u8 = 0;
    let mut v___x_8994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_8995_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8990_ = lean_unsigned_to_nat(1);
                v___x_8991_ = lean_nat_add(v_i_8989_, v___x_8990_);
                v___x_8992_ = lean_array_get_size(v_xs_8988_);
                v___x_8993_ = lean_nat_dec_lt(v___x_8991_, v___x_8992_);
                if v___x_8993_ == 0 {
                    lean_dec(v___x_8991_);
                    lean_dec(v_i_8989_);
                    v___x_8994_ = lean_array_pop(v_xs_8988_);
                    return v___x_8994_;
                } else {
                    v_xs_x27_8995_ = lean_array_fswap(v_xs_8988_, v___x_8991_, v_i_8989_);
                    lean_dec(v_i_8989_);
                    v_xs_8988_ = v_xs_x27_8995_;
                    v_i_8989_ = v___x_8991_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_eraseIdx(
    mut v_00_u03b1_8997_: *mut LeanObject,
    mut v_xs_8998_: *mut LeanObject,
    mut v_i_8999_: *mut LeanObject,
    mut v_h_9000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9001_: *mut LeanObject = core::ptr::null_mut();
    v___x_9001_ = l_Array_eraseIdx___redArg(v_xs_8998_, v_i_8999_);
    return v___x_9001_;
}
pub unsafe fn l_Array_eraseIdxIfInBounds___redArg(
    mut v_xs_9002_: *mut LeanObject,
    mut v_i_9003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9005_: u8 = 0;
    v___x_9004_ = lean_array_get_size(v_xs_9002_);
    v___x_9005_ = lean_nat_dec_lt(v_i_9003_, v___x_9004_);
    if v___x_9005_ == 0 {
        lean_dec(v_i_9003_);
        return v_xs_9002_;
    } else {
        let mut v___x_9006_: *mut LeanObject = core::ptr::null_mut();
        v___x_9006_ = l_Array_eraseIdx___redArg(v_xs_9002_, v_i_9003_);
        return v___x_9006_;
    }
}
pub unsafe fn l_Array_eraseIdxIfInBounds(
    mut v_00_u03b1_9007_: *mut LeanObject,
    mut v_xs_9008_: *mut LeanObject,
    mut v_i_9009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9010_: *mut LeanObject = core::ptr::null_mut();
    v___x_9010_ = l_Array_eraseIdxIfInBounds___redArg(v_xs_9008_, v_i_9009_);
    return v___x_9010_;
}
pub unsafe fn _init_l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_9011_: *mut LeanObject = core::ptr::null_mut();
    v___x_9011_ = l_Array_instInhabited(lean_box(0));
    return v___x_9011_;
}
pub unsafe fn l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(
    mut v_msg_9012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9014_: *mut LeanObject = core::ptr::null_mut();
    v___x_9013_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0_once
        ),
        _init_l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0,
    );
    v___x_9014_ = lean_panic_fn_borrowed(v___x_9013_, v_msg_9012_);
    return v___x_9014_;
}
pub unsafe fn l_panic___at___00Array_eraseIdx_x21_spec__0(
    mut v_00_u03b1_9015_: *mut LeanObject,
    mut v_msg_9016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9017_: *mut LeanObject = core::ptr::null_mut();
    v___x_9017_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v_msg_9016_);
    return v___x_9017_;
}
pub unsafe fn _init_l_Array_eraseIdx_x21___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_9020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9025_: *mut LeanObject = core::ptr::null_mut();
    v___x_9020_ = l_Array_eraseIdx_x21___redArg___closed__1;
    v___x_9021_ = lean_unsigned_to_nat(47);
    v___x_9022_ = lean_unsigned_to_nat(1820);
    v___x_9023_ = l_Array_eraseIdx_x21___redArg___closed__0;
    v___x_9024_ = l_Array_swapAt_x21___redArg___closed__0;
    v___x_9025_ = l_mkPanicMessageWithDecl(
        v___x_9024_,
        v___x_9023_,
        v___x_9022_,
        v___x_9021_,
        v___x_9020_,
    );
    return v___x_9025_;
}
pub unsafe fn l_Array_eraseIdx_x21___redArg(
    mut v_xs_9026_: *mut LeanObject,
    mut v_i_9027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9029_: u8 = 0;
    v___x_9028_ = lean_array_get_size(v_xs_9026_);
    v___x_9029_ = lean_nat_dec_lt(v_i_9027_, v___x_9028_);
    if v___x_9029_ == 0 {
        let mut v___x_9030_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9031_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_i_9027_);
        lean_dec_ref(v_xs_9026_);
        v___x_9030_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Array_eraseIdx_x21___redArg___closed__2),
            core::ptr::addr_of_mut!(l_Array_eraseIdx_x21___redArg___closed__2_once),
            _init_l_Array_eraseIdx_x21___redArg___closed__2,
        );
        v___x_9031_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_9030_);
        return v___x_9031_;
    } else {
        let mut v___x_9032_: *mut LeanObject = core::ptr::null_mut();
        v___x_9032_ = l_Array_eraseIdx___redArg(v_xs_9026_, v_i_9027_);
        return v___x_9032_;
    }
}
pub unsafe fn l_Array_eraseIdx_x21(
    mut v_00_u03b1_9033_: *mut LeanObject,
    mut v_xs_9034_: *mut LeanObject,
    mut v_i_9035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9036_: *mut LeanObject = core::ptr::null_mut();
    v___x_9036_ = l_Array_eraseIdx_x21___redArg(v_xs_9034_, v_i_9035_);
    return v___x_9036_;
}
pub unsafe fn l_Array_erase___redArg(
    mut v_inst_9037_: *mut LeanObject,
    mut v_as_9038_: *mut LeanObject,
    mut v_a_9039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9040_: *mut LeanObject = core::ptr::null_mut();
    v___x_9040_ = l_Array_finIdxOf_x3f___redArg(v_inst_9037_, v_as_9038_, v_a_9039_);
    if lean_obj_tag(v___x_9040_) == 0 {
        return v_as_9038_;
    } else {
        let mut v_val_9041_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9042_: *mut LeanObject = core::ptr::null_mut();
        v_val_9041_ = lean_ctor_get(v___x_9040_, 0);
        lean_inc(v_val_9041_);
        lean_dec_ref_known(v___x_9040_, 1);
        v___x_9042_ = l_Array_eraseIdx___redArg(v_as_9038_, v_val_9041_);
        return v___x_9042_;
    }
}
pub unsafe fn l_Array_erase(
    mut v_00_u03b1_9043_: *mut LeanObject,
    mut v_inst_9044_: *mut LeanObject,
    mut v_as_9045_: *mut LeanObject,
    mut v_a_9046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9047_: *mut LeanObject = core::ptr::null_mut();
    v___x_9047_ = l_Array_erase___redArg(v_inst_9044_, v_as_9045_, v_a_9046_);
    return v___x_9047_;
}
pub unsafe fn l_Array_eraseP___redArg(
    mut v_as_9048_: *mut LeanObject,
    mut v_p_9049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9051_: *mut LeanObject = core::ptr::null_mut();
    v___x_9050_ = lean_unsigned_to_nat(0);
    v___x_9051_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(
        v_p_9049_,
        v_as_9048_,
        v___x_9050_,
    );
    if lean_obj_tag(v___x_9051_) == 0 {
        return v_as_9048_;
    } else {
        let mut v_val_9052_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9053_: *mut LeanObject = core::ptr::null_mut();
        v_val_9052_ = lean_ctor_get(v___x_9051_, 0);
        lean_inc(v_val_9052_);
        lean_dec_ref_known(v___x_9051_, 1);
        v___x_9053_ = l_Array_eraseIdx___redArg(v_as_9048_, v_val_9052_);
        return v___x_9053_;
    }
}
pub unsafe fn l_Array_eraseP(
    mut v_00_u03b1_9054_: *mut LeanObject,
    mut v_as_9055_: *mut LeanObject,
    mut v_p_9056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9057_: *mut LeanObject = core::ptr::null_mut();
    v___x_9057_ = l_Array_eraseP___redArg(v_as_9055_, v_p_9056_);
    return v___x_9057_;
}
pub unsafe fn _init_l_Array_insertIdx___auto__1() -> *mut LeanObject {
    let mut v___x_9058_: *mut LeanObject = core::ptr::null_mut();
    v___x_9058_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Array_swap___auto__1___closed__17_once),
        _init_l_Array_swap___auto__1___closed__17,
    );
    return v___x_9058_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(
    mut v_i_9059_: *mut LeanObject,
    mut v_as_9060_: *mut LeanObject,
    mut v_j_9061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9062_: u8 = 0;
    let mut v___x_9063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_as_9065_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9062_ = lean_nat_dec_lt(v_i_9059_, v_j_9061_);
                if v___x_9062_ == 0 {
                    lean_dec(v_j_9061_);
                    return v_as_9060_;
                } else {
                    v___x_9063_ = lean_unsigned_to_nat(1);
                    v___x_9064_ = lean_nat_sub(v_j_9061_, v___x_9063_);
                    v_as_9065_ = lean_array_fswap(v_as_9060_, v___x_9064_, v_j_9061_);
                    lean_dec(v_j_9061_);
                    v_as_9060_ = v_as_9065_;
                    v_j_9061_ = v___x_9064_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg___boxed(
    mut v_i_9067_: *mut LeanObject,
    mut v_as_9068_: *mut LeanObject,
    mut v_j_9069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9070_: *mut LeanObject = core::ptr::null_mut();
    v_res_9070_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(
        v_i_9067_, v_as_9068_, v_j_9069_,
    );
    lean_dec(v_i_9067_);
    return v_res_9070_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
    mut v_00_u03b1_9071_: *mut LeanObject,
    mut v_i_9072_: *mut LeanObject,
    mut v_as_9073_: *mut LeanObject,
    mut v_j_9074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9075_: *mut LeanObject = core::ptr::null_mut();
    v___x_9075_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(
        v_i_9072_, v_as_9073_, v_j_9074_,
    );
    return v___x_9075_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___boxed(
    mut v_00_u03b1_9076_: *mut LeanObject,
    mut v_i_9077_: *mut LeanObject,
    mut v_as_9078_: *mut LeanObject,
    mut v_j_9079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9080_: *mut LeanObject = core::ptr::null_mut();
    v_res_9080_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
        v_00_u03b1_9076_,
        v_i_9077_,
        v_as_9078_,
        v_j_9079_,
    );
    lean_dec(v_i_9077_);
    return v_res_9080_;
}
pub unsafe fn l_Array_insertIdx___redArg(
    mut v_as_9081_: *mut LeanObject,
    mut v_i_9082_: *mut LeanObject,
    mut v_a_9083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_j_9084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_as_9085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9086_: *mut LeanObject = core::ptr::null_mut();
    v_j_9084_ = lean_array_get_size(v_as_9081_);
    v_as_9085_ = lean_array_push(v_as_9081_, v_a_9083_);
    v___x_9086_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(
        v_i_9082_, v_as_9085_, v_j_9084_,
    );
    return v___x_9086_;
}
pub unsafe fn l_Array_insertIdx___redArg___boxed(
    mut v_as_9087_: *mut LeanObject,
    mut v_i_9088_: *mut LeanObject,
    mut v_a_9089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9090_: *mut LeanObject = core::ptr::null_mut();
    v_res_9090_ = l_Array_insertIdx___redArg(v_as_9087_, v_i_9088_, v_a_9089_);
    lean_dec(v_i_9088_);
    return v_res_9090_;
}
pub unsafe fn l_Array_insertIdx(
    mut v_00_u03b1_9091_: *mut LeanObject,
    mut v_as_9092_: *mut LeanObject,
    mut v_i_9093_: *mut LeanObject,
    mut v_a_9094_: *mut LeanObject,
    mut v_x_9095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_j_9096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_as_9097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9098_: *mut LeanObject = core::ptr::null_mut();
    v_j_9096_ = lean_array_get_size(v_as_9092_);
    v_as_9097_ = lean_array_push(v_as_9092_, v_a_9094_);
    v___x_9098_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(
        v_i_9093_, v_as_9097_, v_j_9096_,
    );
    return v___x_9098_;
}
pub unsafe fn l_Array_insertIdx___boxed(
    mut v_00_u03b1_9099_: *mut LeanObject,
    mut v_as_9100_: *mut LeanObject,
    mut v_i_9101_: *mut LeanObject,
    mut v_a_9102_: *mut LeanObject,
    mut v_x_9103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9104_: *mut LeanObject = core::ptr::null_mut();
    v_res_9104_ = l_Array_insertIdx(
        v_00_u03b1_9099_,
        v_as_9100_,
        v_i_9101_,
        v_a_9102_,
        v_x_9103_,
    );
    lean_dec(v_i_9101_);
    return v_res_9104_;
}
pub unsafe fn _init_l_Array_insertIdx_x21___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_9106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9111_: *mut LeanObject = core::ptr::null_mut();
    v___x_9106_ = l_Array_eraseIdx_x21___redArg___closed__1;
    v___x_9107_ = lean_unsigned_to_nat(7);
    v___x_9108_ = lean_unsigned_to_nat(1902);
    v___x_9109_ = l_Array_insertIdx_x21___redArg___closed__0;
    v___x_9110_ = l_Array_swapAt_x21___redArg___closed__0;
    v___x_9111_ = l_mkPanicMessageWithDecl(
        v___x_9110_,
        v___x_9109_,
        v___x_9108_,
        v___x_9107_,
        v___x_9106_,
    );
    return v___x_9111_;
}
pub unsafe fn l_Array_insertIdx_x21___redArg(
    mut v_as_9112_: *mut LeanObject,
    mut v_i_9113_: *mut LeanObject,
    mut v_a_9114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9116_: u8 = 0;
    v___x_9115_ = lean_array_get_size(v_as_9112_);
    v___x_9116_ = lean_nat_dec_le(v_i_9113_, v___x_9115_);
    if v___x_9116_ == 0 {
        let mut v___x_9117_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9118_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_9114_);
        lean_dec_ref(v_as_9112_);
        v___x_9117_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Array_insertIdx_x21___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Array_insertIdx_x21___redArg___closed__1_once),
            _init_l_Array_insertIdx_x21___redArg___closed__1,
        );
        v___x_9118_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_9117_);
        return v___x_9118_;
    } else {
        let mut v_as_9119_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9120_: *mut LeanObject = core::ptr::null_mut();
        v_as_9119_ = lean_array_push(v_as_9112_, v_a_9114_);
        v___x_9120_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(
            v_i_9113_,
            v_as_9119_,
            v___x_9115_,
        );
        return v___x_9120_;
    }
}
pub unsafe fn l_Array_insertIdx_x21___redArg___boxed(
    mut v_as_9121_: *mut LeanObject,
    mut v_i_9122_: *mut LeanObject,
    mut v_a_9123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9124_: *mut LeanObject = core::ptr::null_mut();
    v_res_9124_ = l_Array_insertIdx_x21___redArg(v_as_9121_, v_i_9122_, v_a_9123_);
    lean_dec(v_i_9122_);
    return v_res_9124_;
}
pub unsafe fn l_Array_insertIdx_x21(
    mut v_00_u03b1_9125_: *mut LeanObject,
    mut v_as_9126_: *mut LeanObject,
    mut v_i_9127_: *mut LeanObject,
    mut v_a_9128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9129_: *mut LeanObject = core::ptr::null_mut();
    v___x_9129_ = l_Array_insertIdx_x21___redArg(v_as_9126_, v_i_9127_, v_a_9128_);
    return v___x_9129_;
}
pub unsafe fn l_Array_insertIdx_x21___boxed(
    mut v_00_u03b1_9130_: *mut LeanObject,
    mut v_as_9131_: *mut LeanObject,
    mut v_i_9132_: *mut LeanObject,
    mut v_a_9133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9134_: *mut LeanObject = core::ptr::null_mut();
    v_res_9134_ = l_Array_insertIdx_x21(v_00_u03b1_9130_, v_as_9131_, v_i_9132_, v_a_9133_);
    lean_dec(v_i_9132_);
    return v_res_9134_;
}
pub unsafe fn l_Array_insertIdxIfInBounds___redArg(
    mut v_as_9135_: *mut LeanObject,
    mut v_i_9136_: *mut LeanObject,
    mut v_a_9137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9139_: u8 = 0;
    v___x_9138_ = lean_array_get_size(v_as_9135_);
    v___x_9139_ = lean_nat_dec_le(v_i_9136_, v___x_9138_);
    if v___x_9139_ == 0 {
        lean_dec(v_a_9137_);
        return v_as_9135_;
    } else {
        let mut v_as_9140_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9141_: *mut LeanObject = core::ptr::null_mut();
        v_as_9140_ = lean_array_push(v_as_9135_, v_a_9137_);
        v___x_9141_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(
            v_i_9136_,
            v_as_9140_,
            v___x_9138_,
        );
        return v___x_9141_;
    }
}
pub unsafe fn l_Array_insertIdxIfInBounds___redArg___boxed(
    mut v_as_9142_: *mut LeanObject,
    mut v_i_9143_: *mut LeanObject,
    mut v_a_9144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9145_: *mut LeanObject = core::ptr::null_mut();
    v_res_9145_ = l_Array_insertIdxIfInBounds___redArg(v_as_9142_, v_i_9143_, v_a_9144_);
    lean_dec(v_i_9143_);
    return v_res_9145_;
}
pub unsafe fn l_Array_insertIdxIfInBounds(
    mut v_00_u03b1_9146_: *mut LeanObject,
    mut v_as_9147_: *mut LeanObject,
    mut v_i_9148_: *mut LeanObject,
    mut v_a_9149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9150_: *mut LeanObject = core::ptr::null_mut();
    v___x_9150_ = l_Array_insertIdxIfInBounds___redArg(v_as_9147_, v_i_9148_, v_a_9149_);
    return v___x_9150_;
}
pub unsafe fn l_Array_insertIdxIfInBounds___boxed(
    mut v_00_u03b1_9151_: *mut LeanObject,
    mut v_as_9152_: *mut LeanObject,
    mut v_i_9153_: *mut LeanObject,
    mut v_a_9154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9155_: *mut LeanObject = core::ptr::null_mut();
    v_res_9155_ = l_Array_insertIdxIfInBounds(v_00_u03b1_9151_, v_as_9152_, v_i_9153_, v_a_9154_);
    lean_dec(v_i_9153_);
    return v_res_9155_;
}
pub unsafe fn l_Array_isPrefixOfAux___redArg(
    mut v_inst_9156_: *mut LeanObject,
    mut v_as_9157_: *mut LeanObject,
    mut v_bs_9158_: *mut LeanObject,
    mut v_i_9159_: *mut LeanObject,
) -> u8 {
    let mut v___x_9160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9161_: u8 = 0;
    let mut v___x_9162_: u8 = 0;
    let mut v_a_9163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_9164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9166_: u8 = 0;
    let mut v___x_9167_: u8 = 0;
    let mut v___x_9168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9169_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9160_ = lean_array_get_size(v_as_9157_);
                v___x_9161_ = lean_nat_dec_lt(v_i_9159_, v___x_9160_);
                if v___x_9161_ == 0 {
                    lean_dec(v_i_9159_);
                    lean_dec_ref(v_inst_9156_);
                    v___x_9162_ = 1;
                    return v___x_9162_;
                } else {
                    v_a_9163_ = lean_array_fget_borrowed(v_as_9157_, v_i_9159_);
                    v_b_9164_ = lean_array_fget_borrowed(v_bs_9158_, v_i_9159_);
                    lean_inc_ref(v_inst_9156_);
                    lean_inc(v_b_9164_);
                    lean_inc(v_a_9163_);
                    v___x_9165_ = lean_apply_2(v_inst_9156_, v_a_9163_, v_b_9164_);
                    v___x_9166_ = (lean_unbox(v___x_9165_) as u8);
                    if v___x_9166_ == 0 {
                        lean_dec(v_i_9159_);
                        lean_dec_ref(v_inst_9156_);
                        v___x_9167_ = (lean_unbox(v___x_9165_) as u8);
                        return v___x_9167_;
                    } else {
                        v___x_9168_ = lean_unsigned_to_nat(1);
                        v___x_9169_ = lean_nat_add(v_i_9159_, v___x_9168_);
                        lean_dec(v_i_9159_);
                        v_i_9159_ = v___x_9169_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isPrefixOfAux___redArg___boxed(
    mut v_inst_9171_: *mut LeanObject,
    mut v_as_9172_: *mut LeanObject,
    mut v_bs_9173_: *mut LeanObject,
    mut v_i_9174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9175_: u8 = 0;
    let mut v_r_9176_: *mut LeanObject = core::ptr::null_mut();
    v_res_9175_ = l_Array_isPrefixOfAux___redArg(v_inst_9171_, v_as_9172_, v_bs_9173_, v_i_9174_);
    lean_dec_ref(v_bs_9173_);
    lean_dec_ref(v_as_9172_);
    v_r_9176_ = lean_box((v_res_9175_) as usize);
    return v_r_9176_;
}
pub unsafe fn l_Array_isPrefixOfAux(
    mut v_00_u03b1_9177_: *mut LeanObject,
    mut v_inst_9178_: *mut LeanObject,
    mut v_as_9179_: *mut LeanObject,
    mut v_bs_9180_: *mut LeanObject,
    mut v_hle_9181_: *mut LeanObject,
    mut v_i_9182_: *mut LeanObject,
) -> u8 {
    let mut v___x_9183_: u8 = 0;
    v___x_9183_ = l_Array_isPrefixOfAux___redArg(v_inst_9178_, v_as_9179_, v_bs_9180_, v_i_9182_);
    return v___x_9183_;
}
pub unsafe fn l_Array_isPrefixOfAux___boxed(
    mut v_00_u03b1_9184_: *mut LeanObject,
    mut v_inst_9185_: *mut LeanObject,
    mut v_as_9186_: *mut LeanObject,
    mut v_bs_9187_: *mut LeanObject,
    mut v_hle_9188_: *mut LeanObject,
    mut v_i_9189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9190_: u8 = 0;
    let mut v_r_9191_: *mut LeanObject = core::ptr::null_mut();
    v_res_9190_ = l_Array_isPrefixOfAux(
        v_00_u03b1_9184_,
        v_inst_9185_,
        v_as_9186_,
        v_bs_9187_,
        v_hle_9188_,
        v_i_9189_,
    );
    lean_dec_ref(v_bs_9187_);
    lean_dec_ref(v_as_9186_);
    v_r_9191_ = lean_box((v_res_9190_) as usize);
    return v_r_9191_;
}
pub unsafe fn l_Array_isPrefixOf___redArg(
    mut v_inst_9192_: *mut LeanObject,
    mut v_as_9193_: *mut LeanObject,
    mut v_bs_9194_: *mut LeanObject,
) -> u8 {
    let mut v___x_9195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9197_: u8 = 0;
    v___x_9195_ = lean_array_get_size(v_as_9193_);
    v___x_9196_ = lean_array_get_size(v_bs_9194_);
    v___x_9197_ = lean_nat_dec_le(v___x_9195_, v___x_9196_);
    if v___x_9197_ == 0 {
        lean_dec_ref(v_inst_9192_);
        return v___x_9197_;
    } else {
        let mut v___x_9198_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9199_: u8 = 0;
        v___x_9198_ = lean_unsigned_to_nat(0);
        v___x_9199_ =
            l_Array_isPrefixOfAux___redArg(v_inst_9192_, v_as_9193_, v_bs_9194_, v___x_9198_);
        return v___x_9199_;
    }
}
pub unsafe fn l_Array_isPrefixOf___redArg___boxed(
    mut v_inst_9200_: *mut LeanObject,
    mut v_as_9201_: *mut LeanObject,
    mut v_bs_9202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9203_: u8 = 0;
    let mut v_r_9204_: *mut LeanObject = core::ptr::null_mut();
    v_res_9203_ = l_Array_isPrefixOf___redArg(v_inst_9200_, v_as_9201_, v_bs_9202_);
    lean_dec_ref(v_bs_9202_);
    lean_dec_ref(v_as_9201_);
    v_r_9204_ = lean_box((v_res_9203_) as usize);
    return v_r_9204_;
}
pub unsafe fn l_Array_isPrefixOf(
    mut v_00_u03b1_9205_: *mut LeanObject,
    mut v_inst_9206_: *mut LeanObject,
    mut v_as_9207_: *mut LeanObject,
    mut v_bs_9208_: *mut LeanObject,
) -> u8 {
    let mut v___x_9209_: u8 = 0;
    v___x_9209_ = l_Array_isPrefixOf___redArg(v_inst_9206_, v_as_9207_, v_bs_9208_);
    return v___x_9209_;
}
pub unsafe fn l_Array_isPrefixOf___boxed(
    mut v_00_u03b1_9210_: *mut LeanObject,
    mut v_inst_9211_: *mut LeanObject,
    mut v_as_9212_: *mut LeanObject,
    mut v_bs_9213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9214_: u8 = 0;
    let mut v_r_9215_: *mut LeanObject = core::ptr::null_mut();
    v_res_9214_ = l_Array_isPrefixOf(v_00_u03b1_9210_, v_inst_9211_, v_as_9212_, v_bs_9213_);
    lean_dec_ref(v_bs_9213_);
    lean_dec_ref(v_as_9212_);
    v_r_9215_ = lean_box((v_res_9214_) as usize);
    return v_r_9215_;
}
pub unsafe fn l_Array_zipWithMAux___redArg___lam__0___boxed(
    mut v_i_9216_: *mut LeanObject,
    mut v_cs_9217_: *mut LeanObject,
    mut v_inst_9218_: *mut LeanObject,
    mut v_as_9219_: *mut LeanObject,
    mut v_bs_9220_: *mut LeanObject,
    mut v_f_9221_: *mut LeanObject,
    mut v_____do__lift_9222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9223_: *mut LeanObject = core::ptr::null_mut();
    v_res_9223_ = l_Array_zipWithMAux___redArg___lam__0(
        v_i_9216_,
        v_cs_9217_,
        v_inst_9218_,
        v_as_9219_,
        v_bs_9220_,
        v_f_9221_,
        v_____do__lift_9222_,
    );
    lean_dec(v_i_9216_);
    return v_res_9223_;
}
pub unsafe fn l_Array_zipWithMAux___redArg(
    mut v_inst_9224_: *mut LeanObject,
    mut v_as_9225_: *mut LeanObject,
    mut v_bs_9226_: *mut LeanObject,
    mut v_f_9227_: *mut LeanObject,
    mut v_i_9228_: *mut LeanObject,
    mut v_cs_9229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9231_: u8 = 0;
    v___x_9230_ = lean_array_get_size(v_as_9225_);
    v___x_9231_ = lean_nat_dec_lt(v_i_9228_, v___x_9230_);
    if v___x_9231_ == 0 {
        let mut v_toApplicative_9232_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_9233_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9234_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_i_9228_);
        lean_dec(v_f_9227_);
        lean_dec_ref(v_bs_9226_);
        lean_dec_ref(v_as_9225_);
        v_toApplicative_9232_ = lean_ctor_get(v_inst_9224_, 0);
        lean_inc_ref(v_toApplicative_9232_);
        lean_dec_ref(v_inst_9224_);
        v_toPure_9233_ = lean_ctor_get(v_toApplicative_9232_, 1);
        lean_inc(v_toPure_9233_);
        lean_dec_ref(v_toApplicative_9232_);
        v___x_9234_ = lean_apply_2(v_toPure_9233_, lean_box(0), v_cs_9229_);
        return v___x_9234_;
    } else {
        let mut v___x_9235_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9236_: u8 = 0;
        v___x_9235_ = lean_array_get_size(v_bs_9226_);
        v___x_9236_ = lean_nat_dec_lt(v_i_9228_, v___x_9235_);
        if v___x_9236_ == 0 {
            let mut v_toApplicative_9237_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_9238_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9239_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_i_9228_);
            lean_dec(v_f_9227_);
            lean_dec_ref(v_bs_9226_);
            lean_dec_ref(v_as_9225_);
            v_toApplicative_9237_ = lean_ctor_get(v_inst_9224_, 0);
            lean_inc_ref(v_toApplicative_9237_);
            lean_dec_ref(v_inst_9224_);
            v_toPure_9238_ = lean_ctor_get(v_toApplicative_9237_, 1);
            lean_inc(v_toPure_9238_);
            lean_dec_ref(v_toApplicative_9237_);
            v___x_9239_ = lean_apply_2(v_toPure_9238_, lean_box(0), v_cs_9229_);
            return v___x_9239_;
        } else {
            let mut v_toBind_9240_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_9241_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_9242_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_9243_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9244_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9245_: *mut LeanObject = core::ptr::null_mut();
            v_toBind_9240_ = lean_ctor_get(v_inst_9224_, 1);
            lean_inc(v_toBind_9240_);
            lean_inc(v_f_9227_);
            lean_inc_ref(v_bs_9226_);
            lean_inc_ref(v_as_9225_);
            lean_inc(v_i_9228_);
            v___f_9241_ = lean_alloc_closure(
                l_Array_zipWithMAux___redArg___lam__0___boxed as *mut core::ffi::c_void,
                7,
                6,
            );
            lean_closure_set(v___f_9241_, 0, v_i_9228_);
            lean_closure_set(v___f_9241_, 1, v_cs_9229_);
            lean_closure_set(v___f_9241_, 2, v_inst_9224_);
            lean_closure_set(v___f_9241_, 3, v_as_9225_);
            lean_closure_set(v___f_9241_, 4, v_bs_9226_);
            lean_closure_set(v___f_9241_, 5, v_f_9227_);
            v_a_9242_ = lean_array_fget(v_as_9225_, v_i_9228_);
            lean_dec_ref(v_as_9225_);
            v_b_9243_ = lean_array_fget(v_bs_9226_, v_i_9228_);
            lean_dec(v_i_9228_);
            lean_dec_ref(v_bs_9226_);
            v___x_9244_ = lean_apply_2(v_f_9227_, v_a_9242_, v_b_9243_);
            v___x_9245_ = lean_apply_4(
                v_toBind_9240_,
                lean_box(0),
                lean_box(0),
                v___x_9244_,
                v___f_9241_,
            );
            return v___x_9245_;
        }
    }
}
pub unsafe fn l_Array_zipWithMAux___redArg___lam__0(
    mut v_i_9246_: *mut LeanObject,
    mut v_cs_9247_: *mut LeanObject,
    mut v_inst_9248_: *mut LeanObject,
    mut v_as_9249_: *mut LeanObject,
    mut v_bs_9250_: *mut LeanObject,
    mut v_f_9251_: *mut LeanObject,
    mut v_____do__lift_9252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9256_: *mut LeanObject = core::ptr::null_mut();
    v___x_9253_ = lean_unsigned_to_nat(1);
    v___x_9254_ = lean_nat_add(v_i_9246_, v___x_9253_);
    v___x_9255_ = lean_array_push(v_cs_9247_, v_____do__lift_9252_);
    v___x_9256_ = l_Array_zipWithMAux___redArg(
        v_inst_9248_,
        v_as_9249_,
        v_bs_9250_,
        v_f_9251_,
        v___x_9254_,
        v___x_9255_,
    );
    return v___x_9256_;
}
pub unsafe fn l_Array_zipWithMAux(
    mut v_00_u03b1_9257_: *mut LeanObject,
    mut v_00_u03b2_9258_: *mut LeanObject,
    mut v_00_u03b3_9259_: *mut LeanObject,
    mut v_m_9260_: *mut LeanObject,
    mut v_inst_9261_: *mut LeanObject,
    mut v_as_9262_: *mut LeanObject,
    mut v_bs_9263_: *mut LeanObject,
    mut v_f_9264_: *mut LeanObject,
    mut v_i_9265_: *mut LeanObject,
    mut v_cs_9266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9267_: *mut LeanObject = core::ptr::null_mut();
    v___x_9267_ = l_Array_zipWithMAux___redArg(
        v_inst_9261_,
        v_as_9262_,
        v_bs_9263_,
        v_f_9264_,
        v_i_9265_,
        v_cs_9266_,
    );
    return v___x_9267_;
}
pub unsafe fn l_Array_zipWith___redArg(
    mut v_f_9268_: *mut LeanObject,
    mut v_as_9269_: *mut LeanObject,
    mut v_bs_9270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_9271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9275_: *mut LeanObject = core::ptr::null_mut();
    v___f_9271_ = lean_alloc_closure(
        l_Array_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_9271_, 0, v_f_9268_);
    v___x_9272_ = l_Array_foldl___redArg___closed__9;
    v___x_9273_ = lean_unsigned_to_nat(0);
    v___x_9274_ = l_Array_filter___redArg___closed__0;
    v___x_9275_ = l_Array_zipWithMAux___redArg(
        v___x_9272_,
        v_as_9269_,
        v_bs_9270_,
        v___f_9271_,
        v___x_9273_,
        v___x_9274_,
    );
    return v___x_9275_;
}
pub unsafe fn l_Array_zipWith(
    mut v_00_u03b1_9276_: *mut LeanObject,
    mut v_00_u03b2_9277_: *mut LeanObject,
    mut v_00_u03b3_9278_: *mut LeanObject,
    mut v_f_9279_: *mut LeanObject,
    mut v_as_9280_: *mut LeanObject,
    mut v_bs_9281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_9282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9286_: *mut LeanObject = core::ptr::null_mut();
    v___f_9282_ = lean_alloc_closure(
        l_Array_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_9282_, 0, v_f_9279_);
    v___x_9283_ = l_Array_foldl___redArg___closed__9;
    v___x_9284_ = lean_unsigned_to_nat(0);
    v___x_9285_ = l_Array_filter___redArg___closed__0;
    v___x_9286_ = l_Array_zipWithMAux___redArg(
        v___x_9283_,
        v_as_9280_,
        v_bs_9281_,
        v___f_9282_,
        v___x_9284_,
        v___x_9285_,
    );
    return v___x_9286_;
}
pub unsafe fn l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(
    mut v_as_9287_: *mut LeanObject,
    mut v_bs_9288_: *mut LeanObject,
    mut v_i_9289_: *mut LeanObject,
    mut v_cs_9290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9292_: u8 = 0;
    let mut v___x_9293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9294_: u8 = 0;
    let mut v_a_9295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_9296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9300_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9291_ = lean_array_get_size(v_as_9287_);
                v___x_9292_ = lean_nat_dec_lt(v_i_9289_, v___x_9291_);
                if v___x_9292_ == 0 {
                    lean_dec(v_i_9289_);
                    return v_cs_9290_;
                } else {
                    v___x_9293_ = lean_array_get_size(v_bs_9288_);
                    v___x_9294_ = lean_nat_dec_lt(v_i_9289_, v___x_9293_);
                    if v___x_9294_ == 0 {
                        lean_dec(v_i_9289_);
                        return v_cs_9290_;
                    } else {
                        v_a_9295_ = lean_array_fget_borrowed(v_as_9287_, v_i_9289_);
                        v_b_9296_ = lean_array_fget_borrowed(v_bs_9288_, v_i_9289_);
                        lean_inc(v_b_9296_);
                        lean_inc(v_a_9295_);
                        v___x_9297_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_9297_, 0, v_a_9295_);
                        lean_ctor_set(v___x_9297_, 1, v_b_9296_);
                        v___x_9298_ = lean_unsigned_to_nat(1);
                        v___x_9299_ = lean_nat_add(v_i_9289_, v___x_9298_);
                        lean_dec(v_i_9289_);
                        v___x_9300_ = lean_array_push(v_cs_9290_, v___x_9297_);
                        v_i_9289_ = v___x_9299_;
                        v_cs_9290_ = v___x_9300_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg___boxed(
    mut v_as_9302_: *mut LeanObject,
    mut v_bs_9303_: *mut LeanObject,
    mut v_i_9304_: *mut LeanObject,
    mut v_cs_9305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9306_: *mut LeanObject = core::ptr::null_mut();
    v_res_9306_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(
        v_as_9302_, v_bs_9303_, v_i_9304_, v_cs_9305_,
    );
    lean_dec_ref(v_bs_9303_);
    lean_dec_ref(v_as_9302_);
    return v_res_9306_;
}
pub unsafe fn l_Array_zip___redArg(
    mut v_as_9309_: *mut LeanObject,
    mut v_bs_9310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9313_: *mut LeanObject = core::ptr::null_mut();
    v___x_9311_ = lean_unsigned_to_nat(0);
    v___x_9312_ = l_Array_zip___redArg___closed__0;
    v___x_9313_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(
        v_as_9309_,
        v_bs_9310_,
        v___x_9311_,
        v___x_9312_,
    );
    return v___x_9313_;
}
pub unsafe fn l_Array_zip___redArg___boxed(
    mut v_as_9314_: *mut LeanObject,
    mut v_bs_9315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9316_: *mut LeanObject = core::ptr::null_mut();
    v_res_9316_ = l_Array_zip___redArg(v_as_9314_, v_bs_9315_);
    lean_dec_ref(v_bs_9315_);
    lean_dec_ref(v_as_9314_);
    return v_res_9316_;
}
pub unsafe fn l_Array_zip(
    mut v_00_u03b1_9317_: *mut LeanObject,
    mut v_00_u03b2_9318_: *mut LeanObject,
    mut v_as_9319_: *mut LeanObject,
    mut v_bs_9320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9321_: *mut LeanObject = core::ptr::null_mut();
    v___x_9321_ = l_Array_zip___redArg(v_as_9319_, v_bs_9320_);
    return v___x_9321_;
}
pub unsafe fn l_Array_zip___boxed(
    mut v_00_u03b1_9322_: *mut LeanObject,
    mut v_00_u03b2_9323_: *mut LeanObject,
    mut v_as_9324_: *mut LeanObject,
    mut v_bs_9325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9326_: *mut LeanObject = core::ptr::null_mut();
    v_res_9326_ = l_Array_zip(v_00_u03b1_9322_, v_00_u03b2_9323_, v_as_9324_, v_bs_9325_);
    lean_dec_ref(v_bs_9325_);
    lean_dec_ref(v_as_9324_);
    return v_res_9326_;
}
pub unsafe fn l_Array_zipWithMAux___at___00Array_zip_spec__0(
    mut v_00_u03b1_9327_: *mut LeanObject,
    mut v_00_u03b2_9328_: *mut LeanObject,
    mut v_as_9329_: *mut LeanObject,
    mut v_bs_9330_: *mut LeanObject,
    mut v_i_9331_: *mut LeanObject,
    mut v_cs_9332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9333_: *mut LeanObject = core::ptr::null_mut();
    v___x_9333_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(
        v_as_9329_, v_bs_9330_, v_i_9331_, v_cs_9332_,
    );
    return v___x_9333_;
}
pub unsafe fn l_Array_zipWithMAux___at___00Array_zip_spec__0___boxed(
    mut v_00_u03b1_9334_: *mut LeanObject,
    mut v_00_u03b2_9335_: *mut LeanObject,
    mut v_as_9336_: *mut LeanObject,
    mut v_bs_9337_: *mut LeanObject,
    mut v_i_9338_: *mut LeanObject,
    mut v_cs_9339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9340_: *mut LeanObject = core::ptr::null_mut();
    v_res_9340_ = l_Array_zipWithMAux___at___00Array_zip_spec__0(
        v_00_u03b1_9334_,
        v_00_u03b2_9335_,
        v_as_9336_,
        v_bs_9337_,
        v_i_9338_,
        v_cs_9339_,
    );
    lean_dec_ref(v_bs_9337_);
    lean_dec_ref(v_as_9336_);
    return v_res_9340_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(
    mut v_f_9341_: *mut LeanObject,
    mut v_as_9342_: *mut LeanObject,
    mut v_bs_9343_: *mut LeanObject,
    mut v_i_9344_: *mut LeanObject,
    mut v_cs_9345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_9347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9357_: u8 = 0;
    let mut v___x_9358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9363_: u8 = 0;
    let mut v___x_9364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9365_: u8 = 0;
    let mut v___x_9366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9369_ = lean_array_get_size(v_as_9342_);
                v___x_9370_ = lean_array_get_size(v_bs_9343_);
                v___x_9371_ = lean_nat_dec_le(v___x_9369_, v___x_9370_);
                if v___x_9371_ == 0 {
                    v___y_9362_ = v___x_9369_;
                    state = 3;
                    continue;
                } else {
                    v___y_9362_ = v___x_9370_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_9349_ = lean_unsigned_to_nat(1);
                v___x_9350_ = lean_nat_add(v_i_9344_, v___x_9349_);
                lean_dec(v_i_9344_);
                lean_inc(v_f_9341_);
                v___x_9351_ = lean_apply_2(v_f_9341_, v___y_9347_, v___y_9348_);
                v___x_9352_ = lean_array_push(v_cs_9345_, v___x_9351_);
                v_i_9344_ = v___x_9350_;
                v_cs_9345_ = v___x_9352_;
                state = 0;
                continue;
            }
            2 => {
                v___x_9356_ = lean_array_get_size(v_bs_9343_);
                v___x_9357_ = lean_nat_dec_lt(v_i_9344_, v___x_9356_);
                if v___x_9357_ == 0 {
                    v___x_9358_ = lean_box(0);
                    v___y_9347_ = v___y_9355_;
                    v___y_9348_ = v___x_9358_;
                    state = 1;
                    continue;
                } else {
                    v___x_9359_ = lean_array_fget_borrowed(v_bs_9343_, v_i_9344_);
                    lean_inc(v___x_9359_);
                    v___x_9360_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9360_, 0, v___x_9359_);
                    v___y_9347_ = v___y_9355_;
                    v___y_9348_ = v___x_9360_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_9363_ = lean_nat_dec_lt(v_i_9344_, v___y_9362_);
                lean_dec(v___y_9362_);
                if v___x_9363_ == 0 {
                    lean_dec(v_i_9344_);
                    lean_dec(v_f_9341_);
                    return v_cs_9345_;
                } else {
                    v___x_9364_ = lean_array_get_size(v_as_9342_);
                    v___x_9365_ = lean_nat_dec_lt(v_i_9344_, v___x_9364_);
                    if v___x_9365_ == 0 {
                        v___x_9366_ = lean_box(0);
                        v___y_9355_ = v___x_9366_;
                        state = 2;
                        continue;
                    } else {
                        v___x_9367_ = lean_array_fget_borrowed(v_as_9342_, v_i_9344_);
                        lean_inc(v___x_9367_);
                        v___x_9368_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_9368_, 0, v___x_9367_);
                        v___y_9355_ = v___x_9368_;
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg___boxed(
    mut v_f_9372_: *mut LeanObject,
    mut v_as_9373_: *mut LeanObject,
    mut v_bs_9374_: *mut LeanObject,
    mut v_i_9375_: *mut LeanObject,
    mut v_cs_9376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9377_: *mut LeanObject = core::ptr::null_mut();
    v_res_9377_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(
        v_f_9372_, v_as_9373_, v_bs_9374_, v_i_9375_, v_cs_9376_,
    );
    lean_dec_ref(v_bs_9374_);
    lean_dec_ref(v_as_9373_);
    return v_res_9377_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(
    mut v_00_u03b1_9378_: *mut LeanObject,
    mut v_00_u03b2_9379_: *mut LeanObject,
    mut v_00_u03b3_9380_: *mut LeanObject,
    mut v_f_9381_: *mut LeanObject,
    mut v_as_9382_: *mut LeanObject,
    mut v_bs_9383_: *mut LeanObject,
    mut v_i_9384_: *mut LeanObject,
    mut v_cs_9385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9386_: *mut LeanObject = core::ptr::null_mut();
    v___x_9386_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(
        v_f_9381_, v_as_9382_, v_bs_9383_, v_i_9384_, v_cs_9385_,
    );
    return v___x_9386_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___boxed(
    mut v_00_u03b1_9387_: *mut LeanObject,
    mut v_00_u03b2_9388_: *mut LeanObject,
    mut v_00_u03b3_9389_: *mut LeanObject,
    mut v_f_9390_: *mut LeanObject,
    mut v_as_9391_: *mut LeanObject,
    mut v_bs_9392_: *mut LeanObject,
    mut v_i_9393_: *mut LeanObject,
    mut v_cs_9394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9395_: *mut LeanObject = core::ptr::null_mut();
    v_res_9395_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(
        v_00_u03b1_9387_,
        v_00_u03b2_9388_,
        v_00_u03b3_9389_,
        v_f_9390_,
        v_as_9391_,
        v_bs_9392_,
        v_i_9393_,
        v_cs_9394_,
    );
    lean_dec_ref(v_bs_9392_);
    lean_dec_ref(v_as_9391_);
    return v_res_9395_;
}
pub unsafe fn l_Array_zipWithAll___redArg(
    mut v_f_9396_: *mut LeanObject,
    mut v_as_9397_: *mut LeanObject,
    mut v_bs_9398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9401_: *mut LeanObject = core::ptr::null_mut();
    v___x_9399_ = lean_unsigned_to_nat(0);
    v___x_9400_ = l_Array_filter___redArg___closed__0;
    v___x_9401_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(
        v_f_9396_,
        v_as_9397_,
        v_bs_9398_,
        v___x_9399_,
        v___x_9400_,
    );
    return v___x_9401_;
}
pub unsafe fn l_Array_zipWithAll___redArg___boxed(
    mut v_f_9402_: *mut LeanObject,
    mut v_as_9403_: *mut LeanObject,
    mut v_bs_9404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9405_: *mut LeanObject = core::ptr::null_mut();
    v_res_9405_ = l_Array_zipWithAll___redArg(v_f_9402_, v_as_9403_, v_bs_9404_);
    lean_dec_ref(v_bs_9404_);
    lean_dec_ref(v_as_9403_);
    return v_res_9405_;
}
pub unsafe fn l_Array_zipWithAll(
    mut v_00_u03b1_9406_: *mut LeanObject,
    mut v_00_u03b2_9407_: *mut LeanObject,
    mut v_00_u03b3_9408_: *mut LeanObject,
    mut v_f_9409_: *mut LeanObject,
    mut v_as_9410_: *mut LeanObject,
    mut v_bs_9411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9412_: *mut LeanObject = core::ptr::null_mut();
    v___x_9412_ = l_Array_zipWithAll___redArg(v_f_9409_, v_as_9410_, v_bs_9411_);
    return v___x_9412_;
}
pub unsafe fn l_Array_zipWithAll___boxed(
    mut v_00_u03b1_9413_: *mut LeanObject,
    mut v_00_u03b2_9414_: *mut LeanObject,
    mut v_00_u03b3_9415_: *mut LeanObject,
    mut v_f_9416_: *mut LeanObject,
    mut v_as_9417_: *mut LeanObject,
    mut v_bs_9418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9419_: *mut LeanObject = core::ptr::null_mut();
    v_res_9419_ = l_Array_zipWithAll(
        v_00_u03b1_9413_,
        v_00_u03b2_9414_,
        v_00_u03b3_9415_,
        v_f_9416_,
        v_as_9417_,
        v_bs_9418_,
    );
    lean_dec_ref(v_bs_9418_);
    lean_dec_ref(v_as_9417_);
    return v_res_9419_;
}
pub unsafe fn l_Array_zipWithM___redArg(
    mut v_inst_9420_: *mut LeanObject,
    mut v_f_9421_: *mut LeanObject,
    mut v_as_9422_: *mut LeanObject,
    mut v_bs_9423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9426_: *mut LeanObject = core::ptr::null_mut();
    v___x_9424_ = lean_unsigned_to_nat(0);
    v___x_9425_ = l_Array_filter___redArg___closed__0;
    v___x_9426_ = l_Array_zipWithMAux___redArg(
        v_inst_9420_,
        v_as_9422_,
        v_bs_9423_,
        v_f_9421_,
        v___x_9424_,
        v___x_9425_,
    );
    return v___x_9426_;
}
pub unsafe fn l_Array_zipWithM(
    mut v_00_u03b1_9427_: *mut LeanObject,
    mut v_00_u03b2_9428_: *mut LeanObject,
    mut v_00_u03b3_9429_: *mut LeanObject,
    mut v_m_9430_: *mut LeanObject,
    mut v_inst_9431_: *mut LeanObject,
    mut v_f_9432_: *mut LeanObject,
    mut v_as_9433_: *mut LeanObject,
    mut v_bs_9434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9437_: *mut LeanObject = core::ptr::null_mut();
    v___x_9435_ = lean_unsigned_to_nat(0);
    v___x_9436_ = l_Array_filter___redArg___closed__0;
    v___x_9437_ = l_Array_zipWithMAux___redArg(
        v_inst_9431_,
        v_as_9433_,
        v_bs_9434_,
        v_f_9432_,
        v___x_9435_,
        v___x_9436_,
    );
    return v___x_9437_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(
    mut v_as_9438_: *mut LeanObject,
    mut v_i_9439_: usize,
    mut v_stop_9440_: usize,
    mut v_b_9441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9442_: u8 = 0;
    let mut v_fst_9443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_9446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9450_: u8 = 0;
    let mut v___x_9451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9455_: usize = 0;
    let mut v___x_9456_: usize = 0;
    let mut v_reuseFailAlloc_9458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9442_ = lean_usize_dec_eq(v_i_9439_, v_stop_9440_);
                if v___x_9442_ == 0 {
                    v_fst_9443_ = lean_ctor_get(v_b_9441_, 0);
                    lean_inc(v_fst_9443_);
                    v_snd_9444_ = lean_ctor_get(v_b_9441_, 1);
                    lean_inc(v_snd_9444_);
                    lean_dec_ref(v_b_9441_);
                    v___x_9445_ = lean_array_uget(v_as_9438_, v_i_9439_);
                    v_fst_9446_ = lean_ctor_get(v___x_9445_, 0);
                    v_snd_9447_ = lean_ctor_get(v___x_9445_, 1);
                    v_isSharedCheck_9459_ = (!lean_is_exclusive(v___x_9445_)) as u8;
                    if v_isSharedCheck_9459_ == 0 {
                        v___x_9449_ = v___x_9445_;
                        v_isShared_9450_ = v_isSharedCheck_9459_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_9447_);
                        lean_inc(v_fst_9446_);
                        lean_dec(v___x_9445_);
                        v___x_9449_ = lean_box(0);
                        v_isShared_9450_ = v_isSharedCheck_9459_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_9441_;
                }
            }
            1 => {
                v___x_9451_ = lean_array_push(v_fst_9443_, v_fst_9446_);
                v___x_9452_ = lean_array_push(v_snd_9444_, v_snd_9447_);
                if v_isShared_9450_ == 0 {
                    lean_ctor_set(v___x_9449_, 1, v___x_9452_);
                    lean_ctor_set(v___x_9449_, 0, v___x_9451_);
                    v___x_9454_ = v___x_9449_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9458_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9458_, 0, v___x_9451_);
                    lean_ctor_set(v_reuseFailAlloc_9458_, 1, v___x_9452_);
                    v___x_9454_ = v_reuseFailAlloc_9458_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9455_ = 1usize;
                v___x_9456_ = lean_usize_add(v_i_9439_, v___x_9455_);
                v_i_9439_ = v___x_9456_;
                v_b_9441_ = v___x_9454_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg___boxed(
    mut v_as_9460_: *mut LeanObject,
    mut v_i_9461_: *mut LeanObject,
    mut v_stop_9462_: *mut LeanObject,
    mut v_b_9463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_9464_: usize = 0;
    let mut v_stop_boxed_9465_: usize = 0;
    let mut v_res_9466_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_9464_ = lean_unbox_usize(v_i_9461_);
    lean_dec(v_i_9461_);
    v_stop_boxed_9465_ = lean_unbox_usize(v_stop_9462_);
    lean_dec(v_stop_9462_);
    v_res_9466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_9460_, v_i_boxed_9464_, v_stop_boxed_9465_, v_b_9463_);
    lean_dec_ref(v_as_9460_);
    return v_res_9466_;
}
pub unsafe fn l_Array_unzip___redArg(mut v_as_9467_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_9468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9471_: u8 = 0;
    v___x_9468_ = lean_unsigned_to_nat(0);
    v___x_9469_ = l_Array_partition___redArg___closed__0;
    v___x_9470_ = lean_array_get_size(v_as_9467_);
    v___x_9471_ = lean_nat_dec_lt(v___x_9468_, v___x_9470_);
    if v___x_9471_ == 0 {
        return v___x_9469_;
    } else {
        let mut v___x_9472_: u8 = 0;
        v___x_9472_ = lean_nat_dec_le(v___x_9470_, v___x_9470_);
        if v___x_9472_ == 0 {
            if v___x_9471_ == 0 {
                return v___x_9469_;
            } else {
                let mut v___x_9473_: usize = 0;
                let mut v___x_9474_: usize = 0;
                let mut v___x_9475_: *mut LeanObject = core::ptr::null_mut();
                v___x_9473_ = 0usize;
                v___x_9474_ = lean_usize_of_nat(v___x_9470_);
                v___x_9475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_9467_, v___x_9473_, v___x_9474_, v___x_9469_);
                return v___x_9475_;
            }
        } else {
            let mut v___x_9476_: usize = 0;
            let mut v___x_9477_: usize = 0;
            let mut v___x_9478_: *mut LeanObject = core::ptr::null_mut();
            v___x_9476_ = 0usize;
            v___x_9477_ = lean_usize_of_nat(v___x_9470_);
            v___x_9478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_9467_, v___x_9476_, v___x_9477_, v___x_9469_);
            return v___x_9478_;
        }
    }
}
pub unsafe fn l_Array_unzip___redArg___boxed(mut v_as_9479_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_9480_: *mut LeanObject = core::ptr::null_mut();
    v_res_9480_ = l_Array_unzip___redArg(v_as_9479_);
    lean_dec_ref(v_as_9479_);
    return v_res_9480_;
}
pub unsafe fn l_Array_unzip(
    mut v_00_u03b1_9481_: *mut LeanObject,
    mut v_00_u03b2_9482_: *mut LeanObject,
    mut v_as_9483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9484_: *mut LeanObject = core::ptr::null_mut();
    v___x_9484_ = l_Array_unzip___redArg(v_as_9483_);
    return v___x_9484_;
}
pub unsafe fn l_Array_unzip___boxed(
    mut v_00_u03b1_9485_: *mut LeanObject,
    mut v_00_u03b2_9486_: *mut LeanObject,
    mut v_as_9487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9488_: *mut LeanObject = core::ptr::null_mut();
    v_res_9488_ = l_Array_unzip(v_00_u03b1_9485_, v_00_u03b2_9486_, v_as_9487_);
    lean_dec_ref(v_as_9487_);
    return v_res_9488_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(
    mut v_00_u03b1_9489_: *mut LeanObject,
    mut v_00_u03b2_9490_: *mut LeanObject,
    mut v_as_9491_: *mut LeanObject,
    mut v_i_9492_: usize,
    mut v_stop_9493_: usize,
    mut v_b_9494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9495_: *mut LeanObject = core::ptr::null_mut();
    v___x_9495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_9491_, v_i_9492_, v_stop_9493_, v_b_9494_);
    return v___x_9495_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___boxed(
    mut v_00_u03b1_9496_: *mut LeanObject,
    mut v_00_u03b2_9497_: *mut LeanObject,
    mut v_as_9498_: *mut LeanObject,
    mut v_i_9499_: *mut LeanObject,
    mut v_stop_9500_: *mut LeanObject,
    mut v_b_9501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_9502_: usize = 0;
    let mut v_stop_boxed_9503_: usize = 0;
    let mut v_res_9504_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_9502_ = lean_unbox_usize(v_i_9499_);
    lean_dec(v_i_9499_);
    v_stop_boxed_9503_ = lean_unbox_usize(v_stop_9500_);
    lean_dec(v_stop_9500_);
    v_res_9504_ =
        l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(
            v_00_u03b1_9496_,
            v_00_u03b2_9497_,
            v_as_9498_,
            v_i_boxed_9502_,
            v_stop_boxed_9503_,
            v_b_9501_,
        );
    lean_dec_ref(v_as_9498_);
    return v_res_9504_;
}
pub unsafe fn l_Array_replace___redArg(
    mut v_inst_9505_: *mut LeanObject,
    mut v_xs_9506_: *mut LeanObject,
    mut v_a_9507_: *mut LeanObject,
    mut v_b_9508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9509_: *mut LeanObject = core::ptr::null_mut();
    v___x_9509_ = l_Array_finIdxOf_x3f___redArg(v_inst_9505_, v_xs_9506_, v_a_9507_);
    if lean_obj_tag(v___x_9509_) == 0 {
        lean_dec(v_b_9508_);
        return v_xs_9506_;
    } else {
        let mut v_val_9510_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9511_: *mut LeanObject = core::ptr::null_mut();
        v_val_9510_ = lean_ctor_get(v___x_9509_, 0);
        lean_inc(v_val_9510_);
        lean_dec_ref_known(v___x_9509_, 1);
        v___x_9511_ = lean_array_fset(v_xs_9506_, v_val_9510_, v_b_9508_);
        lean_dec(v_val_9510_);
        return v___x_9511_;
    }
}
pub unsafe fn l_Array_replace(
    mut v_00_u03b1_9512_: *mut LeanObject,
    mut v_inst_9513_: *mut LeanObject,
    mut v_xs_9514_: *mut LeanObject,
    mut v_a_9515_: *mut LeanObject,
    mut v_b_9516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9517_: *mut LeanObject = core::ptr::null_mut();
    v___x_9517_ = l_Array_replace___redArg(v_inst_9513_, v_xs_9514_, v_a_9515_, v_b_9516_);
    return v___x_9517_;
}
pub unsafe fn l_Array_instLT(
    mut v_00_u03b1_9518_: *mut LeanObject,
    mut v_inst_9519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9520_: *mut LeanObject = core::ptr::null_mut();
    v___x_9520_ = lean_box(0);
    return v___x_9520_;
}
pub unsafe fn l_Array_instLE(
    mut v_00_u03b1_9521_: *mut LeanObject,
    mut v_inst_9522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9523_: *mut LeanObject = core::ptr::null_mut();
    v___x_9523_ = lean_box(0);
    return v___x_9523_;
}
pub unsafe fn l_Array_leftpad___redArg(
    mut v_n_9524_: *mut LeanObject,
    mut v_a_9525_: *mut LeanObject,
    mut v_xs_9526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9530_: *mut LeanObject = core::ptr::null_mut();
    v___x_9527_ = lean_array_get_size(v_xs_9526_);
    v___x_9528_ = lean_nat_sub(v_n_9524_, v___x_9527_);
    v___x_9529_ = lean_mk_array(v___x_9528_, v_a_9525_);
    v___x_9530_ = l_Array_append___redArg(v___x_9529_, v_xs_9526_);
    return v___x_9530_;
}
pub unsafe fn l_Array_leftpad___redArg___boxed(
    mut v_n_9531_: *mut LeanObject,
    mut v_a_9532_: *mut LeanObject,
    mut v_xs_9533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9534_: *mut LeanObject = core::ptr::null_mut();
    v_res_9534_ = l_Array_leftpad___redArg(v_n_9531_, v_a_9532_, v_xs_9533_);
    lean_dec_ref(v_xs_9533_);
    lean_dec(v_n_9531_);
    return v_res_9534_;
}
pub unsafe fn l_Array_leftpad(
    mut v_00_u03b1_9535_: *mut LeanObject,
    mut v_n_9536_: *mut LeanObject,
    mut v_a_9537_: *mut LeanObject,
    mut v_xs_9538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9539_: *mut LeanObject = core::ptr::null_mut();
    v___x_9539_ = l_Array_leftpad___redArg(v_n_9536_, v_a_9537_, v_xs_9538_);
    return v___x_9539_;
}
pub unsafe fn l_Array_leftpad___boxed(
    mut v_00_u03b1_9540_: *mut LeanObject,
    mut v_n_9541_: *mut LeanObject,
    mut v_a_9542_: *mut LeanObject,
    mut v_xs_9543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9544_: *mut LeanObject = core::ptr::null_mut();
    v_res_9544_ = l_Array_leftpad(v_00_u03b1_9540_, v_n_9541_, v_a_9542_, v_xs_9543_);
    lean_dec_ref(v_xs_9543_);
    lean_dec(v_n_9541_);
    return v_res_9544_;
}
pub unsafe fn l_Array_rightpad___redArg(
    mut v_n_9545_: *mut LeanObject,
    mut v_a_9546_: *mut LeanObject,
    mut v_xs_9547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9551_: *mut LeanObject = core::ptr::null_mut();
    v___x_9548_ = lean_array_get_size(v_xs_9547_);
    v___x_9549_ = lean_nat_sub(v_n_9545_, v___x_9548_);
    v___x_9550_ = lean_mk_array(v___x_9549_, v_a_9546_);
    v___x_9551_ = l_Array_append___redArg(v_xs_9547_, v___x_9550_);
    lean_dec_ref(v___x_9550_);
    return v___x_9551_;
}
pub unsafe fn l_Array_rightpad___redArg___boxed(
    mut v_n_9552_: *mut LeanObject,
    mut v_a_9553_: *mut LeanObject,
    mut v_xs_9554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9555_: *mut LeanObject = core::ptr::null_mut();
    v_res_9555_ = l_Array_rightpad___redArg(v_n_9552_, v_a_9553_, v_xs_9554_);
    lean_dec(v_n_9552_);
    return v_res_9555_;
}
pub unsafe fn l_Array_rightpad(
    mut v_00_u03b1_9556_: *mut LeanObject,
    mut v_n_9557_: *mut LeanObject,
    mut v_a_9558_: *mut LeanObject,
    mut v_xs_9559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9560_: *mut LeanObject = core::ptr::null_mut();
    v___x_9560_ = l_Array_rightpad___redArg(v_n_9557_, v_a_9558_, v_xs_9559_);
    return v___x_9560_;
}
pub unsafe fn l_Array_rightpad___boxed(
    mut v_00_u03b1_9561_: *mut LeanObject,
    mut v_n_9562_: *mut LeanObject,
    mut v_a_9563_: *mut LeanObject,
    mut v_xs_9564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9565_: *mut LeanObject = core::ptr::null_mut();
    v_res_9565_ = l_Array_rightpad(v_00_u03b1_9561_, v_n_9562_, v_a_9563_, v_xs_9564_);
    lean_dec(v_n_9562_);
    return v_res_9565_;
}
pub unsafe fn l_Array_reduceOption___redArg___lam__0(
    mut v_x_9566_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_9566_);
    return v_x_9566_;
}
pub unsafe fn l_Array_reduceOption___redArg___lam__0___boxed(
    mut v_x_9567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9568_: *mut LeanObject = core::ptr::null_mut();
    v_res_9568_ = l_Array_reduceOption___redArg___lam__0(v_x_9567_);
    lean_dec(v_x_9567_);
    return v_res_9568_;
}
pub unsafe fn l_Array_reduceOption___redArg(mut v_as_9570_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_9571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9575_: *mut LeanObject = core::ptr::null_mut();
    v___f_9571_ = l_Array_reduceOption___redArg___closed__0;
    v___x_9572_ = lean_unsigned_to_nat(0);
    v___x_9573_ = lean_array_get_size(v_as_9570_);
    v___x_9574_ = l_Array_foldl___redArg___closed__9;
    v___x_9575_ = l_Array_filterMapM___redArg(
        v___x_9574_,
        v___f_9571_,
        v_as_9570_,
        v___x_9572_,
        v___x_9573_,
    );
    return v___x_9575_;
}
pub unsafe fn l_Array_reduceOption(
    mut v_00_u03b1_9576_: *mut LeanObject,
    mut v_as_9577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_9578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9582_: *mut LeanObject = core::ptr::null_mut();
    v___f_9578_ = l_Array_reduceOption___redArg___closed__0;
    v___x_9579_ = lean_unsigned_to_nat(0);
    v___x_9580_ = lean_array_get_size(v_as_9577_);
    v___x_9581_ = l_Array_foldl___redArg___closed__9;
    v___x_9582_ = l_Array_filterMapM___redArg(
        v___x_9581_,
        v___f_9578_,
        v_as_9577_,
        v___x_9579_,
        v___x_9580_,
    );
    return v___x_9582_;
}
pub unsafe fn l_Array_eraseReps___redArg___lam__0(
    mut v_inst_9583_: *mut LeanObject,
    mut v_x1_9584_: *mut LeanObject,
    mut v_x2_9585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_9586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9589_: u8 = 0;
    let mut v___x_9591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9592_: u8 = 0;
    let mut v___x_9593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9597_: u8 = 0;
    let mut v_unused_9598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_9599_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_9586_ = lean_ctor_get(v_x1_9584_, 0);
                v_snd_9587_ = lean_ctor_get(v_x1_9584_, 1);
                lean_inc(v_fst_9586_);
                lean_inc(v_x2_9585_);
                v___x_9588_ = lean_apply_2(v_inst_9583_, v_x2_9585_, v_fst_9586_);
                v___x_9589_ = (lean_unbox(v___x_9588_) as u8);
                if v___x_9589_ == 0 {
                    lean_inc(v_snd_9587_);
                    lean_inc(v_fst_9586_);
                    v_isSharedCheck_9597_ = (!lean_is_exclusive(v_x1_9584_)) as u8;
                    if v_isSharedCheck_9597_ == 0 {
                        v_unused_9598_ = lean_ctor_get(v_x1_9584_, 1);
                        lean_dec(v_unused_9598_);
                        v_unused_9599_ = lean_ctor_get(v_x1_9584_, 0);
                        lean_dec(v_unused_9599_);
                        v___x_9591_ = v_x1_9584_;
                        v_isShared_9592_ = v_isSharedCheck_9597_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_x1_9584_);
                        v___x_9591_ = lean_box(0);
                        v_isShared_9592_ = v_isSharedCheck_9597_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_x2_9585_);
                    return v_x1_9584_;
                }
            }
            1 => {
                v___x_9593_ = lean_array_push(v_snd_9587_, v_fst_9586_);
                if v_isShared_9592_ == 0 {
                    lean_ctor_set(v___x_9591_, 1, v___x_9593_);
                    lean_ctor_set(v___x_9591_, 0, v_x2_9585_);
                    v___x_9595_ = v___x_9591_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9596_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9596_, 0, v_x2_9585_);
                    lean_ctor_set(v_reuseFailAlloc_9596_, 1, v___x_9593_);
                    v___x_9595_ = v_reuseFailAlloc_9596_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9595_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_eraseReps___redArg(
    mut v_inst_9600_: *mut LeanObject,
    mut v_as_9601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_9603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_9604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9609_: u8 = 0;
    let mut v___x_9610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9617_: u8 = 0;
    let mut v___x_9618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9619_: usize = 0;
    let mut v___x_9620_: usize = 0;
    let mut v___x_9621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9622_: usize = 0;
    let mut v___x_9623_: usize = 0;
    let mut v___x_9624_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9607_ = lean_unsigned_to_nat(0);
                v___x_9608_ = lean_array_get_size(v_as_9601_);
                v___x_9609_ = lean_nat_dec_lt(v___x_9607_, v___x_9608_);
                if v___x_9609_ == 0 {
                    lean_dec_ref(v_as_9601_);
                    lean_dec_ref(v_inst_9600_);
                    v___x_9610_ = l_Array_filter___redArg___closed__0;
                    return v___x_9610_;
                } else {
                    v___x_9611_ = lean_array_fget_borrowed(v_as_9601_, v___x_9607_);
                    v___x_9612_ = l_Array_filter___redArg___closed__0;
                    v___x_9613_ = l_Array_foldl___redArg___closed__9;
                    if v___x_9609_ == 0 {
                        lean_inc(v___x_9611_);
                        lean_dec_ref(v_as_9601_);
                        lean_dec_ref(v_inst_9600_);
                        v___x_9614_ = lean_array_push(v___x_9612_, v___x_9611_);
                        return v___x_9614_;
                    } else {
                        v___f_9615_ = lean_alloc_closure(
                            l_Array_eraseReps___redArg___lam__0 as *mut core::ffi::c_void,
                            3,
                            1,
                        );
                        lean_closure_set(v___f_9615_, 0, v_inst_9600_);
                        lean_inc(v___x_9611_);
                        v___x_9616_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_9616_, 0, v___x_9611_);
                        lean_ctor_set(v___x_9616_, 1, v___x_9612_);
                        v___x_9617_ = lean_nat_dec_le(v___x_9608_, v___x_9608_);
                        if v___x_9617_ == 0 {
                            if v___x_9609_ == 0 {
                                lean_inc(v___x_9611_);
                                lean_dec_ref_known(v___x_9616_, 2);
                                lean_dec_ref(v___f_9615_);
                                lean_dec_ref(v_as_9601_);
                                v___x_9618_ = lean_array_push(v___x_9612_, v___x_9611_);
                                return v___x_9618_;
                            } else {
                                v___x_9619_ = 0usize;
                                v___x_9620_ = lean_usize_of_nat(v___x_9608_);
                                v___x_9621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_9613_, v___f_9615_, v_as_9601_, v___x_9619_, v___x_9620_, v___x_9616_);
                                v___y_9603_ = v___x_9621_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_9622_ = 0usize;
                            v___x_9623_ = lean_usize_of_nat(v___x_9608_);
                            v___x_9624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_9613_, v___f_9615_, v_as_9601_, v___x_9622_, v___x_9623_, v___x_9616_);
                            v___y_9603_ = v___x_9624_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_9604_ = lean_ctor_get(v___y_9603_, 0);
                lean_inc(v_fst_9604_);
                v_snd_9605_ = lean_ctor_get(v___y_9603_, 1);
                lean_inc(v_snd_9605_);
                lean_dec_ref(v___y_9603_);
                v___x_9606_ = lean_array_push(v_snd_9605_, v_fst_9604_);
                return v___x_9606_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_eraseReps(
    mut v_00_u03b1_9625_: *mut LeanObject,
    mut v_inst_9626_: *mut LeanObject,
    mut v_as_9627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9628_: *mut LeanObject = core::ptr::null_mut();
    v___x_9628_ = l_Array_eraseReps___redArg(v_inst_9626_, v_as_9627_);
    return v___x_9628_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(
    mut v_inst_9629_: *mut LeanObject,
    mut v_as_9630_: *mut LeanObject,
    mut v_a_9631_: *mut LeanObject,
    mut v_x_9632_: *mut LeanObject,
) -> u8 {
    let mut v_zero_9633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_9634_: u8 = 0;
    let mut v_one_9635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_9636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9639_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_9633_ = lean_unsigned_to_nat(0);
                v_isZero_9634_ = lean_nat_dec_eq(v_x_9632_, v_zero_9633_);
                if v_isZero_9634_ == 1 {
                    lean_dec(v_x_9632_);
                    lean_dec(v_a_9631_);
                    lean_dec_ref(v_inst_9629_);
                    return v_isZero_9634_;
                } else {
                    v_one_9635_ = lean_unsigned_to_nat(1);
                    v_n_9636_ = lean_nat_sub(v_x_9632_, v_one_9635_);
                    lean_dec(v_x_9632_);
                    v___x_9637_ = lean_array_fget_borrowed(v_as_9630_, v_n_9636_);
                    lean_inc_ref(v_inst_9629_);
                    lean_inc(v___x_9637_);
                    lean_inc(v_a_9631_);
                    v___x_9638_ = lean_apply_2(v_inst_9629_, v_a_9631_, v___x_9637_);
                    v___x_9639_ = (lean_unbox(v___x_9638_) as u8);
                    if v___x_9639_ == 0 {
                        v_x_9632_ = v_n_9636_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_n_9636_);
                        lean_dec(v_a_9631_);
                        lean_dec_ref(v_inst_9629_);
                        return v_isZero_9634_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg___boxed(
    mut v_inst_9641_: *mut LeanObject,
    mut v_as_9642_: *mut LeanObject,
    mut v_a_9643_: *mut LeanObject,
    mut v_x_9644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9645_: u8 = 0;
    let mut v_r_9646_: *mut LeanObject = core::ptr::null_mut();
    v_res_9645_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(
        v_inst_9641_,
        v_as_9642_,
        v_a_9643_,
        v_x_9644_,
    );
    lean_dec_ref(v_as_9642_);
    v_r_9646_ = lean_box((v_res_9645_) as usize);
    return v_r_9646_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(
    mut v_00_u03b1_9647_: *mut LeanObject,
    mut v_inst_9648_: *mut LeanObject,
    mut v_as_9649_: *mut LeanObject,
    mut v_a_9650_: *mut LeanObject,
    mut v_x_9651_: *mut LeanObject,
    mut v_x_9652_: *mut LeanObject,
) -> u8 {
    let mut v___x_9653_: u8 = 0;
    v___x_9653_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(
        v_inst_9648_,
        v_as_9649_,
        v_a_9650_,
        v_x_9651_,
    );
    return v___x_9653_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___boxed(
    mut v_00_u03b1_9654_: *mut LeanObject,
    mut v_inst_9655_: *mut LeanObject,
    mut v_as_9656_: *mut LeanObject,
    mut v_a_9657_: *mut LeanObject,
    mut v_x_9658_: *mut LeanObject,
    mut v_x_9659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9660_: u8 = 0;
    let mut v_r_9661_: *mut LeanObject = core::ptr::null_mut();
    v_res_9660_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(
        v_00_u03b1_9654_,
        v_inst_9655_,
        v_as_9656_,
        v_a_9657_,
        v_x_9658_,
        v_x_9659_,
    );
    lean_dec_ref(v_as_9656_);
    v_r_9661_ = lean_box((v_res_9660_) as usize);
    return v_r_9661_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(
    mut v_inst_9662_: *mut LeanObject,
    mut v_as_9663_: *mut LeanObject,
    mut v_i_9664_: *mut LeanObject,
) -> u8 {
    let mut v___x_9665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9666_: u8 = 0;
    let mut v___x_9667_: u8 = 0;
    let mut v___x_9668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9669_: u8 = 0;
    let mut v___x_9670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9671_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9665_ = lean_array_get_size(v_as_9663_);
                v___x_9666_ = lean_nat_dec_lt(v_i_9664_, v___x_9665_);
                if v___x_9666_ == 0 {
                    lean_dec(v_i_9664_);
                    lean_dec_ref(v_inst_9662_);
                    v___x_9667_ = 1;
                    return v___x_9667_;
                } else {
                    v___x_9668_ = lean_array_fget_borrowed(v_as_9663_, v_i_9664_);
                    lean_inc(v_i_9664_);
                    lean_inc(v___x_9668_);
                    lean_inc_ref(v_inst_9662_);
                    v___x_9669_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(
                        v_inst_9662_,
                        v_as_9663_,
                        v___x_9668_,
                        v_i_9664_,
                    );
                    if v___x_9669_ == 0 {
                        lean_dec(v_i_9664_);
                        lean_dec_ref(v_inst_9662_);
                        return v___x_9669_;
                    } else {
                        v___x_9670_ = lean_unsigned_to_nat(1);
                        v___x_9671_ = lean_nat_add(v_i_9664_, v___x_9670_);
                        lean_dec(v_i_9664_);
                        v_i_9664_ = v___x_9671_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg___boxed(
    mut v_inst_9673_: *mut LeanObject,
    mut v_as_9674_: *mut LeanObject,
    mut v_i_9675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9676_: u8 = 0;
    let mut v_r_9677_: *mut LeanObject = core::ptr::null_mut();
    v_res_9676_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(
        v_inst_9673_,
        v_as_9674_,
        v_i_9675_,
    );
    lean_dec_ref(v_as_9674_);
    v_r_9677_ = lean_box((v_res_9676_) as usize);
    return v_r_9677_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAux(
    mut v_00_u03b1_9678_: *mut LeanObject,
    mut v_inst_9679_: *mut LeanObject,
    mut v_as_9680_: *mut LeanObject,
    mut v_i_9681_: *mut LeanObject,
) -> u8 {
    let mut v___x_9682_: u8 = 0;
    v___x_9682_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(
        v_inst_9679_,
        v_as_9680_,
        v_i_9681_,
    );
    return v___x_9682_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAux___boxed(
    mut v_00_u03b1_9683_: *mut LeanObject,
    mut v_inst_9684_: *mut LeanObject,
    mut v_as_9685_: *mut LeanObject,
    mut v_i_9686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9687_: u8 = 0;
    let mut v_r_9688_: *mut LeanObject = core::ptr::null_mut();
    v_res_9687_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux(
        v_00_u03b1_9683_,
        v_inst_9684_,
        v_as_9685_,
        v_i_9686_,
    );
    lean_dec_ref(v_as_9685_);
    v_r_9688_ = lean_box((v_res_9687_) as usize);
    return v_r_9688_;
}
pub unsafe fn l_Array_allDiff___redArg(
    mut v_inst_9689_: *mut LeanObject,
    mut v_as_9690_: *mut LeanObject,
) -> u8 {
    let mut v___x_9691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9692_: u8 = 0;
    v___x_9691_ = lean_unsigned_to_nat(0);
    v___x_9692_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(
        v_inst_9689_,
        v_as_9690_,
        v___x_9691_,
    );
    return v___x_9692_;
}
pub unsafe fn l_Array_allDiff___redArg___boxed(
    mut v_inst_9693_: *mut LeanObject,
    mut v_as_9694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9695_: u8 = 0;
    let mut v_r_9696_: *mut LeanObject = core::ptr::null_mut();
    v_res_9695_ = l_Array_allDiff___redArg(v_inst_9693_, v_as_9694_);
    lean_dec_ref(v_as_9694_);
    v_r_9696_ = lean_box((v_res_9695_) as usize);
    return v_r_9696_;
}
pub unsafe fn l_Array_allDiff(
    mut v_00_u03b1_9697_: *mut LeanObject,
    mut v_inst_9698_: *mut LeanObject,
    mut v_as_9699_: *mut LeanObject,
) -> u8 {
    let mut v___x_9700_: u8 = 0;
    v___x_9700_ = l_Array_allDiff___redArg(v_inst_9698_, v_as_9699_);
    return v___x_9700_;
}
pub unsafe fn l_Array_allDiff___boxed(
    mut v_00_u03b1_9701_: *mut LeanObject,
    mut v_inst_9702_: *mut LeanObject,
    mut v_as_9703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9704_: u8 = 0;
    let mut v_r_9705_: *mut LeanObject = core::ptr::null_mut();
    v_res_9704_ = l_Array_allDiff(v_00_u03b1_9701_, v_inst_9702_, v_as_9703_);
    lean_dec_ref(v_as_9703_);
    v_r_9705_ = lean_box((v_res_9704_) as usize);
    return v_r_9705_;
}
pub unsafe fn l_Array_getEvenElems___redArg___lam__0(
    mut v___x_9706_: u8,
    mut v_x1_9707_: *mut LeanObject,
    mut v_x2_9708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_9709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9710_: u8 = 0;
    let mut v_snd_9711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9714_: u8 = 0;
    let mut v___x_9715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9719_: u8 = 0;
    let mut v_unused_9720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9724_: u8 = 0;
    let mut v___x_9725_: u8 = 0;
    let mut v___x_9726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9731_: u8 = 0;
    let mut v_unused_9732_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_9709_ = lean_ctor_get(v_x1_9707_, 0);
                v___x_9710_ = (lean_unbox(v_fst_9709_) as u8);
                if v___x_9710_ == 0 {
                    lean_dec(v_x2_9708_);
                    v_snd_9711_ = lean_ctor_get(v_x1_9707_, 1);
                    v_isSharedCheck_9719_ = (!lean_is_exclusive(v_x1_9707_)) as u8;
                    if v_isSharedCheck_9719_ == 0 {
                        v_unused_9720_ = lean_ctor_get(v_x1_9707_, 0);
                        lean_dec(v_unused_9720_);
                        v___x_9713_ = v_x1_9707_;
                        v_isShared_9714_ = v_isSharedCheck_9719_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_9711_);
                        lean_dec(v_x1_9707_);
                        v___x_9713_ = lean_box(0);
                        v_isShared_9714_ = v_isSharedCheck_9719_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_snd_9721_ = lean_ctor_get(v_x1_9707_, 1);
                    v_isSharedCheck_9731_ = (!lean_is_exclusive(v_x1_9707_)) as u8;
                    if v_isSharedCheck_9731_ == 0 {
                        v_unused_9732_ = lean_ctor_get(v_x1_9707_, 0);
                        lean_dec(v_unused_9732_);
                        v___x_9723_ = v_x1_9707_;
                        v_isShared_9724_ = v_isSharedCheck_9731_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snd_9721_);
                        lean_dec(v_x1_9707_);
                        v___x_9723_ = lean_box(0);
                        v_isShared_9724_ = v_isSharedCheck_9731_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9715_ = lean_box((v___x_9706_) as usize);
                if v_isShared_9714_ == 0 {
                    lean_ctor_set(v___x_9713_, 0, v___x_9715_);
                    v___x_9717_ = v___x_9713_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9718_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9718_, 0, v___x_9715_);
                    lean_ctor_set(v_reuseFailAlloc_9718_, 1, v_snd_9711_);
                    v___x_9717_ = v_reuseFailAlloc_9718_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9717_;
            }
            3 => {
                v___x_9725_ = 0;
                v___x_9726_ = lean_array_push(v_snd_9721_, v_x2_9708_);
                v___x_9727_ = lean_box((v___x_9725_) as usize);
                if v_isShared_9724_ == 0 {
                    lean_ctor_set(v___x_9723_, 1, v___x_9726_);
                    lean_ctor_set(v___x_9723_, 0, v___x_9727_);
                    v___x_9729_ = v___x_9723_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9730_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9730_, 0, v___x_9727_);
                    lean_ctor_set(v_reuseFailAlloc_9730_, 1, v___x_9726_);
                    v___x_9729_ = v_reuseFailAlloc_9730_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9729_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_getEvenElems___redArg___lam__0___boxed(
    mut v___x_9733_: *mut LeanObject,
    mut v_x1_9734_: *mut LeanObject,
    mut v_x2_9735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_172__boxed_9736_: u8 = 0;
    let mut v_res_9737_: *mut LeanObject = core::ptr::null_mut();
    v___x_172__boxed_9736_ = (lean_unbox(v___x_9733_) as u8);
    v_res_9737_ =
        l_Array_getEvenElems___redArg___lam__0(v___x_172__boxed_9736_, v_x1_9734_, v_x2_9735_);
    return v_res_9737_;
}
pub unsafe fn l_Array_getEvenElems___redArg(mut v_as_9738_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_9739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9743_: u8 = 0;
    v___x_9739_ = lean_unsigned_to_nat(0);
    v___x_9740_ = l_Array_instEmptyCollection___closed__0;
    v___x_9741_ = lean_array_get_size(v_as_9738_);
    v___x_9742_ = l_Array_foldl___redArg___closed__9;
    v___x_9743_ = lean_nat_dec_lt(v___x_9739_, v___x_9741_);
    if v___x_9743_ == 0 {
        lean_dec_ref(v_as_9738_);
        return v___x_9740_;
    } else {
        let mut v___x_9744_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_9745_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9746_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9747_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9748_: u8 = 0;
        v___x_9744_ = lean_box((v___x_9743_) as usize);
        v___f_9745_ = lean_alloc_closure(
            l_Array_getEvenElems___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_9745_, 0, v___x_9744_);
        v___x_9746_ = lean_box((v___x_9743_) as usize);
        v___x_9747_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_9747_, 0, v___x_9746_);
        lean_ctor_set(v___x_9747_, 1, v___x_9740_);
        v___x_9748_ = lean_nat_dec_le(v___x_9741_, v___x_9741_);
        if v___x_9748_ == 0 {
            if v___x_9743_ == 0 {
                lean_dec_ref_known(v___x_9747_, 2);
                lean_dec_ref(v___f_9745_);
                lean_dec_ref(v_as_9738_);
                return v___x_9740_;
            } else {
                let mut v___x_9749_: usize = 0;
                let mut v___x_9750_: usize = 0;
                let mut v___x_9751_: *mut LeanObject = core::ptr::null_mut();
                let mut v_snd_9752_: *mut LeanObject = core::ptr::null_mut();
                v___x_9749_ = 0usize;
                v___x_9750_ = lean_usize_of_nat(v___x_9741_);
                v___x_9751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v___x_9742_,
                    v___f_9745_,
                    v_as_9738_,
                    v___x_9749_,
                    v___x_9750_,
                    v___x_9747_,
                );
                v_snd_9752_ = lean_ctor_get(v___x_9751_, 1);
                lean_inc(v_snd_9752_);
                lean_dec(v___x_9751_);
                return v_snd_9752_;
            }
        } else {
            let mut v___x_9753_: usize = 0;
            let mut v___x_9754_: usize = 0;
            let mut v___x_9755_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_9756_: *mut LeanObject = core::ptr::null_mut();
            v___x_9753_ = 0usize;
            v___x_9754_ = lean_usize_of_nat(v___x_9741_);
            v___x_9755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v___x_9742_,
                v___f_9745_,
                v_as_9738_,
                v___x_9753_,
                v___x_9754_,
                v___x_9747_,
            );
            v_snd_9756_ = lean_ctor_get(v___x_9755_, 1);
            lean_inc(v_snd_9756_);
            lean_dec(v___x_9755_);
            return v_snd_9756_;
        }
    }
}
pub unsafe fn l_Array_getEvenElems(
    mut v_00_u03b1_9757_: *mut LeanObject,
    mut v_as_9758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9763_: u8 = 0;
    v___x_9759_ = lean_unsigned_to_nat(0);
    v___x_9760_ = l_Array_instEmptyCollection___closed__0;
    v___x_9761_ = lean_array_get_size(v_as_9758_);
    v___x_9762_ = l_Array_foldl___redArg___closed__9;
    v___x_9763_ = lean_nat_dec_lt(v___x_9759_, v___x_9761_);
    if v___x_9763_ == 0 {
        lean_dec_ref(v_as_9758_);
        return v___x_9760_;
    } else {
        let mut v___x_9764_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_9765_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9766_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9767_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9768_: u8 = 0;
        v___x_9764_ = lean_box((v___x_9763_) as usize);
        v___f_9765_ = lean_alloc_closure(
            l_Array_getEvenElems___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_9765_, 0, v___x_9764_);
        v___x_9766_ = lean_box((v___x_9763_) as usize);
        v___x_9767_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_9767_, 0, v___x_9766_);
        lean_ctor_set(v___x_9767_, 1, v___x_9760_);
        v___x_9768_ = lean_nat_dec_le(v___x_9761_, v___x_9761_);
        if v___x_9768_ == 0 {
            if v___x_9763_ == 0 {
                lean_dec_ref_known(v___x_9767_, 2);
                lean_dec_ref(v___f_9765_);
                lean_dec_ref(v_as_9758_);
                return v___x_9760_;
            } else {
                let mut v___x_9769_: usize = 0;
                let mut v___x_9770_: usize = 0;
                let mut v___x_9771_: *mut LeanObject = core::ptr::null_mut();
                let mut v_snd_9772_: *mut LeanObject = core::ptr::null_mut();
                v___x_9769_ = 0usize;
                v___x_9770_ = lean_usize_of_nat(v___x_9761_);
                v___x_9771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v___x_9762_,
                    v___f_9765_,
                    v_as_9758_,
                    v___x_9769_,
                    v___x_9770_,
                    v___x_9767_,
                );
                v_snd_9772_ = lean_ctor_get(v___x_9771_, 1);
                lean_inc(v_snd_9772_);
                lean_dec(v___x_9771_);
                return v_snd_9772_;
            }
        } else {
            let mut v___x_9773_: usize = 0;
            let mut v___x_9774_: usize = 0;
            let mut v___x_9775_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_9776_: *mut LeanObject = core::ptr::null_mut();
            v___x_9773_ = 0usize;
            v___x_9774_ = lean_usize_of_nat(v___x_9761_);
            v___x_9775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v___x_9762_,
                v___f_9765_,
                v_as_9758_,
                v___x_9773_,
                v___x_9774_,
                v___x_9767_,
            );
            v_snd_9776_ = lean_ctor_get(v___x_9775_, 1);
            lean_inc(v_snd_9776_);
            lean_dec(v___x_9775_);
            return v_snd_9776_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_9782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9783_: *mut LeanObject = core::ptr::null_mut();
    v___x_9782_ = l_term_x23_x5b___x2c_x5d___closed__4;
    v___x_9783_ = lean_string_length(v___x_9782_);
    return v___x_9783_;
}
pub unsafe fn _init_l_Array_repr___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_9784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9785_: *mut LeanObject = core::ptr::null_mut();
    v___x_9784_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_repr___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Array_repr___redArg___closed__2_once),
        _init_l_Array_repr___redArg___closed__2,
    );
    v___x_9785_ = lean_nat_to_int(v___x_9784_);
    return v___x_9785_;
}
pub unsafe fn l_Array_repr___redArg(
    mut v_inst_9793_: *mut LeanObject,
    mut v_xs_9794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9797_: u8 = 0;
    v___x_9795_ = lean_array_get_size(v_xs_9794_);
    v___x_9796_ = lean_unsigned_to_nat(0);
    v___x_9797_ = lean_nat_dec_eq(v___x_9795_, v___x_9796_);
    if v___x_9797_ == 0 {
        let mut v_x_9798_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9799_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9800_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9801_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9802_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9803_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9804_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9805_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9806_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9807_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9808_: *mut LeanObject = core::ptr::null_mut();
        v_x_9798_ = lean_alloc_closure(l_repr as *mut core::ffi::c_void, 3, 2);
        lean_closure_set(v_x_9798_, 0, lean_box(0));
        lean_closure_set(v_x_9798_, 1, v_inst_9793_);
        v___x_9799_ = lean_array_to_list(v_xs_9794_);
        v___x_9800_ = l_Array_repr___redArg___closed__1;
        v___x_9801_ = l_Std_Format_joinSep___redArg(v_x_9798_, v___x_9799_, v___x_9800_);
        v___x_9802_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Array_repr___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Array_repr___redArg___closed__3_once),
            _init_l_Array_repr___redArg___closed__3,
        );
        v___x_9803_ = l_Array_repr___redArg___closed__4;
        v___x_9804_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_9804_, 0, v___x_9803_);
        lean_ctor_set(v___x_9804_, 1, v___x_9801_);
        v___x_9805_ = l_Array_repr___redArg___closed__5;
        v___x_9806_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_9806_, 0, v___x_9804_);
        lean_ctor_set(v___x_9806_, 1, v___x_9805_);
        v___x_9807_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_9807_, 0, v___x_9802_);
        lean_ctor_set(v___x_9807_, 1, v___x_9806_);
        v___x_9808_ = l_Std_Format_fill(v___x_9807_);
        return v___x_9808_;
    } else {
        let mut v___x_9809_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_9794_);
        lean_dec_ref(v_inst_9793_);
        v___x_9809_ = l_Array_repr___redArg___closed__7;
        return v___x_9809_;
    }
}
pub unsafe fn l_Array_repr(
    mut v_00_u03b1_9810_: *mut LeanObject,
    mut v_inst_9811_: *mut LeanObject,
    mut v_xs_9812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9813_: *mut LeanObject = core::ptr::null_mut();
    v___x_9813_ = l_Array_repr___redArg(v_inst_9811_, v_xs_9812_);
    return v___x_9813_;
}
pub unsafe fn l_Array_instRepr___redArg___lam__0(
    mut v_inst_9814_: *mut LeanObject,
    mut v_xs_9815_: *mut LeanObject,
    mut v_x_9816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9817_: *mut LeanObject = core::ptr::null_mut();
    v___x_9817_ = l_Array_repr___redArg(v_inst_9814_, v_xs_9815_);
    return v___x_9817_;
}
pub unsafe fn l_Array_instRepr___redArg___lam__0___boxed(
    mut v_inst_9818_: *mut LeanObject,
    mut v_xs_9819_: *mut LeanObject,
    mut v_x_9820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9821_: *mut LeanObject = core::ptr::null_mut();
    v_res_9821_ = l_Array_instRepr___redArg___lam__0(v_inst_9818_, v_xs_9819_, v_x_9820_);
    lean_dec(v_x_9820_);
    return v_res_9821_;
}
pub unsafe fn l_Array_instRepr___redArg(mut v_inst_9822_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_9823_: *mut LeanObject = core::ptr::null_mut();
    v___f_9823_ = lean_alloc_closure(
        l_Array_instRepr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_9823_, 0, v_inst_9822_);
    return v___f_9823_;
}
pub unsafe fn l_Array_instRepr(
    mut v_00_u03b1_9824_: *mut LeanObject,
    mut v_inst_9825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_9826_: *mut LeanObject = core::ptr::null_mut();
    v___f_9826_ = lean_alloc_closure(
        l_Array_instRepr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_9826_, 0, v_inst_9825_);
    return v___f_9826_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_GetElem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_ToArrayImpl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Set(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_WF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_MetaTypes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Array_swap___auto__1 = _init_l_Array_swap___auto__1();
    lean_mark_persistent(l_Array_swap___auto__1);
    l_Array_swap___auto__3 = _init_l_Array_swap___auto__3();
    lean_mark_persistent(l_Array_swap___auto__3);
    l_Array_back___auto__1 = _init_l_Array_back___auto__1();
    lean_mark_persistent(l_Array_back___auto__1);
    l_Array_swapAt___auto__1 = _init_l_Array_swapAt___auto__1();
    lean_mark_persistent(l_Array_swapAt___auto__1);
    l_Array_eraseIdx___auto__1 = _init_l_Array_eraseIdx___auto__1();
    lean_mark_persistent(l_Array_eraseIdx___auto__1);
    l_Array_insertIdx___auto__1 = _init_l_Array_insertIdx___auto__1();
    lean_mark_persistent(l_Array_insertIdx___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_GetElem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_ToArrayImpl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Set(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_WF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_MetaTypes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Array_Basic(builtin);
}
