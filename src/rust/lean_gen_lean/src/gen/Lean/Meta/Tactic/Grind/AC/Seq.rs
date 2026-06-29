// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.Seq
// Imports: Init.Grind.AC Init.Data.Ord Init.Data.Nat.Linear
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Ord::{initialize_Init_Data_Ord, runtime_initialize_Init_Data_Ord};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Grind::AC::{
    initialize_Init_Grind_AC, l_Lean_Grind_AC_Seq_concat, l_Lean_Grind_AC_instBEqSeq_beq,
    l_Lean_Grind_AC_instReprSeq_repr, runtime_initialize_Init_Grind_AC,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope,
    l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
};
pub static l_Lean_Grind_AC_instOrdSeq__lean___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_AC_Seq_compare___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_AC_instOrdSeq__lean___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instOrdSeq__lean___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_AC_instOrdSeq__lean: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instOrdSeq__lean___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_AC_instAppendSeq__lean___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Grind_AC_Seq_concat as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_AC_instAppendSeq__lean___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instAppendSeq__lean___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_AC_instAppendSeq__lean: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instAppendSeq__lean___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__0_value: crate::leanh::LeanStringObject<78> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 78, m_capacity: 78, m_length: 77, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 83, 101, 113, 46, 48, 46, 76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 83, 116, 97, 114, 116, 115, 87, 105, 116, 104, 82, 101, 115, 117, 108, 116, 46, 101, 120, 97, 99, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__2_value: crate::leanh::LeanStringObject<78> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 78, m_capacity: 78, m_length: 77, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 83, 101, 113, 46, 48, 46, 76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 83, 116, 97, 114, 116, 115, 87, 105, 116, 104, 82, 101, 115, 117, 108, 116, 46, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__6_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 83, 101, 113, 46, 48, 46, 76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 83, 116, 97, 114, 116, 115, 87, 105, 116, 104, 82, 101, 115, 117, 108, 116, 46, 112, 114, 101, 102, 105, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__7_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__7_value) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_AC_instInhabitedStartsWithResult_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instInhabitedStartsWithResult: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__0_value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__2_value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__4_value) as *mut crate::leanh::LeanObject,13556645696814629918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__6_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__6_value) as *mut crate::leanh::LeanObject,18261494228143523011 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__8_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__8_value) as *mut crate::leanh::LeanObject,622053547050603573 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__10_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [65, 67, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__10_value) as *mut crate::leanh::LeanObject,9833679720422092130 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__12_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__12_value) as *mut crate::leanh::LeanObject,3013807095244504109 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__13_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,2695520371319659544 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__14_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__2_value) as *mut crate::leanh::LeanObject,5422116779171899537 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__15_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__8_value) as *mut crate::leanh::LeanObject,13375516371487207919 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__16_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__10_value) as *mut crate::leanh::LeanObject,5567153184062126208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__18_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 101, 114, 109, 95, 58, 58, 95, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__17_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__18_value) as *mut crate::leanh::LeanObject,8142158254776131947 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__20_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 110, 100, 116, 104, 101, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__21_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__20_value) as *mut crate::leanh::LeanObject,12571085391447129896 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__22_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 58, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__23_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__22_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__23_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__24_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 114, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__24_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__25_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__24_value) as *mut crate::leanh::LeanObject,8609355255726335675 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__25_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__26_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 7 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__25_value) as *mut crate::leanh::LeanObject,((( 65 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__26_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__27_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__21_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__23_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__26_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__27_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__28_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__19_value) as *mut crate::leanh::LeanObject,((( 65 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 66 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__27_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__28_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a__: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__28_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__2_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__4_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 101, 113, 46, 99, 111, 110, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__12_value) as *mut crate::leanh::LeanObject,9937852046400114528 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__6_value) as *mut crate::leanh::LeanObject,17833304286857443963 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__8_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__10_value) as *mut crate::leanh::LeanObject,7037901503065350583 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__12_value) as *mut crate::leanh::LeanObject,15233984863453104988 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__6_value) as *mut crate::leanh::LeanObject,7948251239744257903 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__11_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__13_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_a:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_AC_Seq_length(
    mut v_x_978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_978_) == 0 {
        let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_979_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_979_;
    } else {
        let mut v_s_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_s_980_ = crate::leanh::lean_ctor_get(v_x_978_, 1);
        v___x_981_ = l_Lean_Grind_AC_Seq_length(v_s_980_);
        v___x_982_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_983_ = lean_nat_add(v___x_981_, v___x_982_);
        crate::leanh::lean_dec(v___x_981_);
        return v___x_983_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_length___boxed(
    mut v_x_984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_985_ = l_Lean_Grind_AC_Seq_length(v_x_984_);
    crate::leanh::lean_dec_ref(v_x_984_);
    return v_res_985_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_isVar(mut v_x_986_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_986_) == 0 {
        let mut v___x_987_: u8 = 0;
        v___x_987_ = 1;
        return v___x_987_;
    } else {
        let mut v___x_988_: u8 = 0;
        v___x_988_ = 0;
        return v___x_988_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_isVar___boxed(
    mut v_x_989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_990_: u8 = 0;
    let mut v_r_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_990_ = l_Lean_Grind_AC_Seq_isVar(v_x_989_);
    crate::leanh::lean_dec_ref(v_x_989_);
    v_r_991_ = crate::leanh::lean_box((v_res_990_) as usize);
    return v_r_991_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_reverse_go(
    mut v_a_992_: *mut crate::leanh::LeanObject,
    mut v_a_993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1000_: u8 = 0;
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_992_) == 0 {
                    v_x_994_ = crate::leanh::lean_ctor_get(v_a_992_, 0);
                    crate::leanh::lean_inc(v_x_994_);
                    crate::leanh::lean_dec_ref_known(v_a_992_, 1);
                    v___x_995_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_995_, 0, v_x_994_);
                    crate::leanh::lean_ctor_set(v___x_995_, 1, v_a_993_);
                    return v___x_995_;
                } else {
                    v_x_996_ = crate::leanh::lean_ctor_get(v_a_992_, 0);
                    v_s_997_ = crate::leanh::lean_ctor_get(v_a_992_, 1);
                    v_isSharedCheck_1005_ = (!crate::leanh::lean_is_exclusive(v_a_992_)) as u8;
                    if v_isSharedCheck_1005_ == 0 {
                        v___x_999_ = v_a_992_;
                        v_isShared_1000_ = v_isSharedCheck_1005_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_s_997_);
                        crate::leanh::lean_inc(v_x_996_);
                        crate::leanh::lean_dec(v_a_992_);
                        v___x_999_ = crate::leanh::lean_box(0);
                        v_isShared_1000_ = v_isSharedCheck_1005_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1000_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_999_, 1, v_a_993_);
                    v___x_1002_ = v___x_999_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1004_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_x_996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_a_993_);
                    v___x_1002_ = v_reuseFailAlloc_1004_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_992_ = v_s_997_;
                v_a_993_ = v___x_1002_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_reverse(
    mut v_s_1006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_s_1006_) == 0 {
        return v_s_1006_;
    } else {
        let mut v_x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_s_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_x_1007_ = crate::leanh::lean_ctor_get(v_s_1006_, 0);
        crate::leanh::lean_inc(v_x_1007_);
        v_s_1008_ = crate::leanh::lean_ctor_get(v_s_1006_, 1);
        crate::leanh::lean_inc_ref(v_s_1008_);
        crate::leanh::lean_dec_ref_known(v_s_1006_, 2);
        v___x_1009_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1009_, 0, v_x_1007_);
        v___x_1010_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_reverse_go(
            v_s_1008_,
            v___x_1009_,
        );
        return v___x_1010_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_compare_lex(
    mut v_s_u2081_1011_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1012_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: u8 = 0;
    let mut v___x_1016_: u8 = 0;
    let mut v___x_1017_: u8 = 0;
    let mut v___x_1018_: u8 = 0;
    let mut v___x_1019_: u8 = 0;
    let mut v___x_1020_: u8 = 0;
    let mut v___x_1021_: u8 = 0;
    let mut v_x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: u8 = 0;
    let mut v___x_1027_: u8 = 0;
    let mut v___x_1028_: u8 = 0;
    let mut v___x_1030_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_s_u2081_1011_) == 0 {
                    if crate::leanh::lean_obj_tag(v_s_u2082_1012_) == 0 {
                        v_x_1013_ = crate::leanh::lean_ctor_get(v_s_u2081_1011_, 0);
                        v_x_1014_ = crate::leanh::lean_ctor_get(v_s_u2082_1012_, 0);
                        v___x_1015_ = lean_nat_dec_lt(v_x_1013_, v_x_1014_);
                        if v___x_1015_ == 0 {
                            v___x_1016_ = lean_nat_dec_eq(v_x_1013_, v_x_1014_);
                            if v___x_1016_ == 0 {
                                v___x_1017_ = 2;
                                return v___x_1017_;
                            } else {
                                v___x_1018_ = 1;
                                return v___x_1018_;
                            }
                        } else {
                            v___x_1019_ = 0;
                            return v___x_1019_;
                        }
                    } else {
                        v___x_1020_ = 0;
                        return v___x_1020_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_s_u2082_1012_) == 0 {
                        v___x_1021_ = 2;
                        return v___x_1021_;
                    } else {
                        v_x_1022_ = crate::leanh::lean_ctor_get(v_s_u2081_1011_, 0);
                        v_s_1023_ = crate::leanh::lean_ctor_get(v_s_u2081_1011_, 1);
                        v_x_1024_ = crate::leanh::lean_ctor_get(v_s_u2082_1012_, 0);
                        v_s_1025_ = crate::leanh::lean_ctor_get(v_s_u2082_1012_, 1);
                        v___x_1026_ = lean_nat_dec_lt(v_x_1022_, v_x_1024_);
                        if v___x_1026_ == 0 {
                            v___x_1027_ = lean_nat_dec_eq(v_x_1022_, v_x_1024_);
                            if v___x_1027_ == 0 {
                                v___x_1028_ = 2;
                                return v___x_1028_;
                            } else {
                                v_s_u2081_1011_ = v_s_1023_;
                                v_s_u2082_1012_ = v_s_1025_;
                                state = 0;
                                continue;
                            }
                        } else {
                            v___x_1030_ = 0;
                            return v___x_1030_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_compare_lex___boxed(
    mut v_s_u2081_1031_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1033_: u8 = 0;
    let mut v_r_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1033_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_compare_lex(
        v_s_u2081_1031_,
        v_s_u2082_1032_,
    );
    crate::leanh::lean_dec_ref(v_s_u2082_1032_);
    crate::leanh::lean_dec_ref(v_s_u2081_1031_);
    v_r_1034_ = crate::leanh::lean_box((v_res_1033_) as usize);
    return v_r_1034_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_compare(
    mut v_s_u2081_1035_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1036_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_len_u2081_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_len_u2082_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: u8 = 0;
    v_len_u2081_1037_ = l_Lean_Grind_AC_Seq_length(v_s_u2081_1035_);
    v_len_u2082_1038_ = l_Lean_Grind_AC_Seq_length(v_s_u2082_1036_);
    v___x_1039_ = lean_nat_dec_lt(v_len_u2081_1037_, v_len_u2082_1038_);
    if v___x_1039_ == 0 {
        let mut v___x_1040_: u8 = 0;
        v___x_1040_ = lean_nat_dec_lt(v_len_u2082_1038_, v_len_u2081_1037_);
        crate::leanh::lean_dec(v_len_u2081_1037_);
        crate::leanh::lean_dec(v_len_u2082_1038_);
        if v___x_1040_ == 0 {
            let mut v___x_1041_: u8 = 0;
            v___x_1041_ =
                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_compare_lex(
                    v_s_u2081_1035_,
                    v_s_u2082_1036_,
                );
            return v___x_1041_;
        } else {
            let mut v___x_1042_: u8 = 0;
            v___x_1042_ = 2;
            return v___x_1042_;
        }
    } else {
        let mut v___x_1043_: u8 = 0;
        crate::leanh::lean_dec(v_len_u2082_1038_);
        crate::leanh::lean_dec(v_len_u2081_1037_);
        v___x_1043_ = 0;
        return v___x_1043_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_compare___boxed(
    mut v_s_u2081_1044_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1046_: u8 = 0;
    let mut v_r_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1046_ = l_Lean_Grind_AC_Seq_compare(v_s_u2081_1044_, v_s_u2082_1045_);
    crate::leanh::lean_dec_ref(v_s_u2082_1045_);
    crate::leanh::lean_dec_ref(v_s_u2081_1044_);
    v_r_1047_ = crate::leanh::lean_box((v_res_1046_) as usize);
    return v_r_1047_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorIdx(
    mut v_x_1052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1052_) {
        0 => {
            let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1053_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1053_;
        }
        1 => {
            let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1054_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1054_;
        }
        _ => {
            let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1055_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1055_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorIdx___boxed(
    mut v_x_1056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1057_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorIdx(
            v_x_1056_,
        );
    crate::leanh::lean_dec(v_x_1056_);
    return v_res_1057_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(
    mut v_t_1058_: *mut crate::leanh::LeanObject,
    mut v_k_1059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1058_) == 2 {
        let mut v_s_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_s_1060_ = crate::leanh::lean_ctor_get(v_t_1058_, 0);
        crate::leanh::lean_inc_ref(v_s_1060_);
        crate::leanh::lean_dec_ref_known(v_t_1058_, 1);
        v___x_1061_ = crate::leanh::lean_apply_1(v_k_1059_, v_s_1060_);
        return v___x_1061_;
    } else {
        crate::leanh::lean_dec(v_t_1058_);
        return v_k_1059_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim(
    mut v_motive_1062_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1063_: *mut crate::leanh::LeanObject,
    mut v_t_1064_: *mut crate::leanh::LeanObject,
    mut v_h_1065_: *mut crate::leanh::LeanObject,
    mut v_k_1066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1067_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_1064_, v_k_1066_);
    return v___x_1067_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___boxed(
    mut v_motive_1068_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1069_: *mut crate::leanh::LeanObject,
    mut v_t_1070_: *mut crate::leanh::LeanObject,
    mut v_h_1071_: *mut crate::leanh::LeanObject,
    mut v_k_1072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1073_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim(
            v_motive_1068_,
            v_ctorIdx_1069_,
            v_t_1070_,
            v_h_1071_,
            v_k_1072_,
        );
    crate::leanh::lean_dec(v_ctorIdx_1069_);
    return v_res_1073_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_false_elim___redArg(
    mut v_t_1074_: *mut crate::leanh::LeanObject,
    mut v_false_1075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1076_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_1074_, v_false_1075_);
    return v___x_1076_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_false_elim(
    mut v_motive_1077_: *mut crate::leanh::LeanObject,
    mut v_t_1078_: *mut crate::leanh::LeanObject,
    mut v_h_1079_: *mut crate::leanh::LeanObject,
    mut v_false_1080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1081_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_1078_, v_false_1080_);
    return v___x_1081_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_exact_elim___redArg(
    mut v_t_1082_: *mut crate::leanh::LeanObject,
    mut v_exact_1083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1084_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_1082_, v_exact_1083_);
    return v___x_1084_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_exact_elim(
    mut v_motive_1085_: *mut crate::leanh::LeanObject,
    mut v_t_1086_: *mut crate::leanh::LeanObject,
    mut v_h_1087_: *mut crate::leanh::LeanObject,
    mut v_exact_1088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1089_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_1086_, v_exact_1088_);
    return v___x_1089_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_prefix_elim___redArg(
    mut v_t_1090_: *mut crate::leanh::LeanObject,
    mut v_prefix_1091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1092_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_1090_, v_prefix_1091_);
    return v___x_1092_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_prefix_elim(
    mut v_motive_1093_: *mut crate::leanh::LeanObject,
    mut v_t_1094_: *mut crate::leanh::LeanObject,
    mut v_h_1095_: *mut crate::leanh::LeanObject,
    mut v_prefix_1096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1097_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_1094_, v_prefix_1096_);
    return v___x_1097_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1104_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1105_ = lean_nat_to_int(v___x_1104_);
    return v___x_1105_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1106_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1107_ = lean_nat_to_int(v___x_1106_);
    return v___x_1107_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr(
    mut v_x_1114_: *mut crate::leanh::LeanObject,
    mut v_prec_1115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: u8 = 0;
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: u8 = 0;
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: u8 = 0;
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: u8 = 0;
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: u8 = 0;
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: u8 = 0;
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1114_) {
                0 => {
                    v___x_1130_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1131_ = lean_nat_dec_le(v___x_1130_, v_prec_1115_);
                    if v___x_1131_ == 0 {
                        v___x_1132_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4);
                        v___y_1124_ = v___x_1132_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1133_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5);
                        v___y_1124_ = v___x_1133_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v___x_1134_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1135_ = lean_nat_dec_le(v___x_1134_, v_prec_1115_);
                    if v___x_1135_ == 0 {
                        v___x_1136_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4);
                        v___y_1117_ = v___x_1136_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1137_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5);
                        v___y_1117_ = v___x_1137_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_s_1138_ = crate::leanh::lean_ctor_get(v_x_1114_, 0);
                    crate::leanh::lean_inc_ref(v_s_1138_);
                    crate::leanh::lean_dec_ref_known(v_x_1114_, 1);
                    v___x_1149_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1150_ = lean_nat_dec_le(v___x_1149_, v_prec_1115_);
                    if v___x_1150_ == 0 {
                        v___x_1151_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4);
                        v___y_1140_ = v___x_1151_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1152_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5);
                        v___y_1140_ = v___x_1152_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1118_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__1;
                crate::leanh::lean_inc(v___y_1117_);
                v___x_1119_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1119_, 0, v___y_1117_);
                crate::leanh::lean_ctor_set(v___x_1119_, 1, v___x_1118_);
                v___x_1120_ = 0;
                v___x_1121_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1121_, 0, v___x_1119_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1121_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1120_,
                );
                v___x_1122_ = l_Repr_addAppParen(v___x_1121_, v_prec_1115_);
                return v___x_1122_;
            }
            2 => {
                v___x_1125_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__3;
                crate::leanh::lean_inc(v___y_1124_);
                v___x_1126_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1126_, 0, v___y_1124_);
                crate::leanh::lean_ctor_set(v___x_1126_, 1, v___x_1125_);
                v___x_1127_ = 0;
                v___x_1128_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1128_, 0, v___x_1126_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1127_,
                );
                v___x_1129_ = l_Repr_addAppParen(v___x_1128_, v_prec_1115_);
                return v___x_1129_;
            }
            3 => {
                v___x_1141_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__8;
                v___x_1142_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1143_ = l_Lean_Grind_AC_instReprSeq_repr(v_s_1138_, v___x_1142_);
                v___x_1144_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1144_, 0, v___x_1141_);
                crate::leanh::lean_ctor_set(v___x_1144_, 1, v___x_1143_);
                crate::leanh::lean_inc(v___y_1140_);
                v___x_1145_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1145_, 0, v___y_1140_);
                crate::leanh::lean_ctor_set(v___x_1145_, 1, v___x_1144_);
                v___x_1146_ = 0;
                v___x_1147_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1147_, 0, v___x_1145_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1147_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1146_,
                );
                v___x_1148_ = l_Repr_addAppParen(v___x_1147_, v_prec_1115_);
                return v___x_1148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___boxed(
    mut v_x_1153_: *mut crate::leanh::LeanObject,
    mut v_prec_1154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1155_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr(
            v_x_1153_,
            v_prec_1154_,
        );
    crate::leanh::lean_dec(v_prec_1154_);
    return v_res_1155_;
}
pub unsafe fn _init_l_Lean_Grind_AC_instInhabitedStartsWithResult_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1158_ = crate::leanh::lean_box(0);
    return v___x_1158_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instInhabitedStartsWithResult()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1159_ = crate::leanh::lean_box(0);
    return v___x_1159_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(
    mut v_s_u2081_1160_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: u8 = 0;
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1170_: u8 = 0;
    let mut v_x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: u8 = 0;
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1178_: u8 = 0;
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: u8 = 0;
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_s_u2082_1161_) == 0 {
                    if crate::leanh::lean_obj_tag(v_s_u2081_1160_) == 0 {
                        v_x_1162_ = crate::leanh::lean_ctor_get(v_s_u2082_1161_, 0);
                        crate::leanh::lean_inc(v_x_1162_);
                        crate::leanh::lean_dec_ref_known(v_s_u2082_1161_, 1);
                        v_x_1163_ = crate::leanh::lean_ctor_get(v_s_u2081_1160_, 0);
                        v___x_1164_ = lean_nat_dec_eq(v_x_1162_, v_x_1163_);
                        crate::leanh::lean_dec(v_x_1162_);
                        if v___x_1164_ == 0 {
                            v___x_1165_ = crate::leanh::lean_box(0);
                            return v___x_1165_;
                        } else {
                            v___x_1166_ = crate::leanh::lean_box(1);
                            return v___x_1166_;
                        }
                    } else {
                        v_x_1167_ = crate::leanh::lean_ctor_get(v_s_u2082_1161_, 0);
                        v_isSharedCheck_1178_ =
                            (!crate::leanh::lean_is_exclusive(v_s_u2082_1161_)) as u8;
                        if v_isSharedCheck_1178_ == 0 {
                            v___x_1169_ = v_s_u2082_1161_;
                            v_isShared_1170_ = v_isSharedCheck_1178_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_x_1167_);
                            crate::leanh::lean_dec(v_s_u2082_1161_);
                            v___x_1169_ = crate::leanh::lean_box(0);
                            v_isShared_1170_ = v_isSharedCheck_1178_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_s_u2081_1160_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_s_u2082_1161_, 2);
                        v___x_1179_ = crate::leanh::lean_box(0);
                        return v___x_1179_;
                    } else {
                        v_x_1180_ = crate::leanh::lean_ctor_get(v_s_u2082_1161_, 0);
                        crate::leanh::lean_inc(v_x_1180_);
                        v_s_1181_ = crate::leanh::lean_ctor_get(v_s_u2082_1161_, 1);
                        crate::leanh::lean_inc_ref(v_s_1181_);
                        crate::leanh::lean_dec_ref_known(v_s_u2082_1161_, 2);
                        v_x_1182_ = crate::leanh::lean_ctor_get(v_s_u2081_1160_, 0);
                        v_s_1183_ = crate::leanh::lean_ctor_get(v_s_u2081_1160_, 1);
                        v___x_1184_ = lean_nat_dec_eq(v_x_1180_, v_x_1182_);
                        crate::leanh::lean_dec(v_x_1180_);
                        if v___x_1184_ == 0 {
                            crate::leanh::lean_dec_ref(v_s_1181_);
                            v___x_1185_ = crate::leanh::lean_box(0);
                            return v___x_1185_;
                        } else {
                            v_s_u2081_1160_ = v_s_1183_;
                            v_s_u2082_1161_ = v_s_1181_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_x_1171_ = crate::leanh::lean_ctor_get(v_s_u2081_1160_, 0);
                v_s_1172_ = crate::leanh::lean_ctor_get(v_s_u2081_1160_, 1);
                v___x_1173_ = lean_nat_dec_eq(v_x_1167_, v_x_1171_);
                crate::leanh::lean_dec(v_x_1167_);
                if v___x_1173_ == 0 {
                    crate::leanh::lean_del_object(v___x_1169_);
                    v___x_1174_ = crate::leanh::lean_box(0);
                    return v___x_1174_;
                } else {
                    crate::leanh::lean_inc_ref(v_s_1172_);
                    if v_isShared_1170_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1169_, 2);
                        crate::leanh::lean_ctor_set(v___x_1169_, 0, v_s_1172_);
                        v___x_1176_ = v___x_1169_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1177_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_s_1172_);
                        v___x_1176_ = v_reuseFailAlloc_1177_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1176_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith___boxed(
    mut v_s_u2081_1187_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1189_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(
        v_s_u2081_1187_,
        v_s_u2082_1188_,
    );
    crate::leanh::lean_dec_ref(v_s_u2081_1187_);
    return v_res_1189_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1265_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__4;
    v___x_1266_ = l_String_toRawSubstring_x27(v___x_1265_);
    return v___x_1266_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1(
    mut v_x_1291_: *mut crate::leanh::LeanObject,
    mut v_a_1292_: *mut crate::leanh::LeanObject,
    mut v_a_1293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: u8 = 0;
    v___x_1294_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1295_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__19;
    crate::leanh::lean_inc(v_x_1291_);
    v___x_1296_ = l_Lean_Syntax_isOfKind(v_x_1291_, v___x_1295_);
    if v___x_1296_ == 0 {
        let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1291_);
        v___x_1297_ = crate::leanh::lean_box(1);
        v___x_1298_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1298_, 0, v___x_1297_);
        crate::leanh::lean_ctor_set(v___x_1298_, 1, v_a_1293_);
        return v___x_1298_;
    } else {
        let mut v_quotContext_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1305_: u8 = 0;
        let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1299_ = crate::leanh::lean_ctor_get(v_a_1292_, 1);
        v_currMacroScope_1300_ = crate::leanh::lean_ctor_get(v_a_1292_, 2);
        v_ref_1301_ = crate::leanh::lean_ctor_get(v_a_1292_, 5);
        v___x_1302_ = l_Lean_Syntax_getArg(v_x_1291_, v___x_1294_);
        v___x_1303_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_1304_ = l_Lean_Syntax_getArg(v_x_1291_, v___x_1303_);
        crate::leanh::lean_dec(v_x_1291_);
        v___x_1305_ = 0;
        v___x_1306_ = l_Lean_SourceInfo_fromRef(v_ref_1301_, v___x_1305_);
        v___x_1307_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3;
        v___x_1308_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5);
        v___x_1309_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__7;
        crate::leanh::lean_inc(v_currMacroScope_1300_);
        crate::leanh::lean_inc(v_quotContext_1299_);
        v___x_1310_ =
            l_Lean_addMacroScope(v_quotContext_1299_, v___x_1309_, v_currMacroScope_1300_);
        v___x_1311_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__12;
        crate::leanh::lean_inc_n(v___x_1306_, 2);
        v___x_1312_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1312_, 0, v___x_1306_);
        crate::leanh::lean_ctor_set(v___x_1312_, 1, v___x_1308_);
        crate::leanh::lean_ctor_set(v___x_1312_, 2, v___x_1310_);
        crate::leanh::lean_ctor_set(v___x_1312_, 3, v___x_1311_);
        v___x_1313_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__14;
        v___x_1314_ = l_Lean_Syntax_node2(v___x_1306_, v___x_1313_, v___x_1302_, v___x_1304_);
        v___x_1315_ = l_Lean_Syntax_node2(v___x_1306_, v___x_1307_, v___x_1312_, v___x_1314_);
        v___x_1316_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1316_, 0, v___x_1315_);
        crate::leanh::lean_ctor_set(v___x_1316_, 1, v_a_1293_);
        return v___x_1316_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___boxed(
    mut v_x_1317_: *mut crate::leanh::LeanObject,
    mut v_a_1318_: *mut crate::leanh::LeanObject,
    mut v_a_1319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1320_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1(v_x_1317_, v_a_1318_, v_a_1319_);
    crate::leanh::lean_dec_ref(v_a_1318_);
    return v_res_1320_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1(
    mut v_x_1324_: *mut crate::leanh::LeanObject,
    mut v_a_1325_: *mut crate::leanh::LeanObject,
    mut v_a_1326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: u8 = 0;
    v___x_1327_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3;
    crate::leanh::lean_inc(v_x_1324_);
    v___x_1328_ = l_Lean_Syntax_isOfKind(v_x_1324_, v___x_1327_);
    if v___x_1328_ == 0 {
        let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1324_);
        v___x_1329_ = crate::leanh::lean_box(0);
        v___x_1330_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1330_, 0, v___x_1329_);
        crate::leanh::lean_ctor_set(v___x_1330_, 1, v_a_1326_);
        return v___x_1330_;
    } else {
        let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1334_: u8 = 0;
        v___x_1331_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1332_ = l_Lean_Syntax_getArg(v_x_1324_, v___x_1331_);
        v___x_1333_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__1;
        crate::leanh::lean_inc(v___x_1332_);
        v___x_1334_ = l_Lean_Syntax_isOfKind(v___x_1332_, v___x_1333_);
        if v___x_1334_ == 0 {
            let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1332_);
            crate::leanh::lean_dec(v_x_1324_);
            v___x_1335_ = crate::leanh::lean_box(0);
            v___x_1336_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1336_, 0, v___x_1335_);
            crate::leanh::lean_ctor_set(v___x_1336_, 1, v_a_1326_);
            return v___x_1336_;
        } else {
            let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1340_: u8 = 0;
            v___x_1337_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1338_ = l_Lean_Syntax_getArg(v_x_1324_, v___x_1337_);
            crate::leanh::lean_dec(v_x_1324_);
            v___x_1339_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_1338_);
            v___x_1340_ = l_Lean_Syntax_matchesNull(v___x_1338_, v___x_1339_);
            if v___x_1340_ == 0 {
                let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_1338_);
                crate::leanh::lean_dec(v___x_1332_);
                v___x_1341_ = crate::leanh::lean_box(0);
                v___x_1342_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1342_, 0, v___x_1341_);
                crate::leanh::lean_ctor_set(v___x_1342_, 1, v_a_1326_);
                return v___x_1342_;
            } else {
                let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1346_: u8 = 0;
                let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1343_ = l_Lean_Syntax_getArg(v___x_1338_, v___x_1331_);
                v___x_1344_ = l_Lean_Syntax_getArg(v___x_1338_, v___x_1337_);
                crate::leanh::lean_dec(v___x_1338_);
                v_ref_1345_ = l_Lean_replaceRef(v___x_1332_, v_a_1325_);
                crate::leanh::lean_dec(v___x_1332_);
                v___x_1346_ = 0;
                v___x_1347_ = l_Lean_SourceInfo_fromRef(v_ref_1345_, v___x_1346_);
                crate::leanh::lean_dec(v_ref_1345_);
                v___x_1348_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__19;
                v___x_1349_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__22;
                crate::leanh::lean_inc(v___x_1347_);
                v___x_1350_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1350_, 0, v___x_1347_);
                crate::leanh::lean_ctor_set(v___x_1350_, 1, v___x_1349_);
                v___x_1351_ = l_Lean_Syntax_node3(
                    v___x_1347_,
                    v___x_1348_,
                    v___x_1343_,
                    v___x_1350_,
                    v___x_1344_,
                );
                v___x_1352_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1352_, 0, v___x_1351_);
                crate::leanh::lean_ctor_set(v___x_1352_, 1, v_a_1326_);
                return v___x_1352_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___boxed(
    mut v_x_1353_: *mut crate::leanh::LeanObject,
    mut v_a_1354_: *mut crate::leanh::LeanObject,
    mut v_a_1355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1356_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1(v_x_1353_, v_a_1354_, v_a_1355_);
    crate::leanh::lean_dec(v_a_1354_);
    return v_res_1356_;
}
pub unsafe fn l_Lean_Grind_AC_instOfNatSeq__lean(
    mut v_n_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1358_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1358_, 0, v_n_1357_);
    return v___x_1358_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_a()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1359_ = crate::leanh::lean_unsigned_to_nat(1);
    return v___x_1359_;
}
pub unsafe fn l_Lean_Grind_AC_SubseqResult_ctorIdx(
    mut v_x_1360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1360_) {
        0 => {
            let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1361_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1361_;
        }
        1 => {
            let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1362_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1362_;
        }
        2 => {
            let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1363_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1363_;
        }
        3 => {
            let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1364_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_1364_;
        }
        _ => {
            let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1365_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_1365_;
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_SubseqResult_ctorIdx___boxed(
    mut v_x_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1367_ = l_Lean_Grind_AC_SubseqResult_ctorIdx(v_x_1366_);
    crate::leanh::lean_dec(v_x_1366_);
    return v_res_1367_;
}
pub unsafe fn l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(
    mut v_t_1368_: *mut crate::leanh::LeanObject,
    mut v_k_1369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_1368_) {
        2 => {
            let mut v_s_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_s_1370_ = crate::leanh::lean_ctor_get(v_t_1368_, 0);
            crate::leanh::lean_inc_ref(v_s_1370_);
            crate::leanh::lean_dec_ref_known(v_t_1368_, 1);
            v___x_1371_ = crate::leanh::lean_apply_1(v_k_1369_, v_s_1370_);
            return v___x_1371_;
        }
        3 => {
            let mut v_s_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_s_1372_ = crate::leanh::lean_ctor_get(v_t_1368_, 0);
            crate::leanh::lean_inc_ref(v_s_1372_);
            crate::leanh::lean_dec_ref_known(v_t_1368_, 1);
            v___x_1373_ = crate::leanh::lean_apply_1(v_k_1369_, v_s_1372_);
            return v___x_1373_;
        }
        4 => {
            let mut v_p_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_p_1374_ = crate::leanh::lean_ctor_get(v_t_1368_, 0);
            crate::leanh::lean_inc_ref(v_p_1374_);
            v_s_1375_ = crate::leanh::lean_ctor_get(v_t_1368_, 1);
            crate::leanh::lean_inc_ref(v_s_1375_);
            crate::leanh::lean_dec_ref_known(v_t_1368_, 2);
            v___x_1376_ = crate::leanh::lean_apply_2(v_k_1369_, v_p_1374_, v_s_1375_);
            return v___x_1376_;
        }
        _ => {
            crate::leanh::lean_dec(v_t_1368_);
            return v_k_1369_;
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_SubseqResult_ctorElim(
    mut v_motive_1377_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1378_: *mut crate::leanh::LeanObject,
    mut v_t_1379_: *mut crate::leanh::LeanObject,
    mut v_h_1380_: *mut crate::leanh::LeanObject,
    mut v_k_1381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1382_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_1379_, v_k_1381_);
    return v___x_1382_;
}
pub unsafe fn l_Lean_Grind_AC_SubseqResult_ctorElim___boxed(
    mut v_motive_1383_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1384_: *mut crate::leanh::LeanObject,
    mut v_t_1385_: *mut crate::leanh::LeanObject,
    mut v_h_1386_: *mut crate::leanh::LeanObject,
    mut v_k_1387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1388_ = l_Lean_Grind_AC_SubseqResult_ctorElim(
        v_motive_1383_,
        v_ctorIdx_1384_,
        v_t_1385_,
        v_h_1386_,
        v_k_1387_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1384_);
    return v_res_1388_;
}
pub unsafe fn l_Lean_Grind_AC_SubseqResult_false_elim___redArg(
    mut v_t_1389_: *mut crate::leanh::LeanObject,
    mut v_false_1390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1391_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_1389_, v_false_1390_);
    return v___x_1391_;
}
pub unsafe fn l_Lean_Grind_AC_SubseqResult_false_elim(
    mut v_motive_1392_: *mut crate::leanh::LeanObject,
    mut v_t_1393_: *mut crate::leanh::LeanObject,
    mut v_h_1394_: *mut crate::leanh::LeanObject,
    mut v_false_1395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1396_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_1393_, v_false_1395_);
    return v___x_1396_;
}
pub unsafe fn l_Lean_Grind_AC_SubseqResult_exact_elim___redArg(
    mut v_t_1397_: *mut crate::leanh::LeanObject,
    mut v_exact_1398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1399_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_1397_, v_exact_1398_);
    return v___x_1399_;
}
pub unsafe fn l_Lean_Grind_AC_SubseqResult_exact_elim(
    mut v_motive_1400_: *mut crate::leanh::LeanObject,
    mut v_t_1401_: *mut crate::leanh::LeanObject,
    mut v_h_1402_: *mut crate::leanh::LeanObject,
    mut v_exact_1403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_1401_, v_exact_1403_);
    return v___x_1404_;
}
pub unsafe fn l_Lean_Grind_AC_SubseqResult_prefix_elim___redArg(
    mut v_t_1405_: *mut crate::leanh::LeanObject,
    mut v_prefix_1406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1407_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_1405_, v_prefix_1406_);
    return v___x_1407_;
}
pub unsafe fn l_Lean_Grind_AC_SubseqResult_prefix_elim(
    mut v_motive_1408_: *mut crate::leanh::LeanObject,
    mut v_t_1409_: *mut crate::leanh::LeanObject,
    mut v_h_1410_: *mut crate::leanh::LeanObject,
    mut v_prefix_1411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1412_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_1409_, v_prefix_1411_);
    return v___x_1412_;
}
pub unsafe fn l_Lean_Grind_AC_SubseqResult_suffix_elim___redArg(
    mut v_t_1413_: *mut crate::leanh::LeanObject,
    mut v_suffix_1414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1415_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_1413_, v_suffix_1414_);
    return v___x_1415_;
}
pub unsafe fn l_Lean_Grind_AC_SubseqResult_suffix_elim(
    mut v_motive_1416_: *mut crate::leanh::LeanObject,
    mut v_t_1417_: *mut crate::leanh::LeanObject,
    mut v_h_1418_: *mut crate::leanh::LeanObject,
    mut v_suffix_1419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1420_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_1417_, v_suffix_1419_);
    return v___x_1420_;
}
pub unsafe fn l_Lean_Grind_AC_SubseqResult_middle_elim___redArg(
    mut v_t_1421_: *mut crate::leanh::LeanObject,
    mut v_middle_1422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1423_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_1421_, v_middle_1422_);
    return v___x_1423_;
}
pub unsafe fn l_Lean_Grind_AC_SubseqResult_middle_elim(
    mut v_motive_1424_: *mut crate::leanh::LeanObject,
    mut v_t_1425_: *mut crate::leanh::LeanObject,
    mut v_h_1426_: *mut crate::leanh::LeanObject,
    mut v_middle_1427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1428_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_1425_, v_middle_1427_);
    return v___x_1428_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subseq_go(
    mut v_s_u2081_1429_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1430_: *mut crate::leanh::LeanObject,
    mut v_acc_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1432_: u8 = 0;
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1441_: u8 = 0;
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1451_: u8 = 0;
    let mut v_unused_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_s_u2082_1430_) == 0 {
                    v___x_1432_ = l_Lean_Grind_AC_instBEqSeq_beq(v_s_u2081_1429_, v_s_u2082_1430_);
                    crate::leanh::lean_dec_ref_known(v_s_u2082_1430_, 1);
                    crate::leanh::lean_dec_ref(v_s_u2081_1429_);
                    if v___x_1432_ == 0 {
                        crate::leanh::lean_dec_ref(v_acc_1431_);
                        v___x_1433_ = crate::leanh::lean_box(0);
                        return v___x_1433_;
                    } else {
                        v___x_1434_ = l_Lean_Grind_AC_Seq_reverse(v_acc_1431_);
                        v___x_1435_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1435_, 0, v___x_1434_);
                        return v___x_1435_;
                    }
                } else {
                    v_x_1436_ = crate::leanh::lean_ctor_get(v_s_u2082_1430_, 0);
                    crate::leanh::lean_inc(v_x_1436_);
                    v_s_1437_ = crate::leanh::lean_ctor_get(v_s_u2082_1430_, 1);
                    crate::leanh::lean_inc_ref(v_s_1437_);
                    crate::leanh::lean_inc_ref(v_s_u2081_1429_);
                    v___x_1438_ =
                        l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(
                            v_s_u2082_1430_,
                            v_s_u2081_1429_,
                        );
                    v_isSharedCheck_1451_ =
                        (!crate::leanh::lean_is_exclusive(v_s_u2082_1430_)) as u8;
                    if v_isSharedCheck_1451_ == 0 {
                        v_unused_1452_ = crate::leanh::lean_ctor_get(v_s_u2082_1430_, 1);
                        crate::leanh::lean_dec(v_unused_1452_);
                        v_unused_1453_ = crate::leanh::lean_ctor_get(v_s_u2082_1430_, 0);
                        crate::leanh::lean_dec(v_unused_1453_);
                        v___x_1440_ = v_s_u2082_1430_;
                        v_isShared_1441_ = v_isSharedCheck_1451_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_s_u2082_1430_);
                        v___x_1440_ = crate::leanh::lean_box(0);
                        v_isShared_1441_ = v_isSharedCheck_1451_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v___x_1438_) {
                0 => {
                    if v_isShared_1441_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1440_, 1, v_acc_1431_);
                        v___x_1443_ = v___x_1440_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1445_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_x_1436_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_acc_1431_);
                        v___x_1443_ = v_reuseFailAlloc_1445_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_1440_);
                    crate::leanh::lean_dec_ref(v_s_1437_);
                    crate::leanh::lean_dec(v_x_1436_);
                    crate::leanh::lean_dec_ref(v_s_u2081_1429_);
                    v___x_1446_ = l_Lean_Grind_AC_Seq_reverse(v_acc_1431_);
                    v___x_1447_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1447_, 0, v___x_1446_);
                    return v___x_1447_;
                }
                _ => {
                    crate::leanh::lean_del_object(v___x_1440_);
                    crate::leanh::lean_dec_ref(v_s_1437_);
                    crate::leanh::lean_dec(v_x_1436_);
                    crate::leanh::lean_dec_ref(v_s_u2081_1429_);
                    v_s_1448_ = crate::leanh::lean_ctor_get(v___x_1438_, 0);
                    crate::leanh::lean_inc_ref(v_s_1448_);
                    crate::leanh::lean_dec_ref_known(v___x_1438_, 1);
                    v___x_1449_ = l_Lean_Grind_AC_Seq_reverse(v_acc_1431_);
                    v___x_1450_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1450_, 0, v___x_1449_);
                    crate::leanh::lean_ctor_set(v___x_1450_, 1, v_s_1448_);
                    return v___x_1450_;
                }
            },
            2 => {
                v_s_u2082_1430_ = v_s_1437_;
                v_acc_1431_ = v___x_1443_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_subseq(
    mut v_s_u2081_1454_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1456_: u8 = 0;
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1468_: u8 = 0;
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1472_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_s_u2082_1455_) == 0 {
                    v___x_1456_ = l_Lean_Grind_AC_instBEqSeq_beq(v_s_u2081_1454_, v_s_u2082_1455_);
                    crate::leanh::lean_dec_ref_known(v_s_u2082_1455_, 1);
                    crate::leanh::lean_dec_ref(v_s_u2081_1454_);
                    if v___x_1456_ == 0 {
                        v___x_1457_ = crate::leanh::lean_box(0);
                        return v___x_1457_;
                    } else {
                        v___x_1458_ = crate::leanh::lean_box(1);
                        return v___x_1458_;
                    }
                } else {
                    v_x_1459_ = crate::leanh::lean_ctor_get(v_s_u2082_1455_, 0);
                    crate::leanh::lean_inc(v_x_1459_);
                    v_s_1460_ = crate::leanh::lean_ctor_get(v_s_u2082_1455_, 1);
                    crate::leanh::lean_inc_ref(v_s_1460_);
                    crate::leanh::lean_inc_ref(v_s_u2081_1454_);
                    v___x_1461_ =
                        l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(
                            v_s_u2082_1455_,
                            v_s_u2081_1454_,
                        );
                    crate::leanh::lean_dec_ref_known(v_s_u2082_1455_, 2);
                    match crate::leanh::lean_obj_tag(v___x_1461_) {
                        0 => {
                            v___x_1462_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1462_, 0, v_x_1459_);
                            v___x_1463_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subseq_go(v_s_u2081_1454_, v_s_1460_, v___x_1462_);
                            return v___x_1463_;
                        }
                        1 => {
                            crate::leanh::lean_dec_ref(v_s_1460_);
                            crate::leanh::lean_dec(v_x_1459_);
                            crate::leanh::lean_dec_ref(v_s_u2081_1454_);
                            v___x_1464_ = crate::leanh::lean_box(1);
                            return v___x_1464_;
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_s_1460_);
                            crate::leanh::lean_dec(v_x_1459_);
                            crate::leanh::lean_dec_ref(v_s_u2081_1454_);
                            v_s_1465_ = crate::leanh::lean_ctor_get(v___x_1461_, 0);
                            v_isSharedCheck_1472_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1461_)) as u8;
                            if v_isSharedCheck_1472_ == 0 {
                                v___x_1467_ = v___x_1461_;
                                v_isShared_1468_ = v_isSharedCheck_1472_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_s_1465_);
                                crate::leanh::lean_dec(v___x_1461_);
                                v___x_1467_ = crate::leanh::lean_box(0);
                                v_isShared_1468_ = v_isSharedCheck_1472_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1468_ == 0 {
                    v___x_1470_ = v___x_1467_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1471_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_s_1465_);
                    v___x_1470_ = v_reuseFailAlloc_1471_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1470_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_SubsetResult_ctorIdx(
    mut v_x_1473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1473_) {
        0 => {
            let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1474_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1474_;
        }
        1 => {
            let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1475_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1475_;
        }
        _ => {
            let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1476_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1476_;
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_SubsetResult_ctorIdx___boxed(
    mut v_x_1477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1478_ = l_Lean_Grind_AC_SubsetResult_ctorIdx(v_x_1477_);
    crate::leanh::lean_dec(v_x_1477_);
    return v_res_1478_;
}
pub unsafe fn l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(
    mut v_t_1479_: *mut crate::leanh::LeanObject,
    mut v_k_1480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1479_) == 2 {
        let mut v_s_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_s_1481_ = crate::leanh::lean_ctor_get(v_t_1479_, 0);
        crate::leanh::lean_inc_ref(v_s_1481_);
        crate::leanh::lean_dec_ref_known(v_t_1479_, 1);
        v___x_1482_ = crate::leanh::lean_apply_1(v_k_1480_, v_s_1481_);
        return v___x_1482_;
    } else {
        crate::leanh::lean_dec(v_t_1479_);
        return v_k_1480_;
    }
}
pub unsafe fn l_Lean_Grind_AC_SubsetResult_ctorElim(
    mut v_motive_1483_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1484_: *mut crate::leanh::LeanObject,
    mut v_t_1485_: *mut crate::leanh::LeanObject,
    mut v_h_1486_: *mut crate::leanh::LeanObject,
    mut v_k_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1488_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_1485_, v_k_1487_);
    return v___x_1488_;
}
pub unsafe fn l_Lean_Grind_AC_SubsetResult_ctorElim___boxed(
    mut v_motive_1489_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1490_: *mut crate::leanh::LeanObject,
    mut v_t_1491_: *mut crate::leanh::LeanObject,
    mut v_h_1492_: *mut crate::leanh::LeanObject,
    mut v_k_1493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1494_ = l_Lean_Grind_AC_SubsetResult_ctorElim(
        v_motive_1489_,
        v_ctorIdx_1490_,
        v_t_1491_,
        v_h_1492_,
        v_k_1493_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1490_);
    return v_res_1494_;
}
pub unsafe fn l_Lean_Grind_AC_SubsetResult_false_elim___redArg(
    mut v_t_1495_: *mut crate::leanh::LeanObject,
    mut v_false_1496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_1495_, v_false_1496_);
    return v___x_1497_;
}
pub unsafe fn l_Lean_Grind_AC_SubsetResult_false_elim(
    mut v_motive_1498_: *mut crate::leanh::LeanObject,
    mut v_t_1499_: *mut crate::leanh::LeanObject,
    mut v_h_1500_: *mut crate::leanh::LeanObject,
    mut v_false_1501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_1499_, v_false_1501_);
    return v___x_1502_;
}
pub unsafe fn l_Lean_Grind_AC_SubsetResult_exact_elim___redArg(
    mut v_t_1503_: *mut crate::leanh::LeanObject,
    mut v_exact_1504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1505_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_1503_, v_exact_1504_);
    return v___x_1505_;
}
pub unsafe fn l_Lean_Grind_AC_SubsetResult_exact_elim(
    mut v_motive_1506_: *mut crate::leanh::LeanObject,
    mut v_t_1507_: *mut crate::leanh::LeanObject,
    mut v_h_1508_: *mut crate::leanh::LeanObject,
    mut v_exact_1509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1510_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_1507_, v_exact_1509_);
    return v___x_1510_;
}
pub unsafe fn l_Lean_Grind_AC_SubsetResult_strict_elim___redArg(
    mut v_t_1511_: *mut crate::leanh::LeanObject,
    mut v_strict_1512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1513_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_1511_, v_strict_1512_);
    return v___x_1513_;
}
pub unsafe fn l_Lean_Grind_AC_SubsetResult_strict_elim(
    mut v_motive_1514_: *mut crate::leanh::LeanObject,
    mut v_t_1515_: *mut crate::leanh::LeanObject,
    mut v_h_1516_: *mut crate::leanh::LeanObject,
    mut v_strict_1517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1518_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_1515_, v_strict_1517_);
    return v___x_1518_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subset_go(
    mut v_s_u2081_1519_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1520_: *mut crate::leanh::LeanObject,
    mut v_acc_1521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1525_: u8 = 0;
    let mut v_x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: u8 = 0;
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1533_: u8 = 0;
    let mut v_x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1539_: u8 = 0;
    let mut v___x_1540_: u8 = 0;
    let mut v___x_1541_: u8 = 0;
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1549_: u8 = 0;
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1555_: u8 = 0;
    let mut v_unused_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1557_: u8 = 0;
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1565_: u8 = 0;
    let mut v___x_1566_: u8 = 0;
    let mut v___x_1567_: u8 = 0;
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1574_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_s_u2081_1519_) == 0 {
                    if crate::leanh::lean_obj_tag(v_s_u2082_1520_) == 0 {
                        v_x_1522_ = crate::leanh::lean_ctor_get(v_s_u2081_1519_, 0);
                        v_isSharedCheck_1533_ =
                            (!crate::leanh::lean_is_exclusive(v_s_u2081_1519_)) as u8;
                        if v_isSharedCheck_1533_ == 0 {
                            v___x_1524_ = v_s_u2081_1519_;
                            v_isShared_1525_ = v_isSharedCheck_1533_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_x_1522_);
                            crate::leanh::lean_dec(v_s_u2081_1519_);
                            v___x_1524_ = crate::leanh::lean_box(0);
                            v_isShared_1525_ = v_isSharedCheck_1533_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_x_1534_ = crate::leanh::lean_ctor_get(v_s_u2081_1519_, 0);
                        v_x_1535_ = crate::leanh::lean_ctor_get(v_s_u2082_1520_, 0);
                        v_s_1536_ = crate::leanh::lean_ctor_get(v_s_u2082_1520_, 1);
                        v_isSharedCheck_1557_ =
                            (!crate::leanh::lean_is_exclusive(v_s_u2082_1520_)) as u8;
                        if v_isSharedCheck_1557_ == 0 {
                            v___x_1538_ = v_s_u2082_1520_;
                            v_isShared_1539_ = v_isSharedCheck_1557_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_s_1536_);
                            crate::leanh::lean_inc(v_x_1535_);
                            crate::leanh::lean_dec(v_s_u2082_1520_);
                            v___x_1538_ = crate::leanh::lean_box(0);
                            v_isShared_1539_ = v_isSharedCheck_1557_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_s_u2082_1520_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_s_u2082_1520_, 1);
                        crate::leanh::lean_dec_ref_known(v_s_u2081_1519_, 2);
                        crate::leanh::lean_dec_ref(v_acc_1521_);
                        v___x_1558_ = crate::leanh::lean_box(0);
                        return v___x_1558_;
                    } else {
                        v_x_1559_ = crate::leanh::lean_ctor_get(v_s_u2081_1519_, 0);
                        v_s_1560_ = crate::leanh::lean_ctor_get(v_s_u2081_1519_, 1);
                        v_x_1561_ = crate::leanh::lean_ctor_get(v_s_u2082_1520_, 0);
                        v_s_1562_ = crate::leanh::lean_ctor_get(v_s_u2082_1520_, 1);
                        v_isSharedCheck_1574_ =
                            (!crate::leanh::lean_is_exclusive(v_s_u2082_1520_)) as u8;
                        if v_isSharedCheck_1574_ == 0 {
                            v___x_1564_ = v_s_u2082_1520_;
                            v_isShared_1565_ = v_isSharedCheck_1574_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_s_1562_);
                            crate::leanh::lean_inc(v_x_1561_);
                            crate::leanh::lean_dec(v_s_u2082_1520_);
                            v___x_1564_ = crate::leanh::lean_box(0);
                            v_isShared_1565_ = v_isSharedCheck_1574_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_x_1526_ = crate::leanh::lean_ctor_get(v_s_u2082_1520_, 0);
                crate::leanh::lean_inc(v_x_1526_);
                crate::leanh::lean_dec_ref_known(v_s_u2082_1520_, 1);
                v___x_1527_ = lean_nat_dec_eq(v_x_1522_, v_x_1526_);
                crate::leanh::lean_dec(v_x_1526_);
                crate::leanh::lean_dec(v_x_1522_);
                if v___x_1527_ == 0 {
                    crate::leanh::lean_del_object(v___x_1524_);
                    crate::leanh::lean_dec_ref(v_acc_1521_);
                    v___x_1528_ = crate::leanh::lean_box(0);
                    return v___x_1528_;
                } else {
                    v___x_1529_ = l_Lean_Grind_AC_Seq_reverse(v_acc_1521_);
                    if v_isShared_1525_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1524_, 2);
                        crate::leanh::lean_ctor_set(v___x_1524_, 0, v___x_1529_);
                        v___x_1531_ = v___x_1524_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1532_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
                        v___x_1531_ = v_reuseFailAlloc_1532_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1531_;
            }
            3 => {
                v___x_1540_ = lean_nat_dec_eq(v_x_1534_, v_x_1535_);
                if v___x_1540_ == 0 {
                    v___x_1541_ = lean_nat_dec_lt(v_x_1534_, v_x_1535_);
                    if v___x_1541_ == 0 {
                        if v_isShared_1539_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1538_, 1, v_acc_1521_);
                            v___x_1543_ = v___x_1538_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1545_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_x_1535_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_acc_1521_);
                            v___x_1543_ = v_reuseFailAlloc_1545_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1538_);
                        crate::leanh::lean_dec_ref(v_s_1536_);
                        crate::leanh::lean_dec(v_x_1535_);
                        crate::leanh::lean_dec_ref_known(v_s_u2081_1519_, 1);
                        crate::leanh::lean_dec_ref(v_acc_1521_);
                        v___x_1546_ = crate::leanh::lean_box(0);
                        return v___x_1546_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1538_);
                    crate::leanh::lean_dec(v_x_1535_);
                    v_isSharedCheck_1555_ =
                        (!crate::leanh::lean_is_exclusive(v_s_u2081_1519_)) as u8;
                    if v_isSharedCheck_1555_ == 0 {
                        v_unused_1556_ = crate::leanh::lean_ctor_get(v_s_u2081_1519_, 0);
                        crate::leanh::lean_dec(v_unused_1556_);
                        v___x_1548_ = v_s_u2081_1519_;
                        v_isShared_1549_ = v_isSharedCheck_1555_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_s_u2081_1519_);
                        v___x_1548_ = crate::leanh::lean_box(0);
                        v_isShared_1549_ = v_isSharedCheck_1555_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v_s_u2082_1520_ = v_s_1536_;
                v_acc_1521_ = v___x_1543_;
                state = 0;
                continue;
            }
            5 => {
                v___x_1550_ = l_Lean_Grind_AC_Seq_reverse(v_acc_1521_);
                v___x_1551_ = l_Lean_Grind_AC_Seq_concat(v___x_1550_, v_s_1536_);
                if v_isShared_1549_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1548_, 2);
                    crate::leanh::lean_ctor_set(v___x_1548_, 0, v___x_1551_);
                    v___x_1553_ = v___x_1548_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1554_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
                    v___x_1553_ = v_reuseFailAlloc_1554_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1553_;
            }
            7 => {
                v___x_1566_ = lean_nat_dec_eq(v_x_1559_, v_x_1561_);
                if v___x_1566_ == 0 {
                    v___x_1567_ = lean_nat_dec_lt(v_x_1559_, v_x_1561_);
                    if v___x_1567_ == 0 {
                        if v_isShared_1565_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1564_, 1, v_acc_1521_);
                            v___x_1569_ = v___x_1564_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_1571_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_x_1561_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_acc_1521_);
                            v___x_1569_ = v_reuseFailAlloc_1571_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1564_);
                        crate::leanh::lean_dec_ref(v_s_1562_);
                        crate::leanh::lean_dec(v_x_1561_);
                        crate::leanh::lean_dec_ref_known(v_s_u2081_1519_, 2);
                        crate::leanh::lean_dec_ref(v_acc_1521_);
                        v___x_1572_ = crate::leanh::lean_box(0);
                        return v___x_1572_;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_s_1560_);
                    crate::leanh::lean_del_object(v___x_1564_);
                    crate::leanh::lean_dec(v_x_1561_);
                    crate::leanh::lean_dec_ref_known(v_s_u2081_1519_, 2);
                    v_s_u2081_1519_ = v_s_1560_;
                    v_s_u2082_1520_ = v_s_1562_;
                    state = 0;
                    continue;
                }
            }
            8 => {
                v_s_u2082_1520_ = v_s_1562_;
                v_acc_1521_ = v___x_1569_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_subset(
    mut v_s_u2081_1575_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: u8 = 0;
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: u8 = 0;
    let mut v___x_1586_: u8 = 0;
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1592_: u8 = 0;
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1596_: u8 = 0;
    let mut v_unused_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: u8 = 0;
    let mut v___x_1604_: u8 = 0;
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_s_u2081_1575_) == 0 {
                    if crate::leanh::lean_obj_tag(v_s_u2082_1576_) == 0 {
                        v_x_1577_ = crate::leanh::lean_ctor_get(v_s_u2081_1575_, 0);
                        crate::leanh::lean_inc(v_x_1577_);
                        crate::leanh::lean_dec_ref_known(v_s_u2081_1575_, 1);
                        v_x_1578_ = crate::leanh::lean_ctor_get(v_s_u2082_1576_, 0);
                        crate::leanh::lean_inc(v_x_1578_);
                        crate::leanh::lean_dec_ref_known(v_s_u2082_1576_, 1);
                        v___x_1579_ = lean_nat_dec_eq(v_x_1577_, v_x_1578_);
                        crate::leanh::lean_dec(v_x_1578_);
                        crate::leanh::lean_dec(v_x_1577_);
                        if v___x_1579_ == 0 {
                            v___x_1580_ = crate::leanh::lean_box(0);
                            return v___x_1580_;
                        } else {
                            v___x_1581_ = crate::leanh::lean_box(1);
                            return v___x_1581_;
                        }
                    } else {
                        v_x_1582_ = crate::leanh::lean_ctor_get(v_s_u2081_1575_, 0);
                        v_x_1583_ = crate::leanh::lean_ctor_get(v_s_u2082_1576_, 0);
                        crate::leanh::lean_inc(v_x_1583_);
                        v_s_1584_ = crate::leanh::lean_ctor_get(v_s_u2082_1576_, 1);
                        crate::leanh::lean_inc_ref(v_s_1584_);
                        crate::leanh::lean_dec_ref_known(v_s_u2082_1576_, 2);
                        v___x_1585_ = lean_nat_dec_eq(v_x_1582_, v_x_1583_);
                        if v___x_1585_ == 0 {
                            v___x_1586_ = lean_nat_dec_lt(v_x_1582_, v_x_1583_);
                            if v___x_1586_ == 0 {
                                v___x_1587_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1587_, 0, v_x_1583_);
                                v___x_1588_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subset_go(v_s_u2081_1575_, v_s_1584_, v___x_1587_);
                                return v___x_1588_;
                            } else {
                                crate::leanh::lean_dec_ref(v_s_1584_);
                                crate::leanh::lean_dec(v_x_1583_);
                                crate::leanh::lean_dec_ref_known(v_s_u2081_1575_, 1);
                                v___x_1589_ = crate::leanh::lean_box(0);
                                return v___x_1589_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_x_1583_);
                            v_isSharedCheck_1596_ =
                                (!crate::leanh::lean_is_exclusive(v_s_u2081_1575_)) as u8;
                            if v_isSharedCheck_1596_ == 0 {
                                v_unused_1597_ = crate::leanh::lean_ctor_get(v_s_u2081_1575_, 0);
                                crate::leanh::lean_dec(v_unused_1597_);
                                v___x_1591_ = v_s_u2081_1575_;
                                v_isShared_1592_ = v_isSharedCheck_1596_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_s_u2081_1575_);
                                v___x_1591_ = crate::leanh::lean_box(0);
                                v_isShared_1592_ = v_isSharedCheck_1596_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_s_u2082_1576_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_s_u2082_1576_, 1);
                        crate::leanh::lean_dec_ref_known(v_s_u2081_1575_, 2);
                        v___x_1598_ = crate::leanh::lean_box(0);
                        return v___x_1598_;
                    } else {
                        v_x_1599_ = crate::leanh::lean_ctor_get(v_s_u2081_1575_, 0);
                        v_s_1600_ = crate::leanh::lean_ctor_get(v_s_u2081_1575_, 1);
                        v_x_1601_ = crate::leanh::lean_ctor_get(v_s_u2082_1576_, 0);
                        crate::leanh::lean_inc(v_x_1601_);
                        v_s_1602_ = crate::leanh::lean_ctor_get(v_s_u2082_1576_, 1);
                        crate::leanh::lean_inc_ref(v_s_1602_);
                        crate::leanh::lean_dec_ref_known(v_s_u2082_1576_, 2);
                        v___x_1603_ = lean_nat_dec_eq(v_x_1599_, v_x_1601_);
                        if v___x_1603_ == 0 {
                            v___x_1604_ = lean_nat_dec_lt(v_x_1599_, v_x_1601_);
                            if v___x_1604_ == 0 {
                                v___x_1605_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1605_, 0, v_x_1601_);
                                v___x_1606_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subset_go(v_s_u2081_1575_, v_s_1602_, v___x_1605_);
                                return v___x_1606_;
                            } else {
                                crate::leanh::lean_dec_ref(v_s_1602_);
                                crate::leanh::lean_dec(v_x_1601_);
                                crate::leanh::lean_dec_ref_known(v_s_u2081_1575_, 2);
                                v___x_1607_ = crate::leanh::lean_box(0);
                                return v___x_1607_;
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_s_1600_);
                            crate::leanh::lean_dec(v_x_1601_);
                            crate::leanh::lean_dec_ref_known(v_s_u2081_1575_, 2);
                            v_s_u2081_1575_ = v_s_1600_;
                            v_s_u2082_1576_ = v_s_1602_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1592_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1591_, 2);
                    crate::leanh::lean_ctor_set(v___x_1591_, 0, v_s_1584_);
                    v___x_1594_ = v___x_1591_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1595_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_s_1584_);
                    v___x_1594_ = v_reuseFailAlloc_1595_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1594_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go(
    mut v_x_1609_: *mut crate::leanh::LeanObject,
    mut v_s_1610_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: u8 = 0;
    let mut v_x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_s_1610_) == 0 {
                    v_x_1611_ = crate::leanh::lean_ctor_get(v_s_1610_, 0);
                    v___x_1612_ = lean_nat_dec_le(v_x_1609_, v_x_1611_);
                    return v___x_1612_;
                } else {
                    v_x_1613_ = crate::leanh::lean_ctor_get(v_s_1610_, 0);
                    v_s_1614_ = crate::leanh::lean_ctor_get(v_s_1610_, 1);
                    v___x_1615_ = lean_nat_dec_le(v_x_1609_, v_x_1613_);
                    if v___x_1615_ == 0 {
                        return v___x_1615_;
                    } else {
                        v_x_1609_ = v_x_1613_;
                        v_s_1610_ = v_s_1614_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go___boxed(
    mut v_x_1617_: *mut crate::leanh::LeanObject,
    mut v_s_1618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1619_: u8 = 0;
    let mut v_r_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1619_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go(
        v_x_1617_, v_s_1618_,
    );
    crate::leanh::lean_dec_ref(v_s_1618_);
    crate::leanh::lean_dec(v_x_1617_);
    v_r_1620_ = crate::leanh::lean_box((v_res_1619_) as usize);
    return v_r_1620_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_isSorted(mut v_s_1621_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_s_1621_) == 0 {
        let mut v___x_1622_: u8 = 0;
        v___x_1622_ = 1;
        return v___x_1622_;
    } else {
        let mut v_x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_s_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1625_: u8 = 0;
        v_x_1623_ = crate::leanh::lean_ctor_get(v_s_1621_, 0);
        v_s_1624_ = crate::leanh::lean_ctor_get(v_s_1621_, 1);
        v___x_1625_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go(
            v_x_1623_, v_s_1624_,
        );
        return v___x_1625_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_isSorted___boxed(
    mut v_s_1626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1627_: u8 = 0;
    let mut v_r_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1627_ = l_Lean_Grind_AC_Seq_isSorted(v_s_1626_);
    crate::leanh::lean_dec_ref(v_s_1626_);
    v_r_1628_ = crate::leanh::lean_box((v_res_1627_) as usize);
    return v_r_1628_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_contains(
    mut v_s_1629_: *mut crate::leanh::LeanObject,
    mut v_x_1630_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: u8 = 0;
    let mut v_x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_s_1629_) == 0 {
                    v_x_1631_ = crate::leanh::lean_ctor_get(v_s_1629_, 0);
                    v___x_1632_ = lean_nat_dec_eq(v_x_1630_, v_x_1631_);
                    return v___x_1632_;
                } else {
                    v_x_1633_ = crate::leanh::lean_ctor_get(v_s_1629_, 0);
                    v_s_1634_ = crate::leanh::lean_ctor_get(v_s_1629_, 1);
                    v___x_1635_ = lean_nat_dec_eq(v_x_1630_, v_x_1633_);
                    if v___x_1635_ == 0 {
                        v_s_1629_ = v_s_1634_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1635_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_contains___boxed(
    mut v_s_1637_: *mut crate::leanh::LeanObject,
    mut v_x_1638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1639_: u8 = 0;
    let mut v_r_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1639_ = l_Lean_Grind_AC_Seq_contains(v_s_1637_, v_x_1638_);
    crate::leanh::lean_dec(v_x_1638_);
    crate::leanh::lean_dec_ref(v_s_1637_);
    v_r_1640_ = crate::leanh::lean_box((v_res_1639_) as usize);
    return v_r_1640_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go(
    mut v_x_1641_: *mut crate::leanh::LeanObject,
    mut v_s_1642_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: u8 = 0;
    let mut v___x_1645_: u8 = 0;
    let mut v___x_1646_: u8 = 0;
    let mut v_x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: u8 = 0;
    let mut v___x_1651_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_s_1642_) == 0 {
                    v_x_1643_ = crate::leanh::lean_ctor_get(v_s_1642_, 0);
                    v___x_1644_ = lean_nat_dec_eq(v_x_1641_, v_x_1643_);
                    if v___x_1644_ == 0 {
                        v___x_1645_ = 1;
                        return v___x_1645_;
                    } else {
                        v___x_1646_ = 0;
                        return v___x_1646_;
                    }
                } else {
                    v_x_1647_ = crate::leanh::lean_ctor_get(v_s_1642_, 0);
                    v_s_1648_ = crate::leanh::lean_ctor_get(v_s_1642_, 1);
                    v___x_1649_ = lean_nat_dec_eq(v_x_1641_, v_x_1647_);
                    if v___x_1649_ == 0 {
                        v_x_1641_ = v_x_1647_;
                        v_s_1642_ = v_s_1648_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1651_ = 0;
                        return v___x_1651_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go___boxed(
    mut v_x_1652_: *mut crate::leanh::LeanObject,
    mut v_s_1653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1654_: u8 = 0;
    let mut v_r_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1654_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go(
            v_x_1652_, v_s_1653_,
        );
    crate::leanh::lean_dec_ref(v_s_1653_);
    crate::leanh::lean_dec(v_x_1652_);
    v_r_1655_ = crate::leanh::lean_box((v_res_1654_) as usize);
    return v_r_1655_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_noAdjacentDuplicates(
    mut v_s_1656_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_s_1656_) == 0 {
        let mut v___x_1657_: u8 = 0;
        v___x_1657_ = 1;
        return v___x_1657_;
    } else {
        let mut v_x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_s_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1660_: u8 = 0;
        v_x_1658_ = crate::leanh::lean_ctor_get(v_s_1656_, 0);
        v_s_1659_ = crate::leanh::lean_ctor_get(v_s_1656_, 1);
        v___x_1660_ =
            l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go(
                v_x_1658_, v_s_1659_,
            );
        return v___x_1660_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_noAdjacentDuplicates___boxed(
    mut v_s_1661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1662_: u8 = 0;
    let mut v_r_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1662_ = l_Lean_Grind_AC_Seq_noAdjacentDuplicates(v_s_1661_);
    crate::leanh::lean_dec_ref(v_s_1661_);
    v_r_1663_ = crate::leanh::lean_box((v_res_1662_) as usize);
    return v_r_1663_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_sharesVar(
    mut v_s_u2081_1664_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1665_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: u8 = 0;
    let mut v_x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: u8 = 0;
    let mut v_x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: u8 = 0;
    let mut v_x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: u8 = 0;
    let mut v___x_1684_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_s_u2081_1664_) == 0 {
                    if crate::leanh::lean_obj_tag(v_s_u2082_1665_) == 0 {
                        v_x_1666_ = crate::leanh::lean_ctor_get(v_s_u2081_1664_, 0);
                        v_x_1667_ = crate::leanh::lean_ctor_get(v_s_u2082_1665_, 0);
                        v___x_1668_ = lean_nat_dec_eq(v_x_1666_, v_x_1667_);
                        return v___x_1668_;
                    } else {
                        v_x_1669_ = crate::leanh::lean_ctor_get(v_s_u2081_1664_, 0);
                        v_x_1670_ = crate::leanh::lean_ctor_get(v_s_u2082_1665_, 0);
                        v_s_1671_ = crate::leanh::lean_ctor_get(v_s_u2082_1665_, 1);
                        v___x_1672_ = lean_nat_dec_eq(v_x_1669_, v_x_1670_);
                        if v___x_1672_ == 0 {
                            v_s_u2082_1665_ = v_s_1671_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_1672_;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_s_u2082_1665_) == 0 {
                        v_x_1674_ = crate::leanh::lean_ctor_get(v_s_u2081_1664_, 0);
                        v_s_1675_ = crate::leanh::lean_ctor_get(v_s_u2081_1664_, 1);
                        v_x_1676_ = crate::leanh::lean_ctor_get(v_s_u2082_1665_, 0);
                        v___x_1677_ = lean_nat_dec_eq(v_x_1674_, v_x_1676_);
                        if v___x_1677_ == 0 {
                            v_s_u2081_1664_ = v_s_1675_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_1677_;
                        }
                    } else {
                        v_x_1679_ = crate::leanh::lean_ctor_get(v_s_u2081_1664_, 0);
                        v_s_1680_ = crate::leanh::lean_ctor_get(v_s_u2081_1664_, 1);
                        v_x_1681_ = crate::leanh::lean_ctor_get(v_s_u2082_1665_, 0);
                        v_s_1682_ = crate::leanh::lean_ctor_get(v_s_u2082_1665_, 1);
                        v___x_1683_ = lean_nat_dec_eq(v_x_1679_, v_x_1681_);
                        if v___x_1683_ == 0 {
                            v___x_1684_ = lean_nat_dec_lt(v_x_1679_, v_x_1681_);
                            if v___x_1684_ == 0 {
                                v_s_u2082_1665_ = v_s_1682_;
                                state = 0;
                                continue;
                            } else {
                                v_s_u2081_1664_ = v_s_1680_;
                                state = 0;
                                continue;
                            }
                        } else {
                            return v___x_1683_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_sharesVar___boxed(
    mut v_s_u2081_1687_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1689_: u8 = 0;
    let mut v_r_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1689_ = l_Lean_Grind_AC_Seq_sharesVar(v_s_u2081_1687_, v_s_u2082_1688_);
    crate::leanh::lean_dec_ref(v_s_u2082_1688_);
    crate::leanh::lean_dec_ref(v_s_u2081_1687_);
    v_r_1690_ = crate::leanh::lean_box((v_res_1689_) as usize);
    return v_r_1690_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith_match__1_splitter___redArg(
    mut v_s_u2082_1691_: *mut crate::leanh::LeanObject,
    mut v_s_u2081_1692_: *mut crate::leanh::LeanObject,
    mut v_h__1_1693_: *mut crate::leanh::LeanObject,
    mut v_h__2_1694_: *mut crate::leanh::LeanObject,
    mut v_h__3_1695_: *mut crate::leanh::LeanObject,
    mut v_h__4_1696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_s_u2082_1691_) == 0 {
        crate::leanh::lean_dec(v_h__4_1696_);
        crate::leanh::lean_dec(v_h__3_1695_);
        if crate::leanh::lean_obj_tag(v_s_u2081_1692_) == 0 {
            let mut v_x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1694_);
            v_x_1697_ = crate::leanh::lean_ctor_get(v_s_u2082_1691_, 0);
            crate::leanh::lean_inc(v_x_1697_);
            crate::leanh::lean_dec_ref_known(v_s_u2082_1691_, 1);
            v_x_1698_ = crate::leanh::lean_ctor_get(v_s_u2081_1692_, 0);
            crate::leanh::lean_inc(v_x_1698_);
            crate::leanh::lean_dec_ref_known(v_s_u2081_1692_, 1);
            v___x_1699_ = crate::leanh::lean_apply_2(v_h__1_1693_, v_x_1697_, v_x_1698_);
            return v___x_1699_;
        } else {
            let mut v_x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_1693_);
            v_x_1700_ = crate::leanh::lean_ctor_get(v_s_u2082_1691_, 0);
            crate::leanh::lean_inc(v_x_1700_);
            crate::leanh::lean_dec_ref_known(v_s_u2082_1691_, 1);
            v_x_1701_ = crate::leanh::lean_ctor_get(v_s_u2081_1692_, 0);
            crate::leanh::lean_inc(v_x_1701_);
            v_s_1702_ = crate::leanh::lean_ctor_get(v_s_u2081_1692_, 1);
            crate::leanh::lean_inc_ref(v_s_1702_);
            crate::leanh::lean_dec_ref_known(v_s_u2081_1692_, 2);
            v___x_1703_ = crate::leanh::lean_apply_3(v_h__2_1694_, v_x_1700_, v_x_1701_, v_s_1702_);
            return v___x_1703_;
        }
    } else {
        crate::leanh::lean_dec(v_h__2_1694_);
        crate::leanh::lean_dec(v_h__1_1693_);
        if crate::leanh::lean_obj_tag(v_s_u2081_1692_) == 0 {
            let mut v_x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1696_);
            v_x_1704_ = crate::leanh::lean_ctor_get(v_s_u2082_1691_, 0);
            crate::leanh::lean_inc(v_x_1704_);
            v_s_1705_ = crate::leanh::lean_ctor_get(v_s_u2082_1691_, 1);
            crate::leanh::lean_inc_ref(v_s_1705_);
            crate::leanh::lean_dec_ref_known(v_s_u2082_1691_, 2);
            v_x_1706_ = crate::leanh::lean_ctor_get(v_s_u2081_1692_, 0);
            crate::leanh::lean_inc(v_x_1706_);
            crate::leanh::lean_dec_ref_known(v_s_u2081_1692_, 1);
            v___x_1707_ = crate::leanh::lean_apply_3(v_h__3_1695_, v_x_1704_, v_s_1705_, v_x_1706_);
            return v___x_1707_;
        } else {
            let mut v_x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1695_);
            v_x_1708_ = crate::leanh::lean_ctor_get(v_s_u2082_1691_, 0);
            crate::leanh::lean_inc(v_x_1708_);
            v_s_1709_ = crate::leanh::lean_ctor_get(v_s_u2082_1691_, 1);
            crate::leanh::lean_inc_ref(v_s_1709_);
            crate::leanh::lean_dec_ref_known(v_s_u2082_1691_, 2);
            v_x_1710_ = crate::leanh::lean_ctor_get(v_s_u2081_1692_, 0);
            crate::leanh::lean_inc(v_x_1710_);
            v_s_1711_ = crate::leanh::lean_ctor_get(v_s_u2081_1692_, 1);
            crate::leanh::lean_inc_ref(v_s_1711_);
            crate::leanh::lean_dec_ref_known(v_s_u2081_1692_, 2);
            v___x_1712_ = crate::leanh::lean_apply_4(
                v_h__4_1696_,
                v_x_1708_,
                v_s_1709_,
                v_x_1710_,
                v_s_1711_,
            );
            return v___x_1712_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith_match__1_splitter(
    mut v_motive_1713_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1714_: *mut crate::leanh::LeanObject,
    mut v_s_u2081_1715_: *mut crate::leanh::LeanObject,
    mut v_h__1_1716_: *mut crate::leanh::LeanObject,
    mut v_h__2_1717_: *mut crate::leanh::LeanObject,
    mut v_h__3_1718_: *mut crate::leanh::LeanObject,
    mut v_h__4_1719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_s_u2082_1714_) == 0 {
        crate::leanh::lean_dec(v_h__4_1719_);
        crate::leanh::lean_dec(v_h__3_1718_);
        if crate::leanh::lean_obj_tag(v_s_u2081_1715_) == 0 {
            let mut v_x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1717_);
            v_x_1720_ = crate::leanh::lean_ctor_get(v_s_u2082_1714_, 0);
            crate::leanh::lean_inc(v_x_1720_);
            crate::leanh::lean_dec_ref_known(v_s_u2082_1714_, 1);
            v_x_1721_ = crate::leanh::lean_ctor_get(v_s_u2081_1715_, 0);
            crate::leanh::lean_inc(v_x_1721_);
            crate::leanh::lean_dec_ref_known(v_s_u2081_1715_, 1);
            v___x_1722_ = crate::leanh::lean_apply_2(v_h__1_1716_, v_x_1720_, v_x_1721_);
            return v___x_1722_;
        } else {
            let mut v_x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_1716_);
            v_x_1723_ = crate::leanh::lean_ctor_get(v_s_u2082_1714_, 0);
            crate::leanh::lean_inc(v_x_1723_);
            crate::leanh::lean_dec_ref_known(v_s_u2082_1714_, 1);
            v_x_1724_ = crate::leanh::lean_ctor_get(v_s_u2081_1715_, 0);
            crate::leanh::lean_inc(v_x_1724_);
            v_s_1725_ = crate::leanh::lean_ctor_get(v_s_u2081_1715_, 1);
            crate::leanh::lean_inc_ref(v_s_1725_);
            crate::leanh::lean_dec_ref_known(v_s_u2081_1715_, 2);
            v___x_1726_ = crate::leanh::lean_apply_3(v_h__2_1717_, v_x_1723_, v_x_1724_, v_s_1725_);
            return v___x_1726_;
        }
    } else {
        crate::leanh::lean_dec(v_h__2_1717_);
        crate::leanh::lean_dec(v_h__1_1716_);
        if crate::leanh::lean_obj_tag(v_s_u2081_1715_) == 0 {
            let mut v_x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1719_);
            v_x_1727_ = crate::leanh::lean_ctor_get(v_s_u2082_1714_, 0);
            crate::leanh::lean_inc(v_x_1727_);
            v_s_1728_ = crate::leanh::lean_ctor_get(v_s_u2082_1714_, 1);
            crate::leanh::lean_inc_ref(v_s_1728_);
            crate::leanh::lean_dec_ref_known(v_s_u2082_1714_, 2);
            v_x_1729_ = crate::leanh::lean_ctor_get(v_s_u2081_1715_, 0);
            crate::leanh::lean_inc(v_x_1729_);
            crate::leanh::lean_dec_ref_known(v_s_u2081_1715_, 1);
            v___x_1730_ = crate::leanh::lean_apply_3(v_h__3_1718_, v_x_1727_, v_s_1728_, v_x_1729_);
            return v___x_1730_;
        } else {
            let mut v_x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1718_);
            v_x_1731_ = crate::leanh::lean_ctor_get(v_s_u2082_1714_, 0);
            crate::leanh::lean_inc(v_x_1731_);
            v_s_1732_ = crate::leanh::lean_ctor_get(v_s_u2082_1714_, 1);
            crate::leanh::lean_inc_ref(v_s_1732_);
            crate::leanh::lean_dec_ref_known(v_s_u2082_1714_, 2);
            v_x_1733_ = crate::leanh::lean_ctor_get(v_s_u2081_1715_, 0);
            crate::leanh::lean_inc(v_x_1733_);
            v_s_1734_ = crate::leanh::lean_ctor_get(v_s_u2081_1715_, 1);
            crate::leanh::lean_inc_ref(v_s_1734_);
            crate::leanh::lean_dec_ref_known(v_s_u2081_1715_, 2);
            v___x_1735_ = crate::leanh::lean_apply_4(
                v_h__4_1719_,
                v_x_1731_,
                v_s_1732_,
                v_x_1733_,
                v_s_1734_,
            );
            return v___x_1735_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_toSeq_x3f_go(
    mut v_xs_1736_: *mut crate::leanh::LeanObject,
    mut v_acc_1737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1748_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_xs_1736_) == 0 {
                    v___x_1738_ = l_Lean_Grind_AC_Seq_reverse(v_acc_1737_);
                    return v___x_1738_;
                } else {
                    v_head_1739_ = crate::leanh::lean_ctor_get(v_xs_1736_, 0);
                    v_tail_1740_ = crate::leanh::lean_ctor_get(v_xs_1736_, 1);
                    v_isSharedCheck_1748_ = (!crate::leanh::lean_is_exclusive(v_xs_1736_)) as u8;
                    if v_isSharedCheck_1748_ == 0 {
                        v___x_1742_ = v_xs_1736_;
                        v_isShared_1743_ = v_isSharedCheck_1748_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1740_);
                        crate::leanh::lean_inc(v_head_1739_);
                        crate::leanh::lean_dec(v_xs_1736_);
                        v___x_1742_ = crate::leanh::lean_box(0);
                        v_isShared_1743_ = v_isSharedCheck_1748_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1743_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1742_, 1, v_acc_1737_);
                    v___x_1745_ = v___x_1742_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1747_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_head_1739_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_acc_1737_);
                    v___x_1745_ = v_reuseFailAlloc_1747_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_xs_1736_ = v_tail_1740_;
                v_acc_1737_ = v___x_1745_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_toSeq_x3f(
    mut v_xs_1749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_xs_1749_) == 0 {
        let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1750_ = crate::leanh::lean_box(0);
        return v___x_1750_;
    } else {
        let mut v_head_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_1751_ = crate::leanh::lean_ctor_get(v_xs_1749_, 0);
        crate::leanh::lean_inc(v_head_1751_);
        v_tail_1752_ = crate::leanh::lean_ctor_get(v_xs_1749_, 1);
        crate::leanh::lean_inc(v_tail_1752_);
        crate::leanh::lean_dec_ref_known(v_xs_1749_, 2);
        v___x_1753_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1753_, 0, v_head_1751_);
        v___x_1754_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_toSeq_x3f_go(
            v_tail_1752_,
            v___x_1753_,
        );
        v___x_1755_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1755_, 0, v___x_1754_);
        return v___x_1755_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(
    mut v_s_x3f_1756_: *mut crate::leanh::LeanObject,
    mut v_x_1757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1763_: u8 = 0;
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1768_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_s_x3f_1756_) == 0 {
                    v___x_1758_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1758_, 0, v_x_1757_);
                    v___x_1759_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1759_, 0, v___x_1758_);
                    return v___x_1759_;
                } else {
                    v_val_1760_ = crate::leanh::lean_ctor_get(v_s_x3f_1756_, 0);
                    v_isSharedCheck_1768_ = (!crate::leanh::lean_is_exclusive(v_s_x3f_1756_)) as u8;
                    if v_isSharedCheck_1768_ == 0 {
                        v___x_1762_ = v_s_x3f_1756_;
                        v_isShared_1763_ = v_isSharedCheck_1768_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1760_);
                        crate::leanh::lean_dec(v_s_x3f_1756_);
                        v___x_1762_ = crate::leanh::lean_box(0);
                        v_isShared_1763_ = v_isSharedCheck_1768_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1764_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1764_, 0, v_x_1757_);
                crate::leanh::lean_ctor_set(v___x_1764_, 1, v_val_1760_);
                if v_isShared_1763_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1762_, 0, v___x_1764_);
                    v___x_1766_ = v___x_1762_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1767_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
                    v___x_1766_ = v_reuseFailAlloc_1767_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1766_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
    mut v_s_x3f_1769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1773_: u8 = 0;
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1778_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_s_x3f_1769_) == 0 {
                    return v_s_x3f_1769_;
                } else {
                    v_val_1770_ = crate::leanh::lean_ctor_get(v_s_x3f_1769_, 0);
                    v_isSharedCheck_1778_ = (!crate::leanh::lean_is_exclusive(v_s_x3f_1769_)) as u8;
                    if v_isSharedCheck_1778_ == 0 {
                        v___x_1772_ = v_s_x3f_1769_;
                        v_isShared_1773_ = v_isSharedCheck_1778_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1770_);
                        crate::leanh::lean_dec(v_s_x3f_1769_);
                        v___x_1772_ = crate::leanh::lean_box(0);
                        v_isShared_1773_ = v_isSharedCheck_1778_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1774_ = l_Lean_Grind_AC_Seq_reverse(v_val_1770_);
                if v_isShared_1773_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1772_, 0, v___x_1774_);
                    v___x_1776_ = v___x_1772_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1777_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1774_);
                    v___x_1776_ = v_reuseFailAlloc_1777_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1776_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(
    mut v_s_x3f_1779_: *mut crate::leanh::LeanObject,
    mut v_s_x27_1780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1785_: u8 = 0;
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1790_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_s_x3f_1779_) == 0 {
                    v___x_1781_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1781_, 0, v_s_x27_1780_);
                    return v___x_1781_;
                } else {
                    v_val_1782_ = crate::leanh::lean_ctor_get(v_s_x3f_1779_, 0);
                    v_isSharedCheck_1790_ = (!crate::leanh::lean_is_exclusive(v_s_x3f_1779_)) as u8;
                    if v_isSharedCheck_1790_ == 0 {
                        v___x_1784_ = v_s_x3f_1779_;
                        v_isShared_1785_ = v_isSharedCheck_1790_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1782_);
                        crate::leanh::lean_dec(v_s_x3f_1779_);
                        v___x_1784_ = crate::leanh::lean_box(0);
                        v_isShared_1785_ = v_isSharedCheck_1790_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1786_ = l_Lean_Grind_AC_Seq_concat(v_val_1782_, v_s_x27_1780_);
                if v_isShared_1785_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1784_, 0, v___x_1786_);
                    v___x_1788_ = v___x_1784_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1789_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1786_);
                    v___x_1788_ = v_reuseFailAlloc_1789_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(
    mut v_r_u2081_1791_: *mut crate::leanh::LeanObject,
    mut v_c_1792_: *mut crate::leanh::LeanObject,
    mut v_r_u2082_1793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1799_: u8 = 0;
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1805_: u8 = 0;
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_r_u2081_1791_) == 1 {
                    if crate::leanh::lean_obj_tag(v_c_1792_) == 1 {
                        if crate::leanh::lean_obj_tag(v_r_u2082_1793_) == 1 {
                            v_val_1794_ = crate::leanh::lean_ctor_get(v_r_u2081_1791_, 0);
                            v_val_1795_ = crate::leanh::lean_ctor_get(v_c_1792_, 0);
                            v_val_1796_ = crate::leanh::lean_ctor_get(v_r_u2082_1793_, 0);
                            v_isSharedCheck_1805_ =
                                (!crate::leanh::lean_is_exclusive(v_r_u2082_1793_)) as u8;
                            if v_isSharedCheck_1805_ == 0 {
                                v___x_1798_ = v_r_u2082_1793_;
                                v_isShared_1799_ = v_isSharedCheck_1805_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_1796_);
                                crate::leanh::lean_dec(v_r_u2082_1793_);
                                v___x_1798_ = crate::leanh::lean_box(0);
                                v_isShared_1799_ = v_isSharedCheck_1805_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_r_u2082_1793_);
                            v___x_1806_ = crate::leanh::lean_box(0);
                            return v___x_1806_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_r_u2082_1793_);
                        v___x_1807_ = crate::leanh::lean_box(0);
                        return v___x_1807_;
                    }
                } else {
                    crate::leanh::lean_dec(v_r_u2082_1793_);
                    v___x_1808_ = crate::leanh::lean_box(0);
                    return v___x_1808_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_val_1795_);
                v___x_1800_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1800_, 0, v_val_1795_);
                crate::leanh::lean_ctor_set(v___x_1800_, 1, v_val_1796_);
                crate::leanh::lean_inc(v_val_1794_);
                v___x_1801_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1801_, 0, v_val_1794_);
                crate::leanh::lean_ctor_set(v___x_1801_, 1, v___x_1800_);
                if v_isShared_1799_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1798_, 0, v___x_1801_);
                    v___x_1803_ = v___x_1798_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1804_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
                    v___x_1803_ = v_reuseFailAlloc_1804_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult___boxed(
    mut v_r_u2081_1809_: *mut crate::leanh::LeanObject,
    mut v_c_1810_: *mut crate::leanh::LeanObject,
    mut v_r_u2082_1811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1812_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(
            v_r_u2081_1809_,
            v_c_1810_,
            v_r_u2082_1811_,
        );
    crate::leanh::lean_dec(v_c_1810_);
    crate::leanh::lean_dec(v_r_u2081_1809_);
    return v_res_1812_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_go(
    mut v_s_u2081_1813_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1814_: *mut crate::leanh::LeanObject,
    mut v_r_u2081_1815_: *mut crate::leanh::LeanObject,
    mut v_c_1816_: *mut crate::leanh::LeanObject,
    mut v_r_u2082_1817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: u8 = 0;
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: u8 = 0;
    let mut v___x_1836_: u8 = 0;
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: u8 = 0;
    let mut v___x_1855_: u8 = 0;
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: u8 = 0;
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_s_u2081_1813_) == 0 {
                    if crate::leanh::lean_obj_tag(v_s_u2082_1814_) == 0 {
                        v_x_1818_ = crate::leanh::lean_ctor_get(v_s_u2081_1813_, 0);
                        crate::leanh::lean_inc(v_x_1818_);
                        crate::leanh::lean_dec_ref_known(v_s_u2081_1813_, 1);
                        v_x_1819_ = crate::leanh::lean_ctor_get(v_s_u2082_1814_, 0);
                        crate::leanh::lean_inc(v_x_1819_);
                        crate::leanh::lean_dec_ref_known(v_s_u2082_1814_, 1);
                        v___x_1820_ = lean_nat_dec_eq(v_x_1818_, v_x_1819_);
                        if v___x_1820_ == 0 {
                            v___x_1821_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(
                                    v_r_u2081_1815_,
                                    v_x_1818_,
                                );
                            v___x_1822_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
                                    v___x_1821_,
                                );
                            v___x_1823_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
                                    v_c_1816_,
                                );
                            v___x_1824_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(
                                    v_r_u2082_1817_,
                                    v_x_1819_,
                                );
                            v___x_1825_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
                                    v___x_1824_,
                                );
                            v___x_1826_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_1822_, v___x_1823_, v___x_1825_);
                            crate::leanh::lean_dec(v___x_1823_);
                            crate::leanh::lean_dec(v___x_1822_);
                            return v___x_1826_;
                        } else {
                            crate::leanh::lean_dec(v_x_1819_);
                            v___x_1827_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
                                    v_r_u2081_1815_,
                                );
                            v___x_1828_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(
                                    v_c_1816_, v_x_1818_,
                                );
                            v___x_1829_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
                                    v___x_1828_,
                                );
                            v___x_1830_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
                                    v_r_u2082_1817_,
                                );
                            v___x_1831_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_1827_, v___x_1829_, v___x_1830_);
                            crate::leanh::lean_dec(v___x_1829_);
                            crate::leanh::lean_dec(v___x_1827_);
                            return v___x_1831_;
                        }
                    } else {
                        v_x_1832_ = crate::leanh::lean_ctor_get(v_s_u2081_1813_, 0);
                        v_x_1833_ = crate::leanh::lean_ctor_get(v_s_u2082_1814_, 0);
                        v_s_1834_ = crate::leanh::lean_ctor_get(v_s_u2082_1814_, 1);
                        v___x_1835_ = lean_nat_dec_eq(v_x_1832_, v_x_1833_);
                        if v___x_1835_ == 0 {
                            v___x_1836_ = lean_nat_dec_lt(v_x_1832_, v_x_1833_);
                            if v___x_1836_ == 0 {
                                crate::leanh::lean_inc_ref(v_s_1834_);
                                crate::leanh::lean_inc(v_x_1833_);
                                crate::leanh::lean_dec_ref_known(v_s_u2082_1814_, 2);
                                v___x_1837_ =
                                    l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(
                                        v_r_u2082_1817_,
                                        v_x_1833_,
                                    );
                                v_s_u2082_1814_ = v_s_1834_;
                                v_r_u2082_1817_ = v___x_1837_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_x_1832_);
                                crate::leanh::lean_dec_ref_known(v_s_u2081_1813_, 1);
                                v___x_1839_ =
                                    l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(
                                        v_r_u2081_1815_,
                                        v_x_1832_,
                                    );
                                v___x_1840_ =
                                    l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
                                        v___x_1839_,
                                    );
                                v___x_1841_ =
                                    l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
                                        v_c_1816_,
                                    );
                                v___x_1842_ =
                                    l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
                                        v_r_u2082_1817_,
                                    );
                                v___x_1843_ =
                                    l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(
                                        v___x_1842_,
                                        v_s_u2082_1814_,
                                    );
                                v___x_1844_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_1840_, v___x_1841_, v___x_1843_);
                                crate::leanh::lean_dec(v___x_1841_);
                                crate::leanh::lean_dec(v___x_1840_);
                                return v___x_1844_;
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_s_1834_);
                            crate::leanh::lean_inc(v_x_1832_);
                            crate::leanh::lean_dec_ref_known(v_s_u2082_1814_, 2);
                            crate::leanh::lean_dec_ref_known(v_s_u2081_1813_, 1);
                            v___x_1845_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
                                    v_r_u2081_1815_,
                                );
                            v___x_1846_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(
                                    v_c_1816_, v_x_1832_,
                                );
                            v___x_1847_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
                                    v___x_1846_,
                                );
                            v___x_1848_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
                                    v_r_u2082_1817_,
                                );
                            v___x_1849_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(
                                    v___x_1848_,
                                    v_s_1834_,
                                );
                            v___x_1850_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_1845_, v___x_1847_, v___x_1849_);
                            crate::leanh::lean_dec(v___x_1847_);
                            crate::leanh::lean_dec(v___x_1845_);
                            return v___x_1850_;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_s_u2082_1814_) == 0 {
                        v_x_1851_ = crate::leanh::lean_ctor_get(v_s_u2081_1813_, 0);
                        v_s_1852_ = crate::leanh::lean_ctor_get(v_s_u2081_1813_, 1);
                        v_x_1853_ = crate::leanh::lean_ctor_get(v_s_u2082_1814_, 0);
                        v___x_1854_ = lean_nat_dec_eq(v_x_1851_, v_x_1853_);
                        if v___x_1854_ == 0 {
                            v___x_1855_ = lean_nat_dec_lt(v_x_1851_, v_x_1853_);
                            if v___x_1855_ == 0 {
                                crate::leanh::lean_inc(v_x_1853_);
                                crate::leanh::lean_dec_ref_known(v_s_u2082_1814_, 1);
                                v___x_1856_ =
                                    l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
                                        v_r_u2081_1815_,
                                    );
                                v___x_1857_ =
                                    l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(
                                        v___x_1856_,
                                        v_s_u2081_1813_,
                                    );
                                v___x_1858_ =
                                    l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
                                        v_c_1816_,
                                    );
                                v___x_1859_ =
                                    l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(
                                        v_r_u2082_1817_,
                                        v_x_1853_,
                                    );
                                v___x_1860_ =
                                    l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
                                        v___x_1859_,
                                    );
                                v___x_1861_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_1857_, v___x_1858_, v___x_1860_);
                                crate::leanh::lean_dec(v___x_1858_);
                                crate::leanh::lean_dec(v___x_1857_);
                                return v___x_1861_;
                            } else {
                                crate::leanh::lean_inc_ref(v_s_1852_);
                                crate::leanh::lean_inc(v_x_1851_);
                                crate::leanh::lean_dec_ref_known(v_s_u2081_1813_, 2);
                                v___x_1862_ =
                                    l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(
                                        v_r_u2081_1815_,
                                        v_x_1851_,
                                    );
                                v_s_u2081_1813_ = v_s_1852_;
                                v_r_u2081_1815_ = v___x_1862_;
                                state = 0;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_s_1852_);
                            crate::leanh::lean_inc(v_x_1851_);
                            crate::leanh::lean_dec_ref_known(v_s_u2082_1814_, 1);
                            crate::leanh::lean_dec_ref_known(v_s_u2081_1813_, 2);
                            v___x_1864_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
                                    v_r_u2081_1815_,
                                );
                            v___x_1865_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(
                                    v___x_1864_,
                                    v_s_1852_,
                                );
                            v___x_1866_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(
                                    v_c_1816_, v_x_1851_,
                                );
                            v___x_1867_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
                                    v___x_1866_,
                                );
                            v___x_1868_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(
                                    v_r_u2082_1817_,
                                );
                            v___x_1869_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_1865_, v___x_1867_, v___x_1868_);
                            crate::leanh::lean_dec(v___x_1867_);
                            crate::leanh::lean_dec(v___x_1865_);
                            return v___x_1869_;
                        }
                    } else {
                        v_x_1870_ = crate::leanh::lean_ctor_get(v_s_u2081_1813_, 0);
                        v_s_1871_ = crate::leanh::lean_ctor_get(v_s_u2081_1813_, 1);
                        v_x_1872_ = crate::leanh::lean_ctor_get(v_s_u2082_1814_, 0);
                        v_s_1873_ = crate::leanh::lean_ctor_get(v_s_u2082_1814_, 1);
                        v___x_1874_ = lean_nat_dec_eq(v_x_1870_, v_x_1872_);
                        if v___x_1874_ == 0 {
                            v___x_1875_ = lean_nat_dec_lt(v_x_1870_, v_x_1872_);
                            if v___x_1875_ == 0 {
                                crate::leanh::lean_inc_ref(v_s_1873_);
                                crate::leanh::lean_inc(v_x_1872_);
                                crate::leanh::lean_dec_ref_known(v_s_u2082_1814_, 2);
                                v___x_1876_ =
                                    l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(
                                        v_r_u2082_1817_,
                                        v_x_1872_,
                                    );
                                v_s_u2082_1814_ = v_s_1873_;
                                v_r_u2082_1817_ = v___x_1876_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_inc_ref(v_s_1871_);
                                crate::leanh::lean_inc(v_x_1870_);
                                crate::leanh::lean_dec_ref_known(v_s_u2081_1813_, 2);
                                v___x_1878_ =
                                    l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(
                                        v_r_u2081_1815_,
                                        v_x_1870_,
                                    );
                                v_s_u2081_1813_ = v_s_1871_;
                                v_r_u2081_1815_ = v___x_1878_;
                                state = 0;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_s_1873_);
                            crate::leanh::lean_inc_ref(v_s_1871_);
                            crate::leanh::lean_inc(v_x_1870_);
                            crate::leanh::lean_dec_ref_known(v_s_u2082_1814_, 2);
                            crate::leanh::lean_dec_ref_known(v_s_u2081_1813_, 2);
                            v___x_1880_ =
                                l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(
                                    v_c_1816_, v_x_1870_,
                                );
                            v_s_u2081_1813_ = v_s_1871_;
                            v_s_u2082_1814_ = v_s_1873_;
                            v_c_1816_ = v___x_1880_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_superposeAC_x3f(
    mut v_s_u2081_1882_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1884_ = crate::leanh::lean_box(0);
    v___x_1885_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_go(
        v_s_u2081_1882_,
        v_s_u2082_1883_,
        v___x_1884_,
        v___x_1884_,
        v___x_1884_,
    );
    return v___x_1885_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go(
    mut v_s_u2081_1886_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1887_: *mut crate::leanh::LeanObject,
    mut v_p_1888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1895_: u8 = 0;
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1900_: u8 = 0;
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1905_: u8 = 0;
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_s_u2081_1886_);
                v___x_1889_ =
                    l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(
                        v_s_u2082_1887_,
                        v_s_u2081_1886_,
                    );
                match crate::leanh::lean_obj_tag(v___x_1889_) {
                    0 => {
                        if crate::leanh::lean_obj_tag(v_s_u2081_1886_) == 0 {
                            crate::leanh::lean_dec_ref_known(v_s_u2081_1886_, 1);
                            crate::leanh::lean_dec_ref(v_p_1888_);
                            v___x_1890_ = crate::leanh::lean_box(0);
                            return v___x_1890_;
                        } else {
                            v_x_1891_ = crate::leanh::lean_ctor_get(v_s_u2081_1886_, 0);
                            v_s_1892_ = crate::leanh::lean_ctor_get(v_s_u2081_1886_, 1);
                            v_isSharedCheck_1900_ =
                                (!crate::leanh::lean_is_exclusive(v_s_u2081_1886_)) as u8;
                            if v_isSharedCheck_1900_ == 0 {
                                v___x_1894_ = v_s_u2081_1886_;
                                v_isShared_1895_ = v_isSharedCheck_1900_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_s_1892_);
                                crate::leanh::lean_inc(v_x_1891_);
                                crate::leanh::lean_dec(v_s_u2081_1886_);
                                v___x_1894_ = crate::leanh::lean_box(0);
                                v_isShared_1895_ = v_isSharedCheck_1900_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref(v_p_1888_);
                        crate::leanh::lean_dec_ref(v_s_u2081_1886_);
                        v___x_1901_ = crate::leanh::lean_box(0);
                        return v___x_1901_;
                    }
                    _ => {
                        v_s_1902_ = crate::leanh::lean_ctor_get(v___x_1889_, 0);
                        v_isSharedCheck_1912_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1889_)) as u8;
                        if v_isSharedCheck_1912_ == 0 {
                            v___x_1904_ = v___x_1889_;
                            v_isShared_1905_ = v_isSharedCheck_1912_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_s_1902_);
                            crate::leanh::lean_dec(v___x_1889_);
                            v___x_1904_ = crate::leanh::lean_box(0);
                            v_isShared_1905_ = v_isSharedCheck_1912_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1895_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1894_, 1, v_p_1888_);
                    v___x_1897_ = v___x_1894_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1899_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_x_1891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_p_1888_);
                    v___x_1897_ = v_reuseFailAlloc_1899_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_s_u2081_1886_ = v_s_1892_;
                v_p_1888_ = v___x_1897_;
                state = 0;
                continue;
            }
            3 => {
                v___x_1906_ = l_Lean_Grind_AC_Seq_reverse(v_p_1888_);
                v___x_1907_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1907_, 0, v_s_u2081_1886_);
                crate::leanh::lean_ctor_set(v___x_1907_, 1, v_s_1902_);
                v___x_1908_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1908_, 0, v___x_1906_);
                crate::leanh::lean_ctor_set(v___x_1908_, 1, v___x_1907_);
                if v_isShared_1905_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1904_, 1);
                    crate::leanh::lean_ctor_set(v___x_1904_, 0, v___x_1908_);
                    v___x_1910_ = v___x_1904_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1911_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
                    v___x_1910_ = v_reuseFailAlloc_1911_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1910_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go___boxed(
    mut v_s_u2081_1913_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1914_: *mut crate::leanh::LeanObject,
    mut v_p_1915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1916_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go(
        v_s_u2081_1913_,
        v_s_u2082_1914_,
        v_p_1915_,
    );
    crate::leanh::lean_dec_ref(v_s_u2082_1914_);
    return v_res_1916_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_superpose_x3f(
    mut v_s_u2081_1917_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_s_u2081_1917_) == 0 {
        let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v_s_u2081_1917_, 1);
        v___x_1919_ = crate::leanh::lean_box(0);
        return v___x_1919_;
    } else {
        let mut v_x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_s_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_x_1920_ = crate::leanh::lean_ctor_get(v_s_u2081_1917_, 0);
        crate::leanh::lean_inc(v_x_1920_);
        v_s_1921_ = crate::leanh::lean_ctor_get(v_s_u2081_1917_, 1);
        crate::leanh::lean_inc_ref(v_s_1921_);
        crate::leanh::lean_dec_ref_known(v_s_u2081_1917_, 2);
        v___x_1922_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1922_, 0, v_x_1920_);
        v___x_1923_ =
            l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go(
                v_s_1921_,
                v_s_u2082_1918_,
                v___x_1922_,
            );
        return v___x_1923_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_superpose_x3f___boxed(
    mut v_s_u2081_1924_: *mut crate::leanh::LeanObject,
    mut v_s_u2082_1925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1926_ = l_Lean_Grind_AC_Seq_superpose_x3f(v_s_u2081_1924_, v_s_u2082_1925_);
    crate::leanh::lean_dec_ref(v_s_u2082_1925_);
    return v_res_1926_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_firstVar(
    mut v_s_1927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1928_ = crate::leanh::lean_ctor_get(v_s_1927_, 0);
    crate::leanh::lean_inc(v_x_1928_);
    return v_x_1928_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_firstVar___boxed(
    mut v_s_1929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1930_ = l_Lean_Grind_AC_Seq_firstVar(v_s_1929_);
    crate::leanh::lean_dec_ref(v_s_1929_);
    return v_res_1930_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_startsWithVar(
    mut v_s_1931_: *mut crate::leanh::LeanObject,
    mut v_x_1932_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: u8 = 0;
    v_x_1933_ = crate::leanh::lean_ctor_get(v_s_1931_, 0);
    v___x_1934_ = lean_nat_dec_eq(v_x_1932_, v_x_1933_);
    return v___x_1934_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_startsWithVar___boxed(
    mut v_s_1935_: *mut crate::leanh::LeanObject,
    mut v_x_1936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1937_: u8 = 0;
    let mut v_r_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1937_ = l_Lean_Grind_AC_Seq_startsWithVar(v_s_1935_, v_x_1936_);
    crate::leanh::lean_dec(v_x_1936_);
    crate::leanh::lean_dec_ref(v_s_1935_);
    v_r_1938_ = crate::leanh::lean_box((v_res_1937_) as usize);
    return v_r_1938_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_lastVar(
    mut v_s_1939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_s_1939_) == 0 {
                    v_x_1940_ = crate::leanh::lean_ctor_get(v_s_1939_, 0);
                    crate::leanh::lean_inc(v_x_1940_);
                    return v_x_1940_;
                } else {
                    v_s_1941_ = crate::leanh::lean_ctor_get(v_s_1939_, 1);
                    v_s_1939_ = v_s_1941_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_lastVar___boxed(
    mut v_s_1943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1944_ = l_Lean_Grind_AC_Seq_lastVar(v_s_1943_);
    crate::leanh::lean_dec_ref(v_s_1943_);
    return v_res_1944_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_endsWithVar(
    mut v_s_1945_: *mut crate::leanh::LeanObject,
    mut v_x_1946_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: u8 = 0;
    let mut v_s_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_s_1945_) == 0 {
                    v_x_1947_ = crate::leanh::lean_ctor_get(v_s_1945_, 0);
                    v___x_1948_ = lean_nat_dec_eq(v_x_1946_, v_x_1947_);
                    return v___x_1948_;
                } else {
                    v_s_1949_ = crate::leanh::lean_ctor_get(v_s_1945_, 1);
                    v_s_1945_ = v_s_1949_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_endsWithVar___boxed(
    mut v_s_1951_: *mut crate::leanh::LeanObject,
    mut v_x_1952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1953_: u8 = 0;
    let mut v_r_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1953_ = l_Lean_Grind_AC_Seq_endsWithVar(v_s_1951_, v_x_1952_);
    crate::leanh::lean_dec(v_x_1952_);
    crate::leanh::lean_dec_ref(v_s_1951_);
    v_r_1954_ = crate::leanh::lean_box((v_res_1953_) as usize);
    return v_r_1954_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_AC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Grind_AC_instInhabitedStartsWithResult_default =
        _init_l_Lean_Grind_AC_instInhabitedStartsWithResult_default();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_AC_instInhabitedStartsWithResult_default);
    l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instInhabitedStartsWithResult = _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instInhabitedStartsWithResult();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instInhabitedStartsWithResult,
    );
    l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_a =
        _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_a();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_a,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_AC_Seq(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_AC_Seq(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_AC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Ord(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
}
