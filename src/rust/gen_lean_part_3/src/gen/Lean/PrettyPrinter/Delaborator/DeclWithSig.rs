// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.DeclWithSig
// Imports: Lean.Parser.Types Lean.Parser.Command
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Parser::Basic::{
    l_Lean_Parser_andthen, l_Lean_Parser_leadingNode, l_Lean_Parser_mkAntiquot,
    l_Lean_Parser_termParser, l_Lean_Parser_withAntiquot,
};
use crate::r#gen::Lean::Parser::Command::{
    initialize_Lean_Parser_Command, l_Lean_Parser_Command_declSig,
    l_Lean_Parser_Command_declSig_formatter___boxed,
    l_Lean_Parser_Command_declSig_parenthesizer___boxed, runtime_initialize_Lean_Parser_Command,
};
use crate::r#gen::Lean::Parser::Extra::{
    l_Lean_Parser_leadingNode_formatter___boxed, l_Lean_Parser_mkAntiquot_formatter___boxed,
    l_Lean_Parser_mkAntiquot_parenthesizer___boxed, l_Lean_Parser_termParser_formatter___boxed,
    l_Lean_Parser_termParser_parenthesizer___boxed,
};
use crate::r#gen::Lean::Parser::Types::{
    initialize_Lean_Parser_Types, l_Lean_Parser_maxPrec, l_Lean_Parser_withCache,
    runtime_initialize_Lean_Parser_Types,
};
use crate::r#gen::Lean::PrettyPrinter::Formatter::{
    l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_orelse_formatter, l_Lean_PrettyPrinter_formatterAttribute,
};
use crate::r#gen::Lean::PrettyPrinter::Parenthesizer::{
    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer,
    l_Lean_PrettyPrinter_parenthesizerAttribute,
};
pub static l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__1_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 0,
    ],
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__2_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [68, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 0],
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__3_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        100, 101, 99, 108, 83, 105, 103, 87, 105, 116, 104, 73, 100, 0,
    ],
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__1_value
        ) as *mut leanh::LeanObject,
        300274991653824376 as *mut leanh::LeanObject,
    ],
};
static l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__2_value
        ) as *mut leanh::LeanObject,
        17585180993507524175 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__3_value
        ) as *mut leanh::LeanObject,
        17006199208638773373 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__5_value:
    leanh::LeanClosureObject<4> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__7_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_Command_declSig_formatter___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [102, 111, 114, 109, 97, 116, 116, 101, 114, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__1_value) as *mut leanh::LeanObject,300274991653824376 as *mut leanh::LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__2_value) as *mut leanh::LeanObject,17585180993507524175 as *mut leanh::LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__3_value) as *mut leanh::LeanObject,17006199208638773373 as *mut leanh::LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__0_value) as *mut leanh::LeanObject,9108602232725572544 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__0_value:
    leanh::LeanClosureObject<4> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_Command_declSig_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__1_value) as *mut leanh::LeanObject,300274991653824376 as *mut leanh::LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__2_value) as *mut leanh::LeanObject,17585180993507524175 as *mut leanh::LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__3_value) as *mut leanh::LeanObject,17006199208638773373 as *mut leanh::LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__0_value) as *mut leanh::LeanObject,12706624235358416028 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_PrettyPrinter_Delaborator_declSigWithId: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_139_ = l_Lean_Parser_maxPrec;
    v___x_140_ = leanh::lean_alloc_closure(
        l_Lean_Parser_termParser_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_140_, 0, v___x_139_);
    return v___x_140_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_142_ = l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__7;
    v___x_143_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__6_once
        ),
        _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__6,
    );
    v___x_144_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_144_, 0, v___x_143_);
    leanh::lean_closure_set(v___x_144_, 1, v___x_142_);
    return v___x_144_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_145_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__8_once
        ),
        _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__8,
    );
    v___x_146_ = leanh::lean_unsigned_to_nat(1024);
    v___x_147_ = l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4;
    v___x_148_ = leanh::lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_148_, 0, v___x_147_);
    leanh::lean_closure_set(v___x_148_, 1, v___x_146_);
    leanh::lean_closure_set(v___x_148_, 2, v___x_145_);
    return v___x_148_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter(
    mut v_a_149_: *mut leanh::LeanObject,
    mut v_a_150_: *mut leanh::LeanObject,
    mut v_a_151_: *mut leanh::LeanObject,
    mut v_a_152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_154_ = l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__5;
    v___x_155_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__9_once
        ),
        _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__9,
    );
    v___x_156_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_154_, v___x_155_, v_a_149_, v_a_150_, v_a_151_, v_a_152_,
    );
    return v___x_156_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___boxed(
    mut v_a_157_: *mut leanh::LeanObject,
    mut v_a_158_: *mut leanh::LeanObject,
    mut v_a_159_: *mut leanh::LeanObject,
    mut v_a_160_: *mut leanh::LeanObject,
    mut v_a_161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_162_ = l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter(
        v_a_157_, v_a_158_, v_a_159_, v_a_160_,
    );
    leanh::lean_dec(v_a_160_);
    leanh::lean_dec_ref(v_a_159_);
    leanh::lean_dec(v_a_158_);
    leanh::lean_dec_ref(v_a_157_);
    return v_res_162_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3()
-> *mut leanh::LeanObject {
    let mut v___x_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_171_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_172_ = l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4;
    v___x_173_ = l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1;
    v___x_174_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_175_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_171_, v___x_172_, v___x_173_, v___x_174_,
    );
    return v___x_175_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___boxed(
    mut v_a_176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_177_ = l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3();
    return v_res_177_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_185_ = l_Lean_Parser_maxPrec;
    v___x_186_ = leanh::lean_alloc_closure(
        l_Lean_Parser_termParser_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_186_, 0, v___x_185_);
    return v___x_186_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_188_ = l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__2;
    v___x_189_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__1_once
        ),
        _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__1,
    );
    v___x_190_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_190_, 0, v___x_189_);
    leanh::lean_closure_set(v___x_190_, 1, v___x_188_);
    return v___x_190_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_191_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__3_once
        ),
        _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__3,
    );
    v___x_192_ = leanh::lean_unsigned_to_nat(1024);
    v___x_193_ = l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4;
    v___x_194_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_194_, 0, v___x_193_);
    leanh::lean_closure_set(v___x_194_, 1, v___x_192_);
    leanh::lean_closure_set(v___x_194_, 2, v___x_191_);
    return v___x_194_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer(
    mut v_a_195_: *mut leanh::LeanObject,
    mut v_a_196_: *mut leanh::LeanObject,
    mut v_a_197_: *mut leanh::LeanObject,
    mut v_a_198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_200_ = l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__0;
    v___x_201_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__4_once
        ),
        _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__4,
    );
    v___x_202_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_200_, v___x_201_, v_a_195_, v_a_196_, v_a_197_, v_a_198_,
    );
    return v___x_202_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___boxed(
    mut v_a_203_: *mut leanh::LeanObject,
    mut v_a_204_: *mut leanh::LeanObject,
    mut v_a_205_: *mut leanh::LeanObject,
    mut v_a_206_: *mut leanh::LeanObject,
    mut v_a_207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_208_ = l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer(
        v_a_203_, v_a_204_, v_a_205_, v_a_206_,
    );
    leanh::lean_dec(v_a_206_);
    leanh::lean_dec_ref(v_a_205_);
    leanh::lean_dec(v_a_204_);
    leanh::lean_dec_ref(v_a_203_);
    return v_res_208_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7()
-> *mut leanh::LeanObject {
    let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_217_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_218_ = l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4;
    v___x_219_ = l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1;
    v___x_220_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_221_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_217_, v___x_218_, v___x_219_, v___x_220_,
    );
    return v___x_221_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___boxed(
    mut v_a_222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_223_ = l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7();
    return v_res_223_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_224_: u8 = 0;
    let mut v___x_225_: u8 = 0;
    let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_224_ = 0;
    v___x_225_ = 1;
    v___x_226_ = l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4;
    v___x_227_ = l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__3;
    v___x_228_ = l_Lean_Parser_mkAntiquot(v___x_227_, v___x_226_, v___x_225_, v___x_224_);
    return v___x_228_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_229_ = l_Lean_Parser_maxPrec;
    v___x_230_ = l_Lean_Parser_termParser(v___x_229_);
    return v___x_230_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_231_ = l_Lean_Parser_Command_declSig;
    v___x_232_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__1),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__1_once),
        _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__1,
    );
    v___x_233_ = l_Lean_Parser_andthen(v___x_232_, v___x_231_);
    return v___x_233_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_234_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__2),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__2_once),
        _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__2,
    );
    v___x_235_ = leanh::lean_unsigned_to_nat(1024);
    v___x_236_ = l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4;
    v___x_237_ = l_Lean_Parser_leadingNode(v___x_236_, v___x_235_, v___x_234_);
    return v___x_237_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_238_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__3),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__3_once),
        _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__3,
    );
    v___x_239_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__0),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__0_once),
        _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__0,
    );
    v___x_240_ = l_Lean_Parser_withAntiquot(v___x_239_, v___x_238_);
    return v___x_240_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_241_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__4),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__4_once),
        _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__4,
    );
    v___x_242_ = l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4;
    v___x_243_ = l_Lean_Parser_withCache(v___x_242_, v___x_241_);
    return v___x_243_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId() -> *mut leanh::LeanObject
{
    let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_244_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__5),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__5_once),
        _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__5,
    );
    return v___x_244_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_PrettyPrinter_Delaborator_DeclWithSig(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_PrettyPrinter_Delaborator_declSigWithId =
        _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId();
    leanh::lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_declSigWithId);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_PrettyPrinter_Delaborator_DeclWithSig(
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
pub unsafe fn initialize_Lean_PrettyPrinter_Delaborator_DeclWithSig(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_DeclWithSig(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_PrettyPrinter_Delaborator_DeclWithSig(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_PrettyPrinter_Delaborator_DeclWithSig(builtin);
}