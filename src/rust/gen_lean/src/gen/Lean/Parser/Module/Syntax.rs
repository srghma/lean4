// Lean compiler output
// Module: Lean.Parser.Module.Syntax
// Imports: Lean.Parser.Command
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Parser::Basic::{
    l_Lean_Parser_andthen, l_Lean_Parser_atomic, l_Lean_Parser_categoryParser,
    l_Lean_Parser_leadingNode, l_Lean_Parser_mkAntiquot, l_Lean_Parser_skip, l_Lean_Parser_symbol,
    l_Lean_Parser_withAntiquot,
};
use crate::r#gen::Lean::Parser::Command::{
    initialize_Lean_Parser_Command, runtime_initialize_Lean_Parser_Command,
};
use crate::r#gen::Lean::Parser::Extra::{
    l_Lean_Parser_atomic_formatter___boxed, l_Lean_Parser_commandParser_formatter___boxed,
    l_Lean_Parser_commandParser_parenthesizer___boxed, l_Lean_Parser_identWithPartialTrailingDot,
    l_Lean_Parser_identWithPartialTrailingDot_formatter___boxed,
    l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___boxed,
    l_Lean_Parser_leadingNode_formatter___boxed, l_Lean_Parser_many,
    l_Lean_Parser_many_formatter___boxed, l_Lean_Parser_many_parenthesizer___boxed,
    l_Lean_Parser_mkAntiquot_formatter___boxed, l_Lean_Parser_mkAntiquot_parenthesizer___boxed,
    l_Lean_Parser_optional, l_Lean_Parser_optional_formatter___boxed,
    l_Lean_Parser_optional_parenthesizer___boxed, l_Lean_Parser_ppLine_parenthesizer___boxed,
    l_Lean_Parser_symbol_formatter___boxed, l_Lean_Parser_symbol_parenthesizer___boxed,
    l_Lean_ppLine_formatter___boxed,
};
use crate::r#gen::Lean::Parser::Types::l_Lean_Parser_withCache;
use crate::r#gen::Lean::PrettyPrinter::Formatter::{
    l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_orelse_formatter, l_Lean_PrettyPrinter_formatterAttribute,
};
use crate::r#gen::Lean::PrettyPrinter::Parenthesizer::{
    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer,
    l_Lean_PrettyPrinter_parenthesizerAttribute,
};
pub static l_Lean_Parser_Module_moduleTk___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Parser_Module_moduleTk___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_moduleTk___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Parser_Module_moduleTk___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_moduleTk___closed__2_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [77, 111, 100, 117, 108, 101, 0],
    };
static mut l_Lean_Parser_Module_moduleTk___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_moduleTk___closed__3_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [109, 111, 100, 117, 108, 101, 84, 107, 0],
    };
static mut l_Lean_Parser_Module_moduleTk___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Module_moduleTk___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_moduleTk___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_moduleTk___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5561193377245250799 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Module_moduleTk___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__3_value)
                as *mut crate::leanh::LeanObject,
            15944969286361870278 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Module_moduleTk___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_moduleTk___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_moduleTk___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Module_moduleTk___closed__6_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [109, 111, 100, 117, 108, 101, 0],
    };
static mut l_Lean_Parser_Module_moduleTk___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_moduleTk___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_moduleTk___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_moduleTk___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_moduleTk___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_moduleTk___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_moduleTk___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_moduleTk___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_moduleTk___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Module_moduleTk: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Module_prelude___closed__0_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [112, 114, 101, 108, 117, 100, 101, 0],
    };
static mut l_Lean_Parser_Module_prelude___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Module_prelude___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_prelude___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_prelude___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5561193377245250799 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Module_prelude___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17898809269769340598 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Module_prelude___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_prelude___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_prelude___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_prelude___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_prelude___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_prelude___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_prelude___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_prelude___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_prelude___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_prelude___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_prelude___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Module_prelude: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Module_public___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [112, 117, 98, 108, 105, 99, 0],
    };
static mut l_Lean_Parser_Module_public___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Module_public___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_public___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_public___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5561193377245250799 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Module_public___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12460543829726897862 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Module_public___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_public___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_public___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_public___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_public___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_public___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_public___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_public___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_public___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_public___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_public___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Module_public: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Module_meta___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [109, 101, 116, 97, 0],
    };
static mut l_Lean_Parser_Module_meta___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Module_meta___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_meta___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_meta___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5561193377245250799 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Module_meta___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17003524124175295577 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Module_meta___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_meta___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_meta___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_meta___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_meta___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_meta___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_meta___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_meta___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_meta___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_meta___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_meta___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Module_meta: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Module_all___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [97, 108, 108, 0],
    };
static mut l_Lean_Parser_Module_all___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Module_all___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_all___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_all___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5561193377245250799 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Module_all___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9485984681193916779 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Module_all___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_all___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_all___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_all___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_all___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_all___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_all___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_all___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_all___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_all___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_all___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Module_all: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Module_import___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [105, 109, 112, 111, 114, 116, 0],
    };
static mut l_Lean_Parser_Module_import___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Module_import___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_import___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_import___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5561193377245250799 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Module_import___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3187861556840815537 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Module_import___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_import___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Module_import___closed__5_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [105, 109, 112, 111, 114, 116, 32, 0],
    };
static mut l_Lean_Parser_Module_import___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_import___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Module_import: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Module_header___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [104, 101, 97, 100, 101, 114, 0],
    };
static mut l_Lean_Parser_Module_header___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Module_header___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_header___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_header___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5561193377245250799 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Module_header___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14592748414440353064 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Module_header___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_header___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Module_header: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Module_moduleTk_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__4_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_moduleTk_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_moduleTk_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_moduleTk_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_moduleTk_formatter___closed__2_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__4_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_moduleTk_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [102, 111, 114, 109, 97, 116, 116, 101, 114, 0]};
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__3_value) as *mut crate::leanh::LeanObject,15944969286361870278 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value) as *mut crate::leanh::LeanObject,7218790382489784727 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_prelude_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_prelude_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_prelude_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_prelude_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_prelude_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_prelude_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_prelude_formatter___closed__2_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_prelude_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_prelude_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__0_value) as *mut crate::leanh::LeanObject,17898809269769340598 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value) as *mut crate::leanh::LeanObject,14630804532564755303 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_public_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_public_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_public_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_public_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_public_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_public_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_public_formatter___closed__2_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_public_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_public_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_public_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__0_value) as *mut crate::leanh::LeanObject,12460543829726897862 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value) as *mut crate::leanh::LeanObject,363164952207938711 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_meta_formatter___closed__0_value: crate::leanh::LeanClosureObject<
    4,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_meta_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_meta_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_meta_formatter___closed__1_value: crate::leanh::LeanClosureObject<
    1,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_meta_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_meta_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_meta_formatter___closed__2_value: crate::leanh::LeanClosureObject<
    3,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_meta_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_meta_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_meta_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__0_value) as *mut crate::leanh::LeanObject,17003524124175295577 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value) as *mut crate::leanh::LeanObject,10481679767173773492 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_all_formatter___closed__0_value: crate::leanh::LeanClosureObject<
    4,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_all_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_all_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_all_formatter___closed__1_value: crate::leanh::LeanClosureObject<
    1,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_all_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_all_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_all_formatter___closed__2_value: crate::leanh::LeanClosureObject<
    3,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_all_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_all_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_all_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__0_value) as *mut crate::leanh::LeanObject,9485984681193916779 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value) as *mut crate::leanh::LeanObject,4207927109047509902 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_import_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_import_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_import_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_import_formatter___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_formatter___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Module_import_formatter___closed__3_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_import_formatter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_import_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_import_formatter___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_formatter___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_formatter___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_formatter___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_formatter___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_formatter___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_formatter___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_formatter___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Module_import_formatter___closed__8_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_identWithPartialTrailingDot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Module_import_formatter___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_import_formatter___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_import_formatter___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_formatter___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_formatter___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_formatter___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_formatter___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_formatter___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__0_value) as *mut crate::leanh::LeanObject,3187861556840815537 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value) as *mut crate::leanh::LeanObject,7553579461518257660 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_header_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_header_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_header_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_header_formatter___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__0_value) as *mut crate::leanh::LeanObject,14592748414440353064 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value) as *mut crate::leanh::LeanObject,12937101448938299577 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Module_module_formatter___closed__0_value_aux_0: crate::leanh::LeanCtorObject<
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Module_module_formatter___closed__0_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Module_module_formatter___closed__0_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Module_module_formatter___closed__0_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Module_module_formatter___closed__0_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value)
            as *mut crate::leanh::LeanObject,
        5561193377245250799 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Module_module_formatter___closed__0_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Module_module_formatter___closed__0_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__6_value)
            as *mut crate::leanh::LeanObject,
        713060080782592827 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_module_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_module_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_module_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_module_formatter___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_module_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_module_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_module_formatter___closed__2_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_commandParser_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Parser_Module_module_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_module_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_module_formatter___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module_formatter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module_formatter___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module_formatter___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module_formatter___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module_formatter___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module_formatter___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module_formatter___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__6_value) as *mut crate::leanh::LeanObject,713060080782592827 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value) as *mut crate::leanh::LeanObject,17424960447186865918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__4_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_moduleTk_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_moduleTk_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_moduleTk_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__4_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_moduleTk_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 0]};
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__3_value) as *mut crate::leanh::LeanObject,15944969286361870278 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value) as *mut crate::leanh::LeanObject,7990296077579416291 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_prelude_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_prelude_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_prelude_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_prelude_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_prelude_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_prelude_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_prelude_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_prelude_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_prelude_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__0_value) as *mut crate::leanh::LeanObject,17898809269769340598 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value) as *mut crate::leanh::LeanObject,17284225932489850483 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_public_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_public_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_public_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_public_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_public_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_public_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_public_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_public_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_public_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_public_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__0_value) as *mut crate::leanh::LeanObject,12460543829726897862 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value) as *mut crate::leanh::LeanObject,16358965941833244643 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_meta_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_meta_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_meta_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_meta_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_meta_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_meta_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_meta_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_meta_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_meta_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_meta_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__0_value) as *mut crate::leanh::LeanObject,17003524124175295577 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value) as *mut crate::leanh::LeanObject,1130732432433876904 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_all_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_all_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_all_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_all_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_all_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_all_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_all_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_all_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_all_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_all_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__0_value) as *mut crate::leanh::LeanObject,9485984681193916779 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value) as *mut crate::leanh::LeanObject,12412954514720509378 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_import_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_import_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_import_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_import_parenthesizer___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_parenthesizer___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Module_import_parenthesizer___closed__3_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_import_parenthesizer___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_import_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_import_parenthesizer___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_parenthesizer___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_parenthesizer___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_parenthesizer___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_parenthesizer___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_parenthesizer___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Module_import_parenthesizer___closed__7_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Module_import_parenthesizer___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_import_parenthesizer___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_import_parenthesizer___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_parenthesizer___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_parenthesizer___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_parenthesizer___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_parenthesizer___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_parenthesizer___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__0_value) as *mut crate::leanh::LeanObject,3187861556840815537 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value) as *mut crate::leanh::LeanObject,11177889036445469280 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_header_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_header_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_header_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_header_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_ppLine_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Module_header_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_header_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_header_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_header_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_header_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_header_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_header_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_header_parenthesizer___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_parenthesizer___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_parenthesizer___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_parenthesizer___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_parenthesizer___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_parenthesizer___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_parenthesizer___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_parenthesizer___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_parenthesizer___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_parenthesizer___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__0_value) as *mut crate::leanh::LeanObject,14592748414440353064 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value) as *mut crate::leanh::LeanObject,5268993740040961389 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_module_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_module_formatter___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_module_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_module_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_module_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_commandParser_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Parser_Module_module_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_module_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_module_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_module_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_header_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_module_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_module_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_module_parenthesizer___closed__3_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_many_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_module_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_module_parenthesizer___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_module_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_module_parenthesizer___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module_parenthesizer___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module_parenthesizer___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module_parenthesizer___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__6_value) as *mut crate::leanh::LeanObject,713060080782592827 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value) as *mut crate::leanh::LeanObject,17272583890648199090 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_module___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Module_module___closed__1_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [99, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lean_Parser_Module_module___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_module___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_module___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Module_module___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5063646790596052253 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Module_module___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_module___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_module___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Module_module: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Parser_Module_moduleTk___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1032_: u8 = 0;
    let mut v___x_1033_: u8 = 0;
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1032_ = 0;
    v___x_1033_ = 1;
    v___x_1034_ = l_Lean_Parser_Module_moduleTk___closed__4;
    v___x_1035_ = l_Lean_Parser_Module_moduleTk___closed__3;
    v___x_1036_ = l_Lean_Parser_mkAntiquot(v___x_1035_, v___x_1034_, v___x_1033_, v___x_1032_);
    return v___x_1036_;
}
pub unsafe fn _init_l_Lean_Parser_Module_moduleTk___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1038_ = l_Lean_Parser_Module_moduleTk___closed__6;
    v___x_1039_ = l_Lean_Parser_symbol(v___x_1038_);
    return v___x_1039_;
}
pub unsafe fn _init_l_Lean_Parser_Module_moduleTk___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1040_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__7_once),
        _init_l_Lean_Parser_Module_moduleTk___closed__7,
    );
    v___x_1041_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_1042_ = l_Lean_Parser_Module_moduleTk___closed__4;
    v___x_1043_ = l_Lean_Parser_leadingNode(v___x_1042_, v___x_1041_, v___x_1040_);
    return v___x_1043_;
}
pub unsafe fn _init_l_Lean_Parser_Module_moduleTk___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1044_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__8_once),
        _init_l_Lean_Parser_Module_moduleTk___closed__8,
    );
    v___x_1045_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__5_once),
        _init_l_Lean_Parser_Module_moduleTk___closed__5,
    );
    v___x_1046_ = l_Lean_Parser_withAntiquot(v___x_1045_, v___x_1044_);
    return v___x_1046_;
}
pub unsafe fn _init_l_Lean_Parser_Module_moduleTk___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1047_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__9_once),
        _init_l_Lean_Parser_Module_moduleTk___closed__9,
    );
    v___x_1048_ = l_Lean_Parser_Module_moduleTk___closed__4;
    v___x_1049_ = l_Lean_Parser_withCache(v___x_1048_, v___x_1047_);
    return v___x_1049_;
}
pub unsafe fn _init_l_Lean_Parser_Module_moduleTk() -> *mut crate::leanh::LeanObject {
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1050_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__10_once),
        _init_l_Lean_Parser_Module_moduleTk___closed__10,
    );
    return v___x_1050_;
}
pub unsafe fn _init_l_Lean_Parser_Module_prelude___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1057_: u8 = 0;
    let mut v___x_1058_: u8 = 0;
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1057_ = 0;
    v___x_1058_ = 1;
    v___x_1059_ = l_Lean_Parser_Module_prelude___closed__1;
    v___x_1060_ = l_Lean_Parser_Module_prelude___closed__0;
    v___x_1061_ = l_Lean_Parser_mkAntiquot(v___x_1060_, v___x_1059_, v___x_1058_, v___x_1057_);
    return v___x_1061_;
}
pub unsafe fn _init_l_Lean_Parser_Module_prelude___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1062_ = l_Lean_Parser_Module_prelude___closed__0;
    v___x_1063_ = l_Lean_Parser_symbol(v___x_1062_);
    return v___x_1063_;
}
pub unsafe fn _init_l_Lean_Parser_Module_prelude___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__3_once),
        _init_l_Lean_Parser_Module_prelude___closed__3,
    );
    v___x_1065_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_1066_ = l_Lean_Parser_Module_prelude___closed__1;
    v___x_1067_ = l_Lean_Parser_leadingNode(v___x_1066_, v___x_1065_, v___x_1064_);
    return v___x_1067_;
}
pub unsafe fn _init_l_Lean_Parser_Module_prelude___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1068_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__4_once),
        _init_l_Lean_Parser_Module_prelude___closed__4,
    );
    v___x_1069_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__2_once),
        _init_l_Lean_Parser_Module_prelude___closed__2,
    );
    v___x_1070_ = l_Lean_Parser_withAntiquot(v___x_1069_, v___x_1068_);
    return v___x_1070_;
}
pub unsafe fn _init_l_Lean_Parser_Module_prelude___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1071_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__5_once),
        _init_l_Lean_Parser_Module_prelude___closed__5,
    );
    v___x_1072_ = l_Lean_Parser_Module_prelude___closed__1;
    v___x_1073_ = l_Lean_Parser_withCache(v___x_1072_, v___x_1071_);
    return v___x_1073_;
}
pub unsafe fn _init_l_Lean_Parser_Module_prelude() -> *mut crate::leanh::LeanObject {
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1074_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__6_once),
        _init_l_Lean_Parser_Module_prelude___closed__6,
    );
    return v___x_1074_;
}
pub unsafe fn _init_l_Lean_Parser_Module_public___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1081_: u8 = 0;
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1081_ = 0;
    v___x_1082_ = l_Lean_Parser_Module_public___closed__1;
    v___x_1083_ = l_Lean_Parser_Module_public___closed__0;
    v___x_1084_ = l_Lean_Parser_mkAntiquot(v___x_1083_, v___x_1082_, v___x_1081_, v___x_1081_);
    return v___x_1084_;
}
pub unsafe fn _init_l_Lean_Parser_Module_public___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1085_ = l_Lean_Parser_Module_public___closed__0;
    v___x_1086_ = l_Lean_Parser_symbol(v___x_1085_);
    return v___x_1086_;
}
pub unsafe fn _init_l_Lean_Parser_Module_public___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1087_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__3_once),
        _init_l_Lean_Parser_Module_public___closed__3,
    );
    v___x_1088_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_1089_ = l_Lean_Parser_Module_public___closed__1;
    v___x_1090_ = l_Lean_Parser_leadingNode(v___x_1089_, v___x_1088_, v___x_1087_);
    return v___x_1090_;
}
pub unsafe fn _init_l_Lean_Parser_Module_public___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1091_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__4_once),
        _init_l_Lean_Parser_Module_public___closed__4,
    );
    v___x_1092_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__2_once),
        _init_l_Lean_Parser_Module_public___closed__2,
    );
    v___x_1093_ = l_Lean_Parser_withAntiquot(v___x_1092_, v___x_1091_);
    return v___x_1093_;
}
pub unsafe fn _init_l_Lean_Parser_Module_public___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1094_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__5_once),
        _init_l_Lean_Parser_Module_public___closed__5,
    );
    v___x_1095_ = l_Lean_Parser_Module_public___closed__1;
    v___x_1096_ = l_Lean_Parser_withCache(v___x_1095_, v___x_1094_);
    return v___x_1096_;
}
pub unsafe fn _init_l_Lean_Parser_Module_public() -> *mut crate::leanh::LeanObject {
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1097_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__6_once),
        _init_l_Lean_Parser_Module_public___closed__6,
    );
    return v___x_1097_;
}
pub unsafe fn _init_l_Lean_Parser_Module_meta___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1104_: u8 = 0;
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1104_ = 0;
    v___x_1105_ = l_Lean_Parser_Module_meta___closed__1;
    v___x_1106_ = l_Lean_Parser_Module_meta___closed__0;
    v___x_1107_ = l_Lean_Parser_mkAntiquot(v___x_1106_, v___x_1105_, v___x_1104_, v___x_1104_);
    return v___x_1107_;
}
pub unsafe fn _init_l_Lean_Parser_Module_meta___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1108_ = l_Lean_Parser_Module_meta___closed__0;
    v___x_1109_ = l_Lean_Parser_symbol(v___x_1108_);
    return v___x_1109_;
}
pub unsafe fn _init_l_Lean_Parser_Module_meta___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__3_once),
        _init_l_Lean_Parser_Module_meta___closed__3,
    );
    v___x_1111_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_1112_ = l_Lean_Parser_Module_meta___closed__1;
    v___x_1113_ = l_Lean_Parser_leadingNode(v___x_1112_, v___x_1111_, v___x_1110_);
    return v___x_1113_;
}
pub unsafe fn _init_l_Lean_Parser_Module_meta___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1114_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__4_once),
        _init_l_Lean_Parser_Module_meta___closed__4,
    );
    v___x_1115_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__2_once),
        _init_l_Lean_Parser_Module_meta___closed__2,
    );
    v___x_1116_ = l_Lean_Parser_withAntiquot(v___x_1115_, v___x_1114_);
    return v___x_1116_;
}
pub unsafe fn _init_l_Lean_Parser_Module_meta___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1117_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__5_once),
        _init_l_Lean_Parser_Module_meta___closed__5,
    );
    v___x_1118_ = l_Lean_Parser_Module_meta___closed__1;
    v___x_1119_ = l_Lean_Parser_withCache(v___x_1118_, v___x_1117_);
    return v___x_1119_;
}
pub unsafe fn _init_l_Lean_Parser_Module_meta() -> *mut crate::leanh::LeanObject {
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1120_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__6_once),
        _init_l_Lean_Parser_Module_meta___closed__6,
    );
    return v___x_1120_;
}
pub unsafe fn _init_l_Lean_Parser_Module_all___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1127_: u8 = 0;
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1127_ = 0;
    v___x_1128_ = l_Lean_Parser_Module_all___closed__1;
    v___x_1129_ = l_Lean_Parser_Module_all___closed__0;
    v___x_1130_ = l_Lean_Parser_mkAntiquot(v___x_1129_, v___x_1128_, v___x_1127_, v___x_1127_);
    return v___x_1130_;
}
pub unsafe fn _init_l_Lean_Parser_Module_all___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1131_ = l_Lean_Parser_Module_all___closed__0;
    v___x_1132_ = l_Lean_Parser_symbol(v___x_1131_);
    return v___x_1132_;
}
pub unsafe fn _init_l_Lean_Parser_Module_all___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1133_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__3_once),
        _init_l_Lean_Parser_Module_all___closed__3,
    );
    v___x_1134_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_1135_ = l_Lean_Parser_Module_all___closed__1;
    v___x_1136_ = l_Lean_Parser_leadingNode(v___x_1135_, v___x_1134_, v___x_1133_);
    return v___x_1136_;
}
pub unsafe fn _init_l_Lean_Parser_Module_all___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1137_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__4_once),
        _init_l_Lean_Parser_Module_all___closed__4,
    );
    v___x_1138_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__2_once),
        _init_l_Lean_Parser_Module_all___closed__2,
    );
    v___x_1139_ = l_Lean_Parser_withAntiquot(v___x_1138_, v___x_1137_);
    return v___x_1139_;
}
pub unsafe fn _init_l_Lean_Parser_Module_all___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1140_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__5_once),
        _init_l_Lean_Parser_Module_all___closed__5,
    );
    v___x_1141_ = l_Lean_Parser_Module_all___closed__1;
    v___x_1142_ = l_Lean_Parser_withCache(v___x_1141_, v___x_1140_);
    return v___x_1142_;
}
pub unsafe fn _init_l_Lean_Parser_Module_all() -> *mut crate::leanh::LeanObject {
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1143_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__6_once),
        _init_l_Lean_Parser_Module_all___closed__6,
    );
    return v___x_1143_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1150_: u8 = 0;
    let mut v___x_1151_: u8 = 0;
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1150_ = 0;
    v___x_1151_ = 1;
    v___x_1152_ = l_Lean_Parser_Module_import___closed__1;
    v___x_1153_ = l_Lean_Parser_Module_import___closed__0;
    v___x_1154_ = l_Lean_Parser_mkAntiquot(v___x_1153_, v___x_1152_, v___x_1151_, v___x_1150_);
    return v___x_1154_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1155_ = l_Lean_Parser_Module_public;
    v___x_1156_ = l_Lean_Parser_optional(v___x_1155_);
    return v___x_1156_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1157_ = l_Lean_Parser_Module_meta;
    v___x_1158_ = l_Lean_Parser_optional(v___x_1157_);
    return v___x_1158_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1160_ = l_Lean_Parser_Module_import___closed__5;
    v___x_1161_ = l_Lean_Parser_symbol(v___x_1160_);
    return v___x_1161_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1162_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__6_once),
        _init_l_Lean_Parser_Module_import___closed__6,
    );
    v___x_1163_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__4_once),
        _init_l_Lean_Parser_Module_import___closed__4,
    );
    v___x_1164_ = l_Lean_Parser_andthen(v___x_1163_, v___x_1162_);
    return v___x_1164_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1165_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__7_once),
        _init_l_Lean_Parser_Module_import___closed__7,
    );
    v___x_1166_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__3_once),
        _init_l_Lean_Parser_Module_import___closed__3,
    );
    v___x_1167_ = l_Lean_Parser_andthen(v___x_1166_, v___x_1165_);
    return v___x_1167_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1168_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__8_once),
        _init_l_Lean_Parser_Module_import___closed__8,
    );
    v___x_1169_ = l_Lean_Parser_atomic(v___x_1168_);
    return v___x_1169_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1170_ = l_Lean_Parser_Module_all;
    v___x_1171_ = l_Lean_Parser_optional(v___x_1170_);
    return v___x_1171_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1172_ = l_Lean_Parser_identWithPartialTrailingDot;
    v___x_1173_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__10_once),
        _init_l_Lean_Parser_Module_import___closed__10,
    );
    v___x_1174_ = l_Lean_Parser_andthen(v___x_1173_, v___x_1172_);
    return v___x_1174_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1175_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__11_once),
        _init_l_Lean_Parser_Module_import___closed__11,
    );
    v___x_1176_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__9_once),
        _init_l_Lean_Parser_Module_import___closed__9,
    );
    v___x_1177_ = l_Lean_Parser_andthen(v___x_1176_, v___x_1175_);
    return v___x_1177_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1178_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__12_once),
        _init_l_Lean_Parser_Module_import___closed__12,
    );
    v___x_1179_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_1180_ = l_Lean_Parser_Module_import___closed__1;
    v___x_1181_ = l_Lean_Parser_leadingNode(v___x_1180_, v___x_1179_, v___x_1178_);
    return v___x_1181_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__14() -> *mut crate::leanh::LeanObject {
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__13_once),
        _init_l_Lean_Parser_Module_import___closed__13,
    );
    v___x_1183_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__2_once),
        _init_l_Lean_Parser_Module_import___closed__2,
    );
    v___x_1184_ = l_Lean_Parser_withAntiquot(v___x_1183_, v___x_1182_);
    return v___x_1184_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1185_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__14_once),
        _init_l_Lean_Parser_Module_import___closed__14,
    );
    v___x_1186_ = l_Lean_Parser_Module_import___closed__1;
    v___x_1187_ = l_Lean_Parser_withCache(v___x_1186_, v___x_1185_);
    return v___x_1187_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import() -> *mut crate::leanh::LeanObject {
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1188_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__15_once),
        _init_l_Lean_Parser_Module_import___closed__15,
    );
    return v___x_1188_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1195_: u8 = 0;
    let mut v___x_1196_: u8 = 0;
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1195_ = 0;
    v___x_1196_ = 1;
    v___x_1197_ = l_Lean_Parser_Module_header___closed__1;
    v___x_1198_ = l_Lean_Parser_Module_header___closed__0;
    v___x_1199_ = l_Lean_Parser_mkAntiquot(v___x_1198_, v___x_1197_, v___x_1196_, v___x_1195_);
    return v___x_1199_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1200_ = l_Lean_Parser_skip;
    v___x_1201_ = l_Lean_Parser_andthen(v___x_1200_, v___x_1200_);
    return v___x_1201_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1202_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__3_once),
        _init_l_Lean_Parser_Module_header___closed__3,
    );
    v___x_1203_ = l_Lean_Parser_Module_moduleTk;
    v___x_1204_ = l_Lean_Parser_andthen(v___x_1203_, v___x_1202_);
    return v___x_1204_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1205_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__4_once),
        _init_l_Lean_Parser_Module_header___closed__4,
    );
    v___x_1206_ = l_Lean_Parser_optional(v___x_1205_);
    return v___x_1206_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1207_ = l_Lean_Parser_skip;
    v___x_1208_ = l_Lean_Parser_Module_prelude;
    v___x_1209_ = l_Lean_Parser_andthen(v___x_1208_, v___x_1207_);
    return v___x_1209_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1210_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__6_once),
        _init_l_Lean_Parser_Module_header___closed__6,
    );
    v___x_1211_ = l_Lean_Parser_optional(v___x_1210_);
    return v___x_1211_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1212_ = l_Lean_Parser_skip;
    v___x_1213_ = l_Lean_Parser_Module_import;
    v___x_1214_ = l_Lean_Parser_andthen(v___x_1213_, v___x_1212_);
    return v___x_1214_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1215_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__8_once),
        _init_l_Lean_Parser_Module_header___closed__8,
    );
    v___x_1216_ = l_Lean_Parser_many(v___x_1215_);
    return v___x_1216_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1217_ = l_Lean_Parser_skip;
    v___x_1218_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__9_once),
        _init_l_Lean_Parser_Module_header___closed__9,
    );
    v___x_1219_ = l_Lean_Parser_andthen(v___x_1218_, v___x_1217_);
    return v___x_1219_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1220_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__10_once),
        _init_l_Lean_Parser_Module_header___closed__10,
    );
    v___x_1221_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__7_once),
        _init_l_Lean_Parser_Module_header___closed__7,
    );
    v___x_1222_ = l_Lean_Parser_andthen(v___x_1221_, v___x_1220_);
    return v___x_1222_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1223_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__11_once),
        _init_l_Lean_Parser_Module_header___closed__11,
    );
    v___x_1224_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__5_once),
        _init_l_Lean_Parser_Module_header___closed__5,
    );
    v___x_1225_ = l_Lean_Parser_andthen(v___x_1224_, v___x_1223_);
    return v___x_1225_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1226_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__12_once),
        _init_l_Lean_Parser_Module_header___closed__12,
    );
    v___x_1227_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_1228_ = l_Lean_Parser_Module_header___closed__1;
    v___x_1229_ = l_Lean_Parser_leadingNode(v___x_1228_, v___x_1227_, v___x_1226_);
    return v___x_1229_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__14() -> *mut crate::leanh::LeanObject {
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1230_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__13_once),
        _init_l_Lean_Parser_Module_header___closed__13,
    );
    v___x_1231_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__2_once),
        _init_l_Lean_Parser_Module_header___closed__2,
    );
    v___x_1232_ = l_Lean_Parser_withAntiquot(v___x_1231_, v___x_1230_);
    return v___x_1232_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1233_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__14_once),
        _init_l_Lean_Parser_Module_header___closed__14,
    );
    v___x_1234_ = l_Lean_Parser_Module_header___closed__1;
    v___x_1235_ = l_Lean_Parser_withCache(v___x_1234_, v___x_1233_);
    return v___x_1235_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header() -> *mut crate::leanh::LeanObject {
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1236_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__15_once),
        _init_l_Lean_Parser_Module_header___closed__15,
    );
    return v___x_1236_;
}
pub unsafe fn l_Lean_Parser_Module_moduleTk_formatter(
    mut v_a_1250_: *mut crate::leanh::LeanObject,
    mut v_a_1251_: *mut crate::leanh::LeanObject,
    mut v_a_1252_: *mut crate::leanh::LeanObject,
    mut v_a_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1255_ = l_Lean_Parser_Module_moduleTk_formatter___closed__0;
    v___x_1256_ = l_Lean_Parser_Module_moduleTk_formatter___closed__2;
    v___x_1257_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_1255_,
        v___x_1256_,
        v_a_1250_,
        v_a_1251_,
        v_a_1252_,
        v_a_1253_,
    );
    return v___x_1257_;
}
pub unsafe fn l_Lean_Parser_Module_moduleTk_formatter___boxed(
    mut v_a_1258_: *mut crate::leanh::LeanObject,
    mut v_a_1259_: *mut crate::leanh::LeanObject,
    mut v_a_1260_: *mut crate::leanh::LeanObject,
    mut v_a_1261_: *mut crate::leanh::LeanObject,
    mut v_a_1262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1263_ =
        l_Lean_Parser_Module_moduleTk_formatter(v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
    crate::leanh::lean_dec(v_a_1261_);
    crate::leanh::lean_dec_ref(v_a_1260_);
    crate::leanh::lean_dec(v_a_1259_);
    crate::leanh::lean_dec_ref(v_a_1258_);
    return v_res_1263_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1272_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1273_ = l_Lean_Parser_Module_moduleTk___closed__4;
    v___x_1274_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1;
    v___x_1275_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_moduleTk_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1276_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1272_,
        v___x_1273_,
        v___x_1274_,
        v___x_1275_,
    );
    return v___x_1276_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___boxed(
    mut v_a_1277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1278_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3();
    return v_res_1278_;
}
pub unsafe fn l_Lean_Parser_Module_prelude_formatter(
    mut v_a_1292_: *mut crate::leanh::LeanObject,
    mut v_a_1293_: *mut crate::leanh::LeanObject,
    mut v_a_1294_: *mut crate::leanh::LeanObject,
    mut v_a_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1297_ = l_Lean_Parser_Module_prelude_formatter___closed__0;
    v___x_1298_ = l_Lean_Parser_Module_prelude_formatter___closed__2;
    v___x_1299_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_1297_,
        v___x_1298_,
        v_a_1292_,
        v_a_1293_,
        v_a_1294_,
        v_a_1295_,
    );
    return v___x_1299_;
}
pub unsafe fn l_Lean_Parser_Module_prelude_formatter___boxed(
    mut v_a_1300_: *mut crate::leanh::LeanObject,
    mut v_a_1301_: *mut crate::leanh::LeanObject,
    mut v_a_1302_: *mut crate::leanh::LeanObject,
    mut v_a_1303_: *mut crate::leanh::LeanObject,
    mut v_a_1304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1305_ =
        l_Lean_Parser_Module_prelude_formatter(v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
    crate::leanh::lean_dec(v_a_1303_);
    crate::leanh::lean_dec_ref(v_a_1302_);
    crate::leanh::lean_dec(v_a_1301_);
    crate::leanh::lean_dec_ref(v_a_1300_);
    return v_res_1305_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1313_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1314_ = l_Lean_Parser_Module_prelude___closed__1;
    v___x_1315_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0;
    v___x_1316_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_prelude_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1317_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1313_,
        v___x_1314_,
        v___x_1315_,
        v___x_1316_,
    );
    return v___x_1317_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___boxed(
    mut v_a_1318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1319_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7();
    return v_res_1319_;
}
pub unsafe fn l_Lean_Parser_Module_public_formatter(
    mut v_a_1332_: *mut crate::leanh::LeanObject,
    mut v_a_1333_: *mut crate::leanh::LeanObject,
    mut v_a_1334_: *mut crate::leanh::LeanObject,
    mut v_a_1335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1337_ = l_Lean_Parser_Module_public_formatter___closed__0;
    v___x_1338_ = l_Lean_Parser_Module_public_formatter___closed__2;
    v___x_1339_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_1337_,
        v___x_1338_,
        v_a_1332_,
        v_a_1333_,
        v_a_1334_,
        v_a_1335_,
    );
    return v___x_1339_;
}
pub unsafe fn l_Lean_Parser_Module_public_formatter___boxed(
    mut v_a_1340_: *mut crate::leanh::LeanObject,
    mut v_a_1341_: *mut crate::leanh::LeanObject,
    mut v_a_1342_: *mut crate::leanh::LeanObject,
    mut v_a_1343_: *mut crate::leanh::LeanObject,
    mut v_a_1344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1345_ = l_Lean_Parser_Module_public_formatter(v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_);
    crate::leanh::lean_dec(v_a_1343_);
    crate::leanh::lean_dec_ref(v_a_1342_);
    crate::leanh::lean_dec(v_a_1341_);
    crate::leanh::lean_dec_ref(v_a_1340_);
    return v_res_1345_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1353_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1354_ = l_Lean_Parser_Module_public___closed__1;
    v___x_1355_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0;
    v___x_1356_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_public_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1357_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1353_,
        v___x_1354_,
        v___x_1355_,
        v___x_1356_,
    );
    return v___x_1357_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___boxed(
    mut v_a_1358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1359_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11();
    return v_res_1359_;
}
pub unsafe fn l_Lean_Parser_Module_meta_formatter(
    mut v_a_1372_: *mut crate::leanh::LeanObject,
    mut v_a_1373_: *mut crate::leanh::LeanObject,
    mut v_a_1374_: *mut crate::leanh::LeanObject,
    mut v_a_1375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1377_ = l_Lean_Parser_Module_meta_formatter___closed__0;
    v___x_1378_ = l_Lean_Parser_Module_meta_formatter___closed__2;
    v___x_1379_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_1377_,
        v___x_1378_,
        v_a_1372_,
        v_a_1373_,
        v_a_1374_,
        v_a_1375_,
    );
    return v___x_1379_;
}
pub unsafe fn l_Lean_Parser_Module_meta_formatter___boxed(
    mut v_a_1380_: *mut crate::leanh::LeanObject,
    mut v_a_1381_: *mut crate::leanh::LeanObject,
    mut v_a_1382_: *mut crate::leanh::LeanObject,
    mut v_a_1383_: *mut crate::leanh::LeanObject,
    mut v_a_1384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1385_ = l_Lean_Parser_Module_meta_formatter(v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
    crate::leanh::lean_dec(v_a_1383_);
    crate::leanh::lean_dec_ref(v_a_1382_);
    crate::leanh::lean_dec(v_a_1381_);
    crate::leanh::lean_dec_ref(v_a_1380_);
    return v_res_1385_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1393_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1394_ = l_Lean_Parser_Module_meta___closed__1;
    v___x_1395_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0;
    v___x_1396_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_meta_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1397_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1393_,
        v___x_1394_,
        v___x_1395_,
        v___x_1396_,
    );
    return v___x_1397_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___boxed(
    mut v_a_1398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1399_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15();
    return v_res_1399_;
}
pub unsafe fn l_Lean_Parser_Module_all_formatter(
    mut v_a_1412_: *mut crate::leanh::LeanObject,
    mut v_a_1413_: *mut crate::leanh::LeanObject,
    mut v_a_1414_: *mut crate::leanh::LeanObject,
    mut v_a_1415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1417_ = l_Lean_Parser_Module_all_formatter___closed__0;
    v___x_1418_ = l_Lean_Parser_Module_all_formatter___closed__2;
    v___x_1419_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_1417_,
        v___x_1418_,
        v_a_1412_,
        v_a_1413_,
        v_a_1414_,
        v_a_1415_,
    );
    return v___x_1419_;
}
pub unsafe fn l_Lean_Parser_Module_all_formatter___boxed(
    mut v_a_1420_: *mut crate::leanh::LeanObject,
    mut v_a_1421_: *mut crate::leanh::LeanObject,
    mut v_a_1422_: *mut crate::leanh::LeanObject,
    mut v_a_1423_: *mut crate::leanh::LeanObject,
    mut v_a_1424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1425_ = l_Lean_Parser_Module_all_formatter(v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
    crate::leanh::lean_dec(v_a_1423_);
    crate::leanh::lean_dec_ref(v_a_1422_);
    crate::leanh::lean_dec(v_a_1421_);
    crate::leanh::lean_dec_ref(v_a_1420_);
    return v_res_1425_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1434_ = l_Lean_Parser_Module_all___closed__1;
    v___x_1435_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0;
    v___x_1436_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_all_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1437_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1433_,
        v___x_1434_,
        v___x_1435_,
        v___x_1436_,
    );
    return v___x_1437_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___boxed(
    mut v_a_1438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1439_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19();
    return v_res_1439_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_formatter___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1447_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_public_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1448_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_optional_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1448_, 0, v___x_1447_);
    return v___x_1448_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_formatter___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1449_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_meta_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1450_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_optional_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1450_, 0, v___x_1449_);
    return v___x_1450_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_formatter___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1453_ = l_Lean_Parser_Module_import_formatter___closed__3;
    v___x_1454_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__2_once),
        _init_l_Lean_Parser_Module_import_formatter___closed__2,
    );
    v___x_1455_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1455_, 0, v___x_1454_);
    crate::leanh::lean_closure_set(v___x_1455_, 1, v___x_1453_);
    return v___x_1455_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_formatter___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1456_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__4_once),
        _init_l_Lean_Parser_Module_import_formatter___closed__4,
    );
    v___x_1457_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__1_once),
        _init_l_Lean_Parser_Module_import_formatter___closed__1,
    );
    v___x_1458_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1458_, 0, v___x_1457_);
    crate::leanh::lean_closure_set(v___x_1458_, 1, v___x_1456_);
    return v___x_1458_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_formatter___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1459_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__5_once),
        _init_l_Lean_Parser_Module_import_formatter___closed__5,
    );
    v___x_1460_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_atomic_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1460_, 0, v___x_1459_);
    return v___x_1460_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_formatter___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1461_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_all_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1462_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_optional_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1462_, 0, v___x_1461_);
    return v___x_1462_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_formatter___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1464_ = l_Lean_Parser_Module_import_formatter___closed__8;
    v___x_1465_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__7_once),
        _init_l_Lean_Parser_Module_import_formatter___closed__7,
    );
    v___x_1466_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1466_, 0, v___x_1465_);
    crate::leanh::lean_closure_set(v___x_1466_, 1, v___x_1464_);
    return v___x_1466_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_formatter___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1467_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__9_once),
        _init_l_Lean_Parser_Module_import_formatter___closed__9,
    );
    v___x_1468_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__6_once),
        _init_l_Lean_Parser_Module_import_formatter___closed__6,
    );
    v___x_1469_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1469_, 0, v___x_1468_);
    crate::leanh::lean_closure_set(v___x_1469_, 1, v___x_1467_);
    return v___x_1469_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_formatter___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1470_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__10_once),
        _init_l_Lean_Parser_Module_import_formatter___closed__10,
    );
    v___x_1471_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_1472_ = l_Lean_Parser_Module_import___closed__1;
    v___x_1473_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_1473_, 0, v___x_1472_);
    crate::leanh::lean_closure_set(v___x_1473_, 1, v___x_1471_);
    crate::leanh::lean_closure_set(v___x_1473_, 2, v___x_1470_);
    return v___x_1473_;
}
pub unsafe fn l_Lean_Parser_Module_import_formatter(
    mut v_a_1474_: *mut crate::leanh::LeanObject,
    mut v_a_1475_: *mut crate::leanh::LeanObject,
    mut v_a_1476_: *mut crate::leanh::LeanObject,
    mut v_a_1477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1479_ = l_Lean_Parser_Module_import_formatter___closed__0;
    v___x_1480_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__11_once),
        _init_l_Lean_Parser_Module_import_formatter___closed__11,
    );
    v___x_1481_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_1479_,
        v___x_1480_,
        v_a_1474_,
        v_a_1475_,
        v_a_1476_,
        v_a_1477_,
    );
    return v___x_1481_;
}
pub unsafe fn l_Lean_Parser_Module_import_formatter___boxed(
    mut v_a_1482_: *mut crate::leanh::LeanObject,
    mut v_a_1483_: *mut crate::leanh::LeanObject,
    mut v_a_1484_: *mut crate::leanh::LeanObject,
    mut v_a_1485_: *mut crate::leanh::LeanObject,
    mut v_a_1486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1487_ = l_Lean_Parser_Module_import_formatter(v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
    crate::leanh::lean_dec(v_a_1485_);
    crate::leanh::lean_dec_ref(v_a_1484_);
    crate::leanh::lean_dec(v_a_1483_);
    crate::leanh::lean_dec_ref(v_a_1482_);
    return v_res_1487_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1495_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1496_ = l_Lean_Parser_Module_import___closed__1;
    v___x_1497_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0;
    v___x_1498_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_import_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1499_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1495_,
        v___x_1496_,
        v___x_1497_,
        v___x_1498_,
    );
    return v___x_1499_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___boxed(
    mut v_a_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1501_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23();
    return v_res_1501_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1509_ = crate::leanh::lean_alloc_closure(
        l_Lean_ppLine_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    crate::leanh::lean_inc_ref(v___x_1509_);
    v___x_1510_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1510_, 0, v___x_1509_);
    crate::leanh::lean_closure_set(v___x_1510_, 1, v___x_1509_);
    return v___x_1510_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1511_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__1_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__1,
    );
    v___x_1512_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_moduleTk_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1513_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1513_, 0, v___x_1512_);
    crate::leanh::lean_closure_set(v___x_1513_, 1, v___x_1511_);
    return v___x_1513_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1514_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__2_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__2,
    );
    v___x_1515_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_optional_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1515_, 0, v___x_1514_);
    return v___x_1515_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1516_ = crate::leanh::lean_alloc_closure(
        l_Lean_ppLine_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1517_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_prelude_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1518_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1518_, 0, v___x_1517_);
    crate::leanh::lean_closure_set(v___x_1518_, 1, v___x_1516_);
    return v___x_1518_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1519_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__4_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__4,
    );
    v___x_1520_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_optional_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1520_, 0, v___x_1519_);
    return v___x_1520_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1521_ = crate::leanh::lean_alloc_closure(
        l_Lean_ppLine_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1522_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_import_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1523_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1523_, 0, v___x_1522_);
    crate::leanh::lean_closure_set(v___x_1523_, 1, v___x_1521_);
    return v___x_1523_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1524_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__6_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__6,
    );
    v___x_1525_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_many_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1525_, 0, v___x_1524_);
    return v___x_1525_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1526_ = crate::leanh::lean_alloc_closure(
        l_Lean_ppLine_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1527_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__7_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__7,
    );
    v___x_1528_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1528_, 0, v___x_1527_);
    crate::leanh::lean_closure_set(v___x_1528_, 1, v___x_1526_);
    return v___x_1528_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1529_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__8_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__8,
    );
    v___x_1530_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__5_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__5,
    );
    v___x_1531_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1531_, 0, v___x_1530_);
    crate::leanh::lean_closure_set(v___x_1531_, 1, v___x_1529_);
    return v___x_1531_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1532_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__9_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__9,
    );
    v___x_1533_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__3_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__3,
    );
    v___x_1534_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1534_, 0, v___x_1533_);
    crate::leanh::lean_closure_set(v___x_1534_, 1, v___x_1532_);
    return v___x_1534_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1535_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__10_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__10,
    );
    v___x_1536_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_1537_ = l_Lean_Parser_Module_header___closed__1;
    v___x_1538_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_1538_, 0, v___x_1537_);
    crate::leanh::lean_closure_set(v___x_1538_, 1, v___x_1536_);
    crate::leanh::lean_closure_set(v___x_1538_, 2, v___x_1535_);
    return v___x_1538_;
}
pub unsafe fn l_Lean_Parser_Module_header_formatter(
    mut v_a_1539_: *mut crate::leanh::LeanObject,
    mut v_a_1540_: *mut crate::leanh::LeanObject,
    mut v_a_1541_: *mut crate::leanh::LeanObject,
    mut v_a_1542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1544_ = l_Lean_Parser_Module_header_formatter___closed__0;
    v___x_1545_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__11_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__11,
    );
    v___x_1546_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_1544_,
        v___x_1545_,
        v_a_1539_,
        v_a_1540_,
        v_a_1541_,
        v_a_1542_,
    );
    return v___x_1546_;
}
pub unsafe fn l_Lean_Parser_Module_header_formatter___boxed(
    mut v_a_1547_: *mut crate::leanh::LeanObject,
    mut v_a_1548_: *mut crate::leanh::LeanObject,
    mut v_a_1549_: *mut crate::leanh::LeanObject,
    mut v_a_1550_: *mut crate::leanh::LeanObject,
    mut v_a_1551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1552_ = l_Lean_Parser_Module_header_formatter(v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
    crate::leanh::lean_dec(v_a_1550_);
    crate::leanh::lean_dec_ref(v_a_1549_);
    crate::leanh::lean_dec(v_a_1548_);
    crate::leanh::lean_dec_ref(v_a_1547_);
    return v_res_1552_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1560_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1561_ = l_Lean_Parser_Module_header___closed__1;
    v___x_1562_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0;
    v___x_1563_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_header_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1564_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1560_,
        v___x_1561_,
        v___x_1562_,
        v___x_1563_,
    );
    return v___x_1564_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___boxed(
    mut v_a_1565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1566_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27();
    return v_res_1566_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module_formatter___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1581_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__1_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__1,
    );
    v___x_1582_ = l_Lean_Parser_Module_module_formatter___closed__2;
    v___x_1583_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1583_, 0, v___x_1582_);
    crate::leanh::lean_closure_set(v___x_1583_, 1, v___x_1581_);
    return v___x_1583_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module_formatter___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1584_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_formatter___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_formatter___closed__3_once),
        _init_l_Lean_Parser_Module_module_formatter___closed__3,
    );
    v___x_1585_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_many_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1585_, 0, v___x_1584_);
    return v___x_1585_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module_formatter___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1586_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_formatter___closed__4_once),
        _init_l_Lean_Parser_Module_module_formatter___closed__4,
    );
    v___x_1587_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_header_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1588_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1588_, 0, v___x_1587_);
    crate::leanh::lean_closure_set(v___x_1588_, 1, v___x_1586_);
    return v___x_1588_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module_formatter___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1589_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_formatter___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_formatter___closed__5_once),
        _init_l_Lean_Parser_Module_module_formatter___closed__5,
    );
    v___x_1590_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_1591_ = l_Lean_Parser_Module_module_formatter___closed__0;
    v___x_1592_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_1592_, 0, v___x_1591_);
    crate::leanh::lean_closure_set(v___x_1592_, 1, v___x_1590_);
    crate::leanh::lean_closure_set(v___x_1592_, 2, v___x_1589_);
    return v___x_1592_;
}
pub unsafe fn l_Lean_Parser_Module_module_formatter(
    mut v_a_1593_: *mut crate::leanh::LeanObject,
    mut v_a_1594_: *mut crate::leanh::LeanObject,
    mut v_a_1595_: *mut crate::leanh::LeanObject,
    mut v_a_1596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1598_ = l_Lean_Parser_Module_module_formatter___closed__1;
    v___x_1599_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_formatter___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_formatter___closed__6_once),
        _init_l_Lean_Parser_Module_module_formatter___closed__6,
    );
    v___x_1600_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_1598_,
        v___x_1599_,
        v_a_1593_,
        v_a_1594_,
        v_a_1595_,
        v_a_1596_,
    );
    return v___x_1600_;
}
pub unsafe fn l_Lean_Parser_Module_module_formatter___boxed(
    mut v_a_1601_: *mut crate::leanh::LeanObject,
    mut v_a_1602_: *mut crate::leanh::LeanObject,
    mut v_a_1603_: *mut crate::leanh::LeanObject,
    mut v_a_1604_: *mut crate::leanh::LeanObject,
    mut v_a_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1606_ = l_Lean_Parser_Module_module_formatter(v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
    crate::leanh::lean_dec(v_a_1604_);
    crate::leanh::lean_dec_ref(v_a_1603_);
    crate::leanh::lean_dec(v_a_1602_);
    crate::leanh::lean_dec_ref(v_a_1601_);
    return v_res_1606_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1615_ = l_Lean_Parser_Module_module_formatter___closed__0;
    v___x_1616_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0;
    v___x_1617_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_module_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1618_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1614_,
        v___x_1615_,
        v___x_1616_,
        v___x_1617_,
    );
    return v___x_1618_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___boxed(
    mut v_a_1619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1620_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31();
    return v_res_1620_;
}
pub unsafe fn l_Lean_Parser_Module_moduleTk_parenthesizer(
    mut v_a_1634_: *mut crate::leanh::LeanObject,
    mut v_a_1635_: *mut crate::leanh::LeanObject,
    mut v_a_1636_: *mut crate::leanh::LeanObject,
    mut v_a_1637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1639_ = l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0;
    v___x_1640_ = l_Lean_Parser_Module_moduleTk_parenthesizer___closed__2;
    v___x_1641_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_1639_,
        v___x_1640_,
        v_a_1634_,
        v_a_1635_,
        v_a_1636_,
        v_a_1637_,
    );
    return v___x_1641_;
}
pub unsafe fn l_Lean_Parser_Module_moduleTk_parenthesizer___boxed(
    mut v_a_1642_: *mut crate::leanh::LeanObject,
    mut v_a_1643_: *mut crate::leanh::LeanObject,
    mut v_a_1644_: *mut crate::leanh::LeanObject,
    mut v_a_1645_: *mut crate::leanh::LeanObject,
    mut v_a_1646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1647_ =
        l_Lean_Parser_Module_moduleTk_parenthesizer(v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_);
    crate::leanh::lean_dec(v_a_1645_);
    crate::leanh::lean_dec_ref(v_a_1644_);
    crate::leanh::lean_dec(v_a_1643_);
    crate::leanh::lean_dec_ref(v_a_1642_);
    return v_res_1647_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1656_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1657_ = l_Lean_Parser_Module_moduleTk___closed__4;
    v___x_1658_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1;
    v___x_1659_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_moduleTk_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1660_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1656_,
        v___x_1657_,
        v___x_1658_,
        v___x_1659_,
    );
    return v___x_1660_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___boxed(
    mut v_a_1661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1662_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35();
    return v_res_1662_;
}
pub unsafe fn l_Lean_Parser_Module_prelude_parenthesizer(
    mut v_a_1676_: *mut crate::leanh::LeanObject,
    mut v_a_1677_: *mut crate::leanh::LeanObject,
    mut v_a_1678_: *mut crate::leanh::LeanObject,
    mut v_a_1679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1681_ = l_Lean_Parser_Module_prelude_parenthesizer___closed__0;
    v___x_1682_ = l_Lean_Parser_Module_prelude_parenthesizer___closed__2;
    v___x_1683_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_1681_,
        v___x_1682_,
        v_a_1676_,
        v_a_1677_,
        v_a_1678_,
        v_a_1679_,
    );
    return v___x_1683_;
}
pub unsafe fn l_Lean_Parser_Module_prelude_parenthesizer___boxed(
    mut v_a_1684_: *mut crate::leanh::LeanObject,
    mut v_a_1685_: *mut crate::leanh::LeanObject,
    mut v_a_1686_: *mut crate::leanh::LeanObject,
    mut v_a_1687_: *mut crate::leanh::LeanObject,
    mut v_a_1688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1689_ =
        l_Lean_Parser_Module_prelude_parenthesizer(v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
    crate::leanh::lean_dec(v_a_1687_);
    crate::leanh::lean_dec_ref(v_a_1686_);
    crate::leanh::lean_dec(v_a_1685_);
    crate::leanh::lean_dec_ref(v_a_1684_);
    return v_res_1689_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1697_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1698_ = l_Lean_Parser_Module_prelude___closed__1;
    v___x_1699_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0;
    v___x_1700_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_prelude_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1701_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1697_,
        v___x_1698_,
        v___x_1699_,
        v___x_1700_,
    );
    return v___x_1701_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___boxed(
    mut v_a_1702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1703_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39();
    return v_res_1703_;
}
pub unsafe fn l_Lean_Parser_Module_public_parenthesizer(
    mut v_a_1716_: *mut crate::leanh::LeanObject,
    mut v_a_1717_: *mut crate::leanh::LeanObject,
    mut v_a_1718_: *mut crate::leanh::LeanObject,
    mut v_a_1719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1721_ = l_Lean_Parser_Module_public_parenthesizer___closed__0;
    v___x_1722_ = l_Lean_Parser_Module_public_parenthesizer___closed__2;
    v___x_1723_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_1721_,
        v___x_1722_,
        v_a_1716_,
        v_a_1717_,
        v_a_1718_,
        v_a_1719_,
    );
    return v___x_1723_;
}
pub unsafe fn l_Lean_Parser_Module_public_parenthesizer___boxed(
    mut v_a_1724_: *mut crate::leanh::LeanObject,
    mut v_a_1725_: *mut crate::leanh::LeanObject,
    mut v_a_1726_: *mut crate::leanh::LeanObject,
    mut v_a_1727_: *mut crate::leanh::LeanObject,
    mut v_a_1728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1729_ =
        l_Lean_Parser_Module_public_parenthesizer(v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
    crate::leanh::lean_dec(v_a_1727_);
    crate::leanh::lean_dec_ref(v_a_1726_);
    crate::leanh::lean_dec(v_a_1725_);
    crate::leanh::lean_dec_ref(v_a_1724_);
    return v_res_1729_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1737_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1738_ = l_Lean_Parser_Module_public___closed__1;
    v___x_1739_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0;
    v___x_1740_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_public_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1741_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1737_,
        v___x_1738_,
        v___x_1739_,
        v___x_1740_,
    );
    return v___x_1741_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___boxed(
    mut v_a_1742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1743_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43();
    return v_res_1743_;
}
pub unsafe fn l_Lean_Parser_Module_meta_parenthesizer(
    mut v_a_1756_: *mut crate::leanh::LeanObject,
    mut v_a_1757_: *mut crate::leanh::LeanObject,
    mut v_a_1758_: *mut crate::leanh::LeanObject,
    mut v_a_1759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1761_ = l_Lean_Parser_Module_meta_parenthesizer___closed__0;
    v___x_1762_ = l_Lean_Parser_Module_meta_parenthesizer___closed__2;
    v___x_1763_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_1761_,
        v___x_1762_,
        v_a_1756_,
        v_a_1757_,
        v_a_1758_,
        v_a_1759_,
    );
    return v___x_1763_;
}
pub unsafe fn l_Lean_Parser_Module_meta_parenthesizer___boxed(
    mut v_a_1764_: *mut crate::leanh::LeanObject,
    mut v_a_1765_: *mut crate::leanh::LeanObject,
    mut v_a_1766_: *mut crate::leanh::LeanObject,
    mut v_a_1767_: *mut crate::leanh::LeanObject,
    mut v_a_1768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1769_ =
        l_Lean_Parser_Module_meta_parenthesizer(v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
    crate::leanh::lean_dec(v_a_1767_);
    crate::leanh::lean_dec_ref(v_a_1766_);
    crate::leanh::lean_dec(v_a_1765_);
    crate::leanh::lean_dec_ref(v_a_1764_);
    return v_res_1769_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1778_ = l_Lean_Parser_Module_meta___closed__1;
    v___x_1779_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0;
    v___x_1780_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_meta_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1781_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1777_,
        v___x_1778_,
        v___x_1779_,
        v___x_1780_,
    );
    return v___x_1781_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___boxed(
    mut v_a_1782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1783_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47();
    return v_res_1783_;
}
pub unsafe fn l_Lean_Parser_Module_all_parenthesizer(
    mut v_a_1796_: *mut crate::leanh::LeanObject,
    mut v_a_1797_: *mut crate::leanh::LeanObject,
    mut v_a_1798_: *mut crate::leanh::LeanObject,
    mut v_a_1799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1801_ = l_Lean_Parser_Module_all_parenthesizer___closed__0;
    v___x_1802_ = l_Lean_Parser_Module_all_parenthesizer___closed__2;
    v___x_1803_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_1801_,
        v___x_1802_,
        v_a_1796_,
        v_a_1797_,
        v_a_1798_,
        v_a_1799_,
    );
    return v___x_1803_;
}
pub unsafe fn l_Lean_Parser_Module_all_parenthesizer___boxed(
    mut v_a_1804_: *mut crate::leanh::LeanObject,
    mut v_a_1805_: *mut crate::leanh::LeanObject,
    mut v_a_1806_: *mut crate::leanh::LeanObject,
    mut v_a_1807_: *mut crate::leanh::LeanObject,
    mut v_a_1808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1809_ =
        l_Lean_Parser_Module_all_parenthesizer(v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
    crate::leanh::lean_dec(v_a_1807_);
    crate::leanh::lean_dec_ref(v_a_1806_);
    crate::leanh::lean_dec(v_a_1805_);
    crate::leanh::lean_dec_ref(v_a_1804_);
    return v_res_1809_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1817_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1818_ = l_Lean_Parser_Module_all___closed__1;
    v___x_1819_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0;
    v___x_1820_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_all_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1821_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1817_,
        v___x_1818_,
        v___x_1819_,
        v___x_1820_,
    );
    return v___x_1821_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___boxed(
    mut v_a_1822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1823_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51();
    return v_res_1823_;
}
pub unsafe fn l_Lean_Parser_Module_import_parenthesizer___lam__0(
    mut v___x_1824_: *mut crate::leanh::LeanObject,
    mut v___x_1825_: *mut crate::leanh::LeanObject,
    mut v___y_1826_: *mut crate::leanh::LeanObject,
    mut v___y_1827_: *mut crate::leanh::LeanObject,
    mut v___y_1828_: *mut crate::leanh::LeanObject,
    mut v___y_1829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1831_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(
        v___x_1824_,
        v___x_1825_,
        v___y_1826_,
        v___y_1827_,
        v___y_1828_,
        v___y_1829_,
    );
    return v___x_1831_;
}
pub unsafe fn l_Lean_Parser_Module_import_parenthesizer___lam__0___boxed(
    mut v___x_1832_: *mut crate::leanh::LeanObject,
    mut v___x_1833_: *mut crate::leanh::LeanObject,
    mut v___y_1834_: *mut crate::leanh::LeanObject,
    mut v___y_1835_: *mut crate::leanh::LeanObject,
    mut v___y_1836_: *mut crate::leanh::LeanObject,
    mut v___y_1837_: *mut crate::leanh::LeanObject,
    mut v___y_1838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1839_ = l_Lean_Parser_Module_import_parenthesizer___lam__0(
        v___x_1832_,
        v___x_1833_,
        v___y_1834_,
        v___y_1835_,
        v___y_1836_,
        v___y_1837_,
    );
    crate::leanh::lean_dec(v___y_1837_);
    crate::leanh::lean_dec_ref(v___y_1836_);
    crate::leanh::lean_dec(v___y_1835_);
    crate::leanh::lean_dec_ref(v___y_1834_);
    return v_res_1839_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_parenthesizer___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1847_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_public_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1848_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_optional_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1848_, 0, v___x_1847_);
    return v___x_1848_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_parenthesizer___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1849_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_meta_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1850_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_optional_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1850_, 0, v___x_1849_);
    return v___x_1850_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_parenthesizer___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1853_ = l_Lean_Parser_Module_import_parenthesizer___closed__3;
    v___x_1854_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__2_once),
        _init_l_Lean_Parser_Module_import_parenthesizer___closed__2,
    );
    v___x_1855_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1855_, 0, v___x_1854_);
    crate::leanh::lean_closure_set(v___x_1855_, 1, v___x_1853_);
    return v___x_1855_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_parenthesizer___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1856_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__4_once),
        _init_l_Lean_Parser_Module_import_parenthesizer___closed__4,
    );
    v___x_1857_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__1_once),
        _init_l_Lean_Parser_Module_import_parenthesizer___closed__1,
    );
    v___f_1858_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_import_parenthesizer___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1858_, 0, v___x_1857_);
    crate::leanh::lean_closure_set(v___f_1858_, 1, v___x_1856_);
    return v___f_1858_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_parenthesizer___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1859_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_all_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1860_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_optional_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1860_, 0, v___x_1859_);
    return v___x_1860_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_parenthesizer___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1862_ = l_Lean_Parser_Module_import_parenthesizer___closed__7;
    v___x_1863_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__6_once),
        _init_l_Lean_Parser_Module_import_parenthesizer___closed__6,
    );
    v___x_1864_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1864_, 0, v___x_1863_);
    crate::leanh::lean_closure_set(v___x_1864_, 1, v___x_1862_);
    return v___x_1864_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_parenthesizer___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1865_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__8_once),
        _init_l_Lean_Parser_Module_import_parenthesizer___closed__8,
    );
    v___f_1866_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__5_once),
        _init_l_Lean_Parser_Module_import_parenthesizer___closed__5,
    );
    v___x_1867_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1867_, 0, v___f_1866_);
    crate::leanh::lean_closure_set(v___x_1867_, 1, v___x_1865_);
    return v___x_1867_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_parenthesizer___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1868_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__9_once),
        _init_l_Lean_Parser_Module_import_parenthesizer___closed__9,
    );
    v___x_1869_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_1870_ = l_Lean_Parser_Module_import___closed__1;
    v___x_1871_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_1871_, 0, v___x_1870_);
    crate::leanh::lean_closure_set(v___x_1871_, 1, v___x_1869_);
    crate::leanh::lean_closure_set(v___x_1871_, 2, v___x_1868_);
    return v___x_1871_;
}
pub unsafe fn l_Lean_Parser_Module_import_parenthesizer(
    mut v_a_1872_: *mut crate::leanh::LeanObject,
    mut v_a_1873_: *mut crate::leanh::LeanObject,
    mut v_a_1874_: *mut crate::leanh::LeanObject,
    mut v_a_1875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1877_ = l_Lean_Parser_Module_import_parenthesizer___closed__0;
    v___x_1878_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__10_once),
        _init_l_Lean_Parser_Module_import_parenthesizer___closed__10,
    );
    v___x_1879_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_1877_,
        v___x_1878_,
        v_a_1872_,
        v_a_1873_,
        v_a_1874_,
        v_a_1875_,
    );
    return v___x_1879_;
}
pub unsafe fn l_Lean_Parser_Module_import_parenthesizer___boxed(
    mut v_a_1880_: *mut crate::leanh::LeanObject,
    mut v_a_1881_: *mut crate::leanh::LeanObject,
    mut v_a_1882_: *mut crate::leanh::LeanObject,
    mut v_a_1883_: *mut crate::leanh::LeanObject,
    mut v_a_1884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1885_ =
        l_Lean_Parser_Module_import_parenthesizer(v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
    crate::leanh::lean_dec(v_a_1883_);
    crate::leanh::lean_dec_ref(v_a_1882_);
    crate::leanh::lean_dec(v_a_1881_);
    crate::leanh::lean_dec_ref(v_a_1880_);
    return v_res_1885_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1893_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1894_ = l_Lean_Parser_Module_import___closed__1;
    v___x_1895_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0;
    v___x_1896_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_import_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1897_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1893_,
        v___x_1894_,
        v___x_1895_,
        v___x_1896_,
    );
    return v___x_1897_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___boxed(
    mut v_a_1898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1899_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55();
    return v_res_1899_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1910_ = l_Lean_Parser_Module_header_parenthesizer___closed__2;
    v___x_1911_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_moduleTk_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1912_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1912_, 0, v___x_1911_);
    crate::leanh::lean_closure_set(v___x_1912_, 1, v___x_1910_);
    return v___x_1912_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1913_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__3_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__3,
    );
    v___x_1914_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_optional_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1914_, 0, v___x_1913_);
    return v___x_1914_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1915_ = l_Lean_Parser_Module_header_parenthesizer___closed__1;
    v___x_1916_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_prelude_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1917_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1917_, 0, v___x_1916_);
    crate::leanh::lean_closure_set(v___x_1917_, 1, v___x_1915_);
    return v___x_1917_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1918_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__5_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__5,
    );
    v___x_1919_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_optional_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1919_, 0, v___x_1918_);
    return v___x_1919_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1920_ = l_Lean_Parser_Module_header_parenthesizer___closed__1;
    v___x_1921_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_import_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1922_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1922_, 0, v___x_1921_);
    crate::leanh::lean_closure_set(v___x_1922_, 1, v___x_1920_);
    return v___x_1922_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1923_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__7_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__7,
    );
    v___x_1924_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_many_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1924_, 0, v___x_1923_);
    return v___x_1924_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1925_ = l_Lean_Parser_Module_header_parenthesizer___closed__1;
    v___x_1926_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__8_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__8,
    );
    v___x_1927_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1927_, 0, v___x_1926_);
    crate::leanh::lean_closure_set(v___x_1927_, 1, v___x_1925_);
    return v___x_1927_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1928_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__9_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__9,
    );
    v___x_1929_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__6_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__6,
    );
    v___x_1930_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1930_, 0, v___x_1929_);
    crate::leanh::lean_closure_set(v___x_1930_, 1, v___x_1928_);
    return v___x_1930_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1931_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__10_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__10,
    );
    v___x_1932_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__4_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__4,
    );
    v___x_1933_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1933_, 0, v___x_1932_);
    crate::leanh::lean_closure_set(v___x_1933_, 1, v___x_1931_);
    return v___x_1933_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1934_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__11_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__11,
    );
    v___x_1935_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_1936_ = l_Lean_Parser_Module_header___closed__1;
    v___x_1937_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_1937_, 0, v___x_1936_);
    crate::leanh::lean_closure_set(v___x_1937_, 1, v___x_1935_);
    crate::leanh::lean_closure_set(v___x_1937_, 2, v___x_1934_);
    return v___x_1937_;
}
pub unsafe fn l_Lean_Parser_Module_header_parenthesizer(
    mut v_a_1938_: *mut crate::leanh::LeanObject,
    mut v_a_1939_: *mut crate::leanh::LeanObject,
    mut v_a_1940_: *mut crate::leanh::LeanObject,
    mut v_a_1941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1943_ = l_Lean_Parser_Module_header_parenthesizer___closed__0;
    v___x_1944_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__12_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__12,
    );
    v___x_1945_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_1943_,
        v___x_1944_,
        v_a_1938_,
        v_a_1939_,
        v_a_1940_,
        v_a_1941_,
    );
    return v___x_1945_;
}
pub unsafe fn l_Lean_Parser_Module_header_parenthesizer___boxed(
    mut v_a_1946_: *mut crate::leanh::LeanObject,
    mut v_a_1947_: *mut crate::leanh::LeanObject,
    mut v_a_1948_: *mut crate::leanh::LeanObject,
    mut v_a_1949_: *mut crate::leanh::LeanObject,
    mut v_a_1950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1951_ =
        l_Lean_Parser_Module_header_parenthesizer(v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
    crate::leanh::lean_dec(v_a_1949_);
    crate::leanh::lean_dec_ref(v_a_1948_);
    crate::leanh::lean_dec(v_a_1947_);
    crate::leanh::lean_dec_ref(v_a_1946_);
    return v_res_1951_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1959_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1960_ = l_Lean_Parser_Module_header___closed__1;
    v___x_1961_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0;
    v___x_1962_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_header_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1963_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1959_,
        v___x_1960_,
        v___x_1961_,
        v___x_1962_,
    );
    return v___x_1963_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___boxed(
    mut v_a_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1965_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59();
    return v_res_1965_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module_parenthesizer___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1980_ = l_Lean_Parser_Module_module_parenthesizer___closed__3;
    v___x_1981_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_header_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1982_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1982_, 0, v___x_1981_);
    crate::leanh::lean_closure_set(v___x_1982_, 1, v___x_1980_);
    return v___x_1982_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module_parenthesizer___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1983_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_parenthesizer___closed__4_once),
        _init_l_Lean_Parser_Module_module_parenthesizer___closed__4,
    );
    v___x_1984_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_1985_ = l_Lean_Parser_Module_module_formatter___closed__0;
    v___x_1986_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_1986_, 0, v___x_1985_);
    crate::leanh::lean_closure_set(v___x_1986_, 1, v___x_1984_);
    crate::leanh::lean_closure_set(v___x_1986_, 2, v___x_1983_);
    return v___x_1986_;
}
pub unsafe fn l_Lean_Parser_Module_module_parenthesizer(
    mut v_a_1987_: *mut crate::leanh::LeanObject,
    mut v_a_1988_: *mut crate::leanh::LeanObject,
    mut v_a_1989_: *mut crate::leanh::LeanObject,
    mut v_a_1990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1992_ = l_Lean_Parser_Module_module_parenthesizer___closed__0;
    v___x_1993_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_parenthesizer___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_parenthesizer___closed__5_once),
        _init_l_Lean_Parser_Module_module_parenthesizer___closed__5,
    );
    v___x_1994_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_1992_,
        v___x_1993_,
        v_a_1987_,
        v_a_1988_,
        v_a_1989_,
        v_a_1990_,
    );
    return v___x_1994_;
}
pub unsafe fn l_Lean_Parser_Module_module_parenthesizer___boxed(
    mut v_a_1995_: *mut crate::leanh::LeanObject,
    mut v_a_1996_: *mut crate::leanh::LeanObject,
    mut v_a_1997_: *mut crate::leanh::LeanObject,
    mut v_a_1998_: *mut crate::leanh::LeanObject,
    mut v_a_1999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2000_ =
        l_Lean_Parser_Module_module_parenthesizer(v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
    crate::leanh::lean_dec(v_a_1998_);
    crate::leanh::lean_dec_ref(v_a_1997_);
    crate::leanh::lean_dec(v_a_1996_);
    crate::leanh::lean_dec_ref(v_a_1995_);
    return v_res_2000_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2008_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_2009_ = l_Lean_Parser_Module_module_formatter___closed__0;
    v___x_2010_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0;
    v___x_2011_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Module_module_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2012_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2008_,
        v___x_2009_,
        v___x_2010_,
        v___x_2011_,
    );
    return v___x_2012_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___boxed(
    mut v_a_2013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2014_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63();
    return v_res_2014_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2015_: u8 = 0;
    let mut v___x_2016_: u8 = 0;
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2015_ = 0;
    v___x_2016_ = 1;
    v___x_2017_ = l_Lean_Parser_Module_module_formatter___closed__0;
    v___x_2018_ = l_Lean_Parser_Module_moduleTk___closed__6;
    v___x_2019_ = l_Lean_Parser_mkAntiquot(v___x_2018_, v___x_2017_, v___x_2016_, v___x_2015_);
    return v___x_2019_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2023_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2024_ = l_Lean_Parser_Module_module___closed__2;
    v___x_2025_ = l_Lean_Parser_categoryParser(v___x_2024_, v___x_2023_);
    return v___x_2025_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2026_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__3_once),
        _init_l_Lean_Parser_Module_header___closed__3,
    );
    v___x_2027_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__3_once),
        _init_l_Lean_Parser_Module_module___closed__3,
    );
    v___x_2028_ = l_Lean_Parser_andthen(v___x_2027_, v___x_2026_);
    return v___x_2028_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2029_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__4_once),
        _init_l_Lean_Parser_Module_module___closed__4,
    );
    v___x_2030_ = l_Lean_Parser_many(v___x_2029_);
    return v___x_2030_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2031_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__5_once),
        _init_l_Lean_Parser_Module_module___closed__5,
    );
    v___x_2032_ = l_Lean_Parser_Module_header;
    v___x_2033_ = l_Lean_Parser_andthen(v___x_2032_, v___x_2031_);
    return v___x_2033_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2034_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__6_once),
        _init_l_Lean_Parser_Module_module___closed__6,
    );
    v___x_2035_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_2036_ = l_Lean_Parser_Module_module_formatter___closed__0;
    v___x_2037_ = l_Lean_Parser_leadingNode(v___x_2036_, v___x_2035_, v___x_2034_);
    return v___x_2037_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2038_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__7_once),
        _init_l_Lean_Parser_Module_module___closed__7,
    );
    v___x_2039_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__0_once),
        _init_l_Lean_Parser_Module_module___closed__0,
    );
    v___x_2040_ = l_Lean_Parser_withAntiquot(v___x_2039_, v___x_2038_);
    return v___x_2040_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2041_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__8_once),
        _init_l_Lean_Parser_Module_module___closed__8,
    );
    v___x_2042_ = l_Lean_Parser_Module_module_formatter___closed__0;
    v___x_2043_ = l_Lean_Parser_withCache(v___x_2042_, v___x_2041_);
    return v___x_2043_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module() -> *mut crate::leanh::LeanObject {
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2044_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__9_once),
        _init_l_Lean_Parser_Module_module___closed__9,
    );
    return v___x_2044_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Parser_Module_Syntax(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Module_moduleTk = _init_l_Lean_Parser_Module_moduleTk();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Module_moduleTk);
    l_Lean_Parser_Module_prelude = _init_l_Lean_Parser_Module_prelude();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Module_prelude);
    l_Lean_Parser_Module_public = _init_l_Lean_Parser_Module_public();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Module_public);
    l_Lean_Parser_Module_meta = _init_l_Lean_Parser_Module_meta();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Module_meta);
    l_Lean_Parser_Module_all = _init_l_Lean_Parser_Module_all();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Module_all);
    l_Lean_Parser_Module_import = _init_l_Lean_Parser_Module_import();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Module_import);
    l_Lean_Parser_Module_header = _init_l_Lean_Parser_Module_header();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Module_header);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Module_module = _init_l_Lean_Parser_Module_module();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Module_module);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Parser_Module_Syntax(
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
pub unsafe fn initialize_Lean_Parser_Module_Syntax(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Module_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Parser_Module_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Parser_Module_Syntax(builtin);
}
