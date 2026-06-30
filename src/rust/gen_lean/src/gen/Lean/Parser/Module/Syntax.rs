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
pub static l_Lean_Parser_Module_moduleTk___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
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
static mut l_Lean_Parser_Module_moduleTk___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_moduleTk___closed__1_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Module_moduleTk___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_moduleTk___closed__2_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Module_moduleTk___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_moduleTk___closed__3_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Module_moduleTk___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Module_moduleTk___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_moduleTk___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_moduleTk___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value)
                as *mut leanh::LeanObject,
            5561193377245250799 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Module_moduleTk___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__3_value)
                as *mut leanh::LeanObject,
            15944969286361870278 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Module_moduleTk___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_moduleTk___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_moduleTk___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Module_moduleTk___closed__6_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Module_moduleTk___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_moduleTk___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_moduleTk___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_moduleTk___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_moduleTk___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_moduleTk___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_moduleTk___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_moduleTk___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_moduleTk___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Module_moduleTk: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Module_prelude___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Module_prelude___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Module_prelude___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_prelude___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_prelude___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value)
                as *mut leanh::LeanObject,
            5561193377245250799 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Module_prelude___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__0_value)
                as *mut leanh::LeanObject,
            17898809269769340598 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Module_prelude___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_prelude___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_prelude___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_prelude___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_prelude___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_prelude___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_prelude___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_prelude___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_prelude___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_prelude___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_prelude___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Module_prelude: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Module_public___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Module_public___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Module_public___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_public___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_public___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value)
                as *mut leanh::LeanObject,
            5561193377245250799 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Module_public___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__0_value)
                as *mut leanh::LeanObject,
            12460543829726897862 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Module_public___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_public___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_public___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_public___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_public___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_public___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_public___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_public___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_public___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_public___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_public___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Module_public: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Module_meta___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Module_meta___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Module_meta___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_meta___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_meta___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value)
                as *mut leanh::LeanObject,
            5561193377245250799 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Module_meta___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__0_value)
                as *mut leanh::LeanObject,
            17003524124175295577 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Module_meta___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_meta___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_meta___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_meta___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_meta___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_meta___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_meta___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_meta___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_meta___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_meta___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_meta___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Module_meta: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Module_all___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Module_all___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Module_all___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_all___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_all___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value)
                as *mut leanh::LeanObject,
            5561193377245250799 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Module_all___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__0_value)
                as *mut leanh::LeanObject,
            9485984681193916779 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Module_all___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_all___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_all___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_all___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_all___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_all___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_all___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_all___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_all___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_all___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_all___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Module_all: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Module_import___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Module_import___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Module_import___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_import___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_import___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value)
                as *mut leanh::LeanObject,
            5561193377245250799 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Module_import___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__0_value)
                as *mut leanh::LeanObject,
            3187861556840815537 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Module_import___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_import___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Module_import___closed__5_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Module_import___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_import___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Module_import: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Module_header___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Module_header___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Module_header___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_header___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Module_header___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value)
                as *mut leanh::LeanObject,
            5561193377245250799 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Module_header___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__0_value)
                as *mut leanh::LeanObject,
            14592748414440353064 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Module_header___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_header___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Module_header: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Module_moduleTk_formatter___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__4_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_moduleTk_formatter___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk_formatter___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_moduleTk_formatter___closed__1_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_moduleTk_formatter___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk_formatter___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_moduleTk_formatter___closed__2_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__4_value)
            as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk_formatter___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_moduleTk_formatter___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk_formatter___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [102, 111, 114, 109, 97, 116, 116, 101, 114, 0]};
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__3_value) as *mut leanh::LeanObject,15944969286361870278 as *mut leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value) as *mut leanh::LeanObject,7218790382489784727 as *mut leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_prelude_formatter___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__1_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_prelude_formatter___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_prelude_formatter___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_prelude_formatter___closed__1_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_prelude_formatter___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_prelude_formatter___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_prelude_formatter___closed__2_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__1_value)
            as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude_formatter___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_prelude_formatter___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_prelude_formatter___closed__2_value)
        as *mut leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__0_value) as *mut leanh::LeanObject,17898809269769340598 as *mut leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value) as *mut leanh::LeanObject,14630804532564755303 as *mut leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_public_formatter___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__1_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_public_formatter___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_public_formatter___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_public_formatter___closed__1_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_public_formatter___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_public_formatter___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_public_formatter___closed__2_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__1_value)
            as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_public_formatter___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_public_formatter___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_public_formatter___closed__2_value)
        as *mut leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__0_value) as *mut leanh::LeanObject,12460543829726897862 as *mut leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value) as *mut leanh::LeanObject,363164952207938711 as *mut leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_meta_formatter___closed__0_value: leanh::LeanClosureObject<
    4,
> = leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__1_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_meta_formatter___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_meta_formatter___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_meta_formatter___closed__1_value: leanh::LeanClosureObject<
    1,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_meta_formatter___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_meta_formatter___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_meta_formatter___closed__2_value: leanh::LeanClosureObject<
    3,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__1_value)
            as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_meta_formatter___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_meta_formatter___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_meta_formatter___closed__2_value)
        as *mut leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__0_value) as *mut leanh::LeanObject,17003524124175295577 as *mut leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value) as *mut leanh::LeanObject,10481679767173773492 as *mut leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_all_formatter___closed__0_value: leanh::LeanClosureObject<
    4,
> = leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__1_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_all_formatter___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_all_formatter___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_all_formatter___closed__1_value: leanh::LeanClosureObject<
    1,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_all_formatter___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_all_formatter___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_all_formatter___closed__2_value: leanh::LeanClosureObject<
    3,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__1_value)
            as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_all_formatter___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_all_formatter___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_all_formatter___closed__2_value)
        as *mut leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__0_value) as *mut leanh::LeanObject,9485984681193916779 as *mut leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value) as *mut leanh::LeanObject,4207927109047509902 as *mut leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_import_formatter___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__1_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_import_formatter___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_import_formatter___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_import_formatter___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_formatter___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_formatter___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_formatter___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Module_import_formatter___closed__3_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_import_formatter___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_import_formatter___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_import_formatter___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_formatter___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_formatter___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_formatter___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_formatter___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_formatter___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_formatter___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_formatter___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Module_import_formatter___closed__8_value:
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
    m_fun: l_Lean_Parser_identWithPartialTrailingDot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Module_import_formatter___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_import_formatter___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_import_formatter___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_formatter___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_formatter___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_formatter___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_formatter___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_formatter___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__0_value) as *mut leanh::LeanObject,3187861556840815537 as *mut leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value) as *mut leanh::LeanObject,7553579461518257660 as *mut leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_header_formatter___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__1_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_header_formatter___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_header_formatter___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_header_formatter___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_formatter___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_formatter___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__0_value) as *mut leanh::LeanObject,14592748414440353064 as *mut leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value) as *mut leanh::LeanObject,12937101448938299577 as *mut leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Module_module_formatter___closed__0_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_Module_module_formatter___closed__0_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_module_formatter___closed__0_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_Module_module_formatter___closed__0_value_aux_2: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_module_formatter___closed__0_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value)
            as *mut leanh::LeanObject,
        5561193377245250799 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Module_module_formatter___closed__0_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_module_formatter___closed__0_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__6_value)
            as *mut leanh::LeanObject,
        713060080782592827 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_module_formatter___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_module_formatter___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_module_formatter___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_module_formatter___closed__0_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_module_formatter___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_module_formatter___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_module_formatter___closed__2_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_commandParser_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Parser_Module_module_formatter___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_module_formatter___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_module_formatter___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module_formatter___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module_formatter___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module_formatter___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module_formatter___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module_formatter___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module_formatter___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module_formatter___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__6_value) as *mut leanh::LeanObject,713060080782592827 as *mut leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value) as *mut leanh::LeanObject,17424960447186865918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__4_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_moduleTk_parenthesizer___closed__1_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_moduleTk_parenthesizer___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk_parenthesizer___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_moduleTk_parenthesizer___closed__2_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__4_value)
            as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk_parenthesizer___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_moduleTk_parenthesizer___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk_parenthesizer___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 0]};
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__3_value) as *mut leanh::LeanObject,15944969286361870278 as *mut leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value) as *mut leanh::LeanObject,7990296077579416291 as *mut leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_prelude_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__1_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_prelude_parenthesizer___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_prelude_parenthesizer___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_prelude_parenthesizer___closed__1_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_prelude_parenthesizer___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_prelude_parenthesizer___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_prelude_parenthesizer___closed__2_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__1_value)
            as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_prelude_parenthesizer___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_prelude_parenthesizer___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_prelude_parenthesizer___closed__2_value)
        as *mut leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_prelude___closed__0_value) as *mut leanh::LeanObject,17898809269769340598 as *mut leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value) as *mut leanh::LeanObject,17284225932489850483 as *mut leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_public_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__1_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_public_parenthesizer___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_public_parenthesizer___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_public_parenthesizer___closed__1_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_public_parenthesizer___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_public_parenthesizer___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_public_parenthesizer___closed__2_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__1_value)
            as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_public_parenthesizer___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_public_parenthesizer___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_public_parenthesizer___closed__2_value)
        as *mut leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_public___closed__0_value) as *mut leanh::LeanObject,12460543829726897862 as *mut leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value) as *mut leanh::LeanObject,16358965941833244643 as *mut leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_meta_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__1_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_meta_parenthesizer___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_meta_parenthesizer___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_meta_parenthesizer___closed__1_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_meta_parenthesizer___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_meta_parenthesizer___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_meta_parenthesizer___closed__2_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__1_value)
            as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_meta_parenthesizer___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_meta_parenthesizer___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_meta_parenthesizer___closed__2_value)
        as *mut leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_meta___closed__0_value) as *mut leanh::LeanObject,17003524124175295577 as *mut leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value) as *mut leanh::LeanObject,1130732432433876904 as *mut leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_all_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__1_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_all_parenthesizer___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_all_parenthesizer___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_all_parenthesizer___closed__1_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_all_parenthesizer___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_all_parenthesizer___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_all_parenthesizer___closed__2_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__1_value)
            as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_all_parenthesizer___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_all_parenthesizer___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_all_parenthesizer___closed__2_value)
        as *mut leanh::LeanObject;
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_all___closed__0_value) as *mut leanh::LeanObject,9485984681193916779 as *mut leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value) as *mut leanh::LeanObject,12412954514720509378 as *mut leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_import_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__1_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_import_parenthesizer___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_import_parenthesizer___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_import_parenthesizer___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_parenthesizer___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_parenthesizer___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_parenthesizer___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Module_import_parenthesizer___closed__3_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_import_parenthesizer___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_import_parenthesizer___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_import_parenthesizer___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_parenthesizer___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_parenthesizer___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_parenthesizer___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_parenthesizer___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_parenthesizer___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Module_import_parenthesizer___closed__7_value:
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
    m_fun: l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Module_import_parenthesizer___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_import_parenthesizer___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_import_parenthesizer___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_parenthesizer___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_parenthesizer___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_parenthesizer___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_import_parenthesizer___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_import_parenthesizer___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_import___closed__0_value) as *mut leanh::LeanObject,3187861556840815537 as *mut leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value) as *mut leanh::LeanObject,11177889036445469280 as *mut leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_header_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__1_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_header_parenthesizer___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_header_parenthesizer___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_header_parenthesizer___closed__1_value:
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
    m_fun: l_Lean_Parser_ppLine_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Module_header_parenthesizer___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_header_parenthesizer___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_header_parenthesizer___closed__2_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_header_parenthesizer___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_header_parenthesizer___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_header_parenthesizer___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_header_parenthesizer___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_header_parenthesizer___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_parenthesizer___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_parenthesizer___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_parenthesizer___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_parenthesizer___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_parenthesizer___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_parenthesizer___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_parenthesizer___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_parenthesizer___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_header_parenthesizer___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_header_parenthesizer___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_header___closed__0_value) as *mut leanh::LeanObject,14592748414440353064 as *mut leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value) as *mut leanh::LeanObject,5268993740040961389 as *mut leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_module_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_module_formatter___closed__0_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_module_parenthesizer___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_module_parenthesizer___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_module_parenthesizer___closed__1_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_commandParser_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Parser_Module_module_parenthesizer___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_module_parenthesizer___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_module_parenthesizer___closed__2_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_module_parenthesizer___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Module_header_parenthesizer___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_module_parenthesizer___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_module_parenthesizer___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_module_parenthesizer___closed__3_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_many_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Module_module_parenthesizer___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Module_module_parenthesizer___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_module_parenthesizer___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_module_parenthesizer___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module_parenthesizer___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module_parenthesizer___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module_parenthesizer___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Module_moduleTk___closed__6_value) as *mut leanh::LeanObject,713060080782592827 as *mut leanh::LeanObject] };
pub static l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value) as *mut leanh::LeanObject,17272583890648199090 as *mut leanh::LeanObject] };
static mut l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_module___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Module_module___closed__1_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Module_module___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_module___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Module_module___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Module_module___closed__1_value)
                as *mut leanh::LeanObject,
            5063646790596052253 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Module_module___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_module___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Module_module___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Module_module___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_module___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Module_module: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Parser_Module_moduleTk___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1032_: u8 = 0;
    let mut v___x_1033_: u8 = 0;
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1032_ = 0;
    v___x_1033_ = 1;
    v___x_1034_ = l_Lean_Parser_Module_moduleTk___closed__4;
    v___x_1035_ = l_Lean_Parser_Module_moduleTk___closed__3;
    v___x_1036_ = l_Lean_Parser_mkAntiquot(v___x_1035_, v___x_1034_, v___x_1033_, v___x_1032_);
    return v___x_1036_;
}
pub unsafe fn _init_l_Lean_Parser_Module_moduleTk___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1038_ = l_Lean_Parser_Module_moduleTk___closed__6;
    v___x_1039_ = l_Lean_Parser_symbol(v___x_1038_);
    return v___x_1039_;
}
pub unsafe fn _init_l_Lean_Parser_Module_moduleTk___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1040_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__7_once),
        _init_l_Lean_Parser_Module_moduleTk___closed__7,
    );
    v___x_1041_ = leanh::lean_unsigned_to_nat(1024);
    v___x_1042_ = l_Lean_Parser_Module_moduleTk___closed__4;
    v___x_1043_ = l_Lean_Parser_leadingNode(v___x_1042_, v___x_1041_, v___x_1040_);
    return v___x_1043_;
}
pub unsafe fn _init_l_Lean_Parser_Module_moduleTk___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1044_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__8_once),
        _init_l_Lean_Parser_Module_moduleTk___closed__8,
    );
    v___x_1045_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__5_once),
        _init_l_Lean_Parser_Module_moduleTk___closed__5,
    );
    v___x_1046_ = l_Lean_Parser_withAntiquot(v___x_1045_, v___x_1044_);
    return v___x_1046_;
}
pub unsafe fn _init_l_Lean_Parser_Module_moduleTk___closed__10() -> *mut leanh::LeanObject {
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1047_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__9_once),
        _init_l_Lean_Parser_Module_moduleTk___closed__9,
    );
    v___x_1048_ = l_Lean_Parser_Module_moduleTk___closed__4;
    v___x_1049_ = l_Lean_Parser_withCache(v___x_1048_, v___x_1047_);
    return v___x_1049_;
}
pub unsafe fn _init_l_Lean_Parser_Module_moduleTk() -> *mut leanh::LeanObject {
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1050_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_moduleTk___closed__10_once),
        _init_l_Lean_Parser_Module_moduleTk___closed__10,
    );
    return v___x_1050_;
}
pub unsafe fn _init_l_Lean_Parser_Module_prelude___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1057_: u8 = 0;
    let mut v___x_1058_: u8 = 0;
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1057_ = 0;
    v___x_1058_ = 1;
    v___x_1059_ = l_Lean_Parser_Module_prelude___closed__1;
    v___x_1060_ = l_Lean_Parser_Module_prelude___closed__0;
    v___x_1061_ = l_Lean_Parser_mkAntiquot(v___x_1060_, v___x_1059_, v___x_1058_, v___x_1057_);
    return v___x_1061_;
}
pub unsafe fn _init_l_Lean_Parser_Module_prelude___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1062_ = l_Lean_Parser_Module_prelude___closed__0;
    v___x_1063_ = l_Lean_Parser_symbol(v___x_1062_);
    return v___x_1063_;
}
pub unsafe fn _init_l_Lean_Parser_Module_prelude___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__3_once),
        _init_l_Lean_Parser_Module_prelude___closed__3,
    );
    v___x_1065_ = leanh::lean_unsigned_to_nat(1024);
    v___x_1066_ = l_Lean_Parser_Module_prelude___closed__1;
    v___x_1067_ = l_Lean_Parser_leadingNode(v___x_1066_, v___x_1065_, v___x_1064_);
    return v___x_1067_;
}
pub unsafe fn _init_l_Lean_Parser_Module_prelude___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1068_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__4_once),
        _init_l_Lean_Parser_Module_prelude___closed__4,
    );
    v___x_1069_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__2_once),
        _init_l_Lean_Parser_Module_prelude___closed__2,
    );
    v___x_1070_ = l_Lean_Parser_withAntiquot(v___x_1069_, v___x_1068_);
    return v___x_1070_;
}
pub unsafe fn _init_l_Lean_Parser_Module_prelude___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1071_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__5_once),
        _init_l_Lean_Parser_Module_prelude___closed__5,
    );
    v___x_1072_ = l_Lean_Parser_Module_prelude___closed__1;
    v___x_1073_ = l_Lean_Parser_withCache(v___x_1072_, v___x_1071_);
    return v___x_1073_;
}
pub unsafe fn _init_l_Lean_Parser_Module_prelude() -> *mut leanh::LeanObject {
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1074_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_prelude___closed__6_once),
        _init_l_Lean_Parser_Module_prelude___closed__6,
    );
    return v___x_1074_;
}
pub unsafe fn _init_l_Lean_Parser_Module_public___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1081_: u8 = 0;
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1081_ = 0;
    v___x_1082_ = l_Lean_Parser_Module_public___closed__1;
    v___x_1083_ = l_Lean_Parser_Module_public___closed__0;
    v___x_1084_ = l_Lean_Parser_mkAntiquot(v___x_1083_, v___x_1082_, v___x_1081_, v___x_1081_);
    return v___x_1084_;
}
pub unsafe fn _init_l_Lean_Parser_Module_public___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1085_ = l_Lean_Parser_Module_public___closed__0;
    v___x_1086_ = l_Lean_Parser_symbol(v___x_1085_);
    return v___x_1086_;
}
pub unsafe fn _init_l_Lean_Parser_Module_public___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1087_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__3_once),
        _init_l_Lean_Parser_Module_public___closed__3,
    );
    v___x_1088_ = leanh::lean_unsigned_to_nat(1024);
    v___x_1089_ = l_Lean_Parser_Module_public___closed__1;
    v___x_1090_ = l_Lean_Parser_leadingNode(v___x_1089_, v___x_1088_, v___x_1087_);
    return v___x_1090_;
}
pub unsafe fn _init_l_Lean_Parser_Module_public___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1091_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__4_once),
        _init_l_Lean_Parser_Module_public___closed__4,
    );
    v___x_1092_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__2_once),
        _init_l_Lean_Parser_Module_public___closed__2,
    );
    v___x_1093_ = l_Lean_Parser_withAntiquot(v___x_1092_, v___x_1091_);
    return v___x_1093_;
}
pub unsafe fn _init_l_Lean_Parser_Module_public___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1094_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__5_once),
        _init_l_Lean_Parser_Module_public___closed__5,
    );
    v___x_1095_ = l_Lean_Parser_Module_public___closed__1;
    v___x_1096_ = l_Lean_Parser_withCache(v___x_1095_, v___x_1094_);
    return v___x_1096_;
}
pub unsafe fn _init_l_Lean_Parser_Module_public() -> *mut leanh::LeanObject {
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1097_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_public___closed__6_once),
        _init_l_Lean_Parser_Module_public___closed__6,
    );
    return v___x_1097_;
}
pub unsafe fn _init_l_Lean_Parser_Module_meta___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1104_: u8 = 0;
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1104_ = 0;
    v___x_1105_ = l_Lean_Parser_Module_meta___closed__1;
    v___x_1106_ = l_Lean_Parser_Module_meta___closed__0;
    v___x_1107_ = l_Lean_Parser_mkAntiquot(v___x_1106_, v___x_1105_, v___x_1104_, v___x_1104_);
    return v___x_1107_;
}
pub unsafe fn _init_l_Lean_Parser_Module_meta___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1108_ = l_Lean_Parser_Module_meta___closed__0;
    v___x_1109_ = l_Lean_Parser_symbol(v___x_1108_);
    return v___x_1109_;
}
pub unsafe fn _init_l_Lean_Parser_Module_meta___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__3_once),
        _init_l_Lean_Parser_Module_meta___closed__3,
    );
    v___x_1111_ = leanh::lean_unsigned_to_nat(1024);
    v___x_1112_ = l_Lean_Parser_Module_meta___closed__1;
    v___x_1113_ = l_Lean_Parser_leadingNode(v___x_1112_, v___x_1111_, v___x_1110_);
    return v___x_1113_;
}
pub unsafe fn _init_l_Lean_Parser_Module_meta___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1114_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__4_once),
        _init_l_Lean_Parser_Module_meta___closed__4,
    );
    v___x_1115_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__2_once),
        _init_l_Lean_Parser_Module_meta___closed__2,
    );
    v___x_1116_ = l_Lean_Parser_withAntiquot(v___x_1115_, v___x_1114_);
    return v___x_1116_;
}
pub unsafe fn _init_l_Lean_Parser_Module_meta___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1117_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__5_once),
        _init_l_Lean_Parser_Module_meta___closed__5,
    );
    v___x_1118_ = l_Lean_Parser_Module_meta___closed__1;
    v___x_1119_ = l_Lean_Parser_withCache(v___x_1118_, v___x_1117_);
    return v___x_1119_;
}
pub unsafe fn _init_l_Lean_Parser_Module_meta() -> *mut leanh::LeanObject {
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1120_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_meta___closed__6_once),
        _init_l_Lean_Parser_Module_meta___closed__6,
    );
    return v___x_1120_;
}
pub unsafe fn _init_l_Lean_Parser_Module_all___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1127_: u8 = 0;
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1127_ = 0;
    v___x_1128_ = l_Lean_Parser_Module_all___closed__1;
    v___x_1129_ = l_Lean_Parser_Module_all___closed__0;
    v___x_1130_ = l_Lean_Parser_mkAntiquot(v___x_1129_, v___x_1128_, v___x_1127_, v___x_1127_);
    return v___x_1130_;
}
pub unsafe fn _init_l_Lean_Parser_Module_all___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1131_ = l_Lean_Parser_Module_all___closed__0;
    v___x_1132_ = l_Lean_Parser_symbol(v___x_1131_);
    return v___x_1132_;
}
pub unsafe fn _init_l_Lean_Parser_Module_all___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1133_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__3_once),
        _init_l_Lean_Parser_Module_all___closed__3,
    );
    v___x_1134_ = leanh::lean_unsigned_to_nat(1024);
    v___x_1135_ = l_Lean_Parser_Module_all___closed__1;
    v___x_1136_ = l_Lean_Parser_leadingNode(v___x_1135_, v___x_1134_, v___x_1133_);
    return v___x_1136_;
}
pub unsafe fn _init_l_Lean_Parser_Module_all___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1137_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__4_once),
        _init_l_Lean_Parser_Module_all___closed__4,
    );
    v___x_1138_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__2_once),
        _init_l_Lean_Parser_Module_all___closed__2,
    );
    v___x_1139_ = l_Lean_Parser_withAntiquot(v___x_1138_, v___x_1137_);
    return v___x_1139_;
}
pub unsafe fn _init_l_Lean_Parser_Module_all___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1140_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__5_once),
        _init_l_Lean_Parser_Module_all___closed__5,
    );
    v___x_1141_ = l_Lean_Parser_Module_all___closed__1;
    v___x_1142_ = l_Lean_Parser_withCache(v___x_1141_, v___x_1140_);
    return v___x_1142_;
}
pub unsafe fn _init_l_Lean_Parser_Module_all() -> *mut leanh::LeanObject {
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1143_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_all___closed__6_once),
        _init_l_Lean_Parser_Module_all___closed__6,
    );
    return v___x_1143_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1150_: u8 = 0;
    let mut v___x_1151_: u8 = 0;
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1150_ = 0;
    v___x_1151_ = 1;
    v___x_1152_ = l_Lean_Parser_Module_import___closed__1;
    v___x_1153_ = l_Lean_Parser_Module_import___closed__0;
    v___x_1154_ = l_Lean_Parser_mkAntiquot(v___x_1153_, v___x_1152_, v___x_1151_, v___x_1150_);
    return v___x_1154_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1155_ = l_Lean_Parser_Module_public;
    v___x_1156_ = l_Lean_Parser_optional(v___x_1155_);
    return v___x_1156_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1157_ = l_Lean_Parser_Module_meta;
    v___x_1158_ = l_Lean_Parser_optional(v___x_1157_);
    return v___x_1158_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1160_ = l_Lean_Parser_Module_import___closed__5;
    v___x_1161_ = l_Lean_Parser_symbol(v___x_1160_);
    return v___x_1161_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1162_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__6_once),
        _init_l_Lean_Parser_Module_import___closed__6,
    );
    v___x_1163_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__4_once),
        _init_l_Lean_Parser_Module_import___closed__4,
    );
    v___x_1164_ = l_Lean_Parser_andthen(v___x_1163_, v___x_1162_);
    return v___x_1164_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1165_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__7_once),
        _init_l_Lean_Parser_Module_import___closed__7,
    );
    v___x_1166_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__3_once),
        _init_l_Lean_Parser_Module_import___closed__3,
    );
    v___x_1167_ = l_Lean_Parser_andthen(v___x_1166_, v___x_1165_);
    return v___x_1167_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1168_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__8_once),
        _init_l_Lean_Parser_Module_import___closed__8,
    );
    v___x_1169_ = l_Lean_Parser_atomic(v___x_1168_);
    return v___x_1169_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__10() -> *mut leanh::LeanObject {
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1170_ = l_Lean_Parser_Module_all;
    v___x_1171_ = l_Lean_Parser_optional(v___x_1170_);
    return v___x_1171_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__11() -> *mut leanh::LeanObject {
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1172_ = l_Lean_Parser_identWithPartialTrailingDot;
    v___x_1173_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__10_once),
        _init_l_Lean_Parser_Module_import___closed__10,
    );
    v___x_1174_ = l_Lean_Parser_andthen(v___x_1173_, v___x_1172_);
    return v___x_1174_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1175_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__11_once),
        _init_l_Lean_Parser_Module_import___closed__11,
    );
    v___x_1176_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__9_once),
        _init_l_Lean_Parser_Module_import___closed__9,
    );
    v___x_1177_ = l_Lean_Parser_andthen(v___x_1176_, v___x_1175_);
    return v___x_1177_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1178_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__12_once),
        _init_l_Lean_Parser_Module_import___closed__12,
    );
    v___x_1179_ = leanh::lean_unsigned_to_nat(1024);
    v___x_1180_ = l_Lean_Parser_Module_import___closed__1;
    v___x_1181_ = l_Lean_Parser_leadingNode(v___x_1180_, v___x_1179_, v___x_1178_);
    return v___x_1181_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__14() -> *mut leanh::LeanObject {
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__13_once),
        _init_l_Lean_Parser_Module_import___closed__13,
    );
    v___x_1183_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__2_once),
        _init_l_Lean_Parser_Module_import___closed__2,
    );
    v___x_1184_ = l_Lean_Parser_withAntiquot(v___x_1183_, v___x_1182_);
    return v___x_1184_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1185_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__14_once),
        _init_l_Lean_Parser_Module_import___closed__14,
    );
    v___x_1186_ = l_Lean_Parser_Module_import___closed__1;
    v___x_1187_ = l_Lean_Parser_withCache(v___x_1186_, v___x_1185_);
    return v___x_1187_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import() -> *mut leanh::LeanObject {
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1188_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import___closed__15_once),
        _init_l_Lean_Parser_Module_import___closed__15,
    );
    return v___x_1188_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1195_: u8 = 0;
    let mut v___x_1196_: u8 = 0;
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1195_ = 0;
    v___x_1196_ = 1;
    v___x_1197_ = l_Lean_Parser_Module_header___closed__1;
    v___x_1198_ = l_Lean_Parser_Module_header___closed__0;
    v___x_1199_ = l_Lean_Parser_mkAntiquot(v___x_1198_, v___x_1197_, v___x_1196_, v___x_1195_);
    return v___x_1199_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1200_ = l_Lean_Parser_skip;
    v___x_1201_ = l_Lean_Parser_andthen(v___x_1200_, v___x_1200_);
    return v___x_1201_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1202_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__3_once),
        _init_l_Lean_Parser_Module_header___closed__3,
    );
    v___x_1203_ = l_Lean_Parser_Module_moduleTk;
    v___x_1204_ = l_Lean_Parser_andthen(v___x_1203_, v___x_1202_);
    return v___x_1204_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1205_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__4_once),
        _init_l_Lean_Parser_Module_header___closed__4,
    );
    v___x_1206_ = l_Lean_Parser_optional(v___x_1205_);
    return v___x_1206_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1207_ = l_Lean_Parser_skip;
    v___x_1208_ = l_Lean_Parser_Module_prelude;
    v___x_1209_ = l_Lean_Parser_andthen(v___x_1208_, v___x_1207_);
    return v___x_1209_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1210_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__6_once),
        _init_l_Lean_Parser_Module_header___closed__6,
    );
    v___x_1211_ = l_Lean_Parser_optional(v___x_1210_);
    return v___x_1211_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1212_ = l_Lean_Parser_skip;
    v___x_1213_ = l_Lean_Parser_Module_import;
    v___x_1214_ = l_Lean_Parser_andthen(v___x_1213_, v___x_1212_);
    return v___x_1214_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1215_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__8_once),
        _init_l_Lean_Parser_Module_header___closed__8,
    );
    v___x_1216_ = l_Lean_Parser_many(v___x_1215_);
    return v___x_1216_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__10() -> *mut leanh::LeanObject {
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1217_ = l_Lean_Parser_skip;
    v___x_1218_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__9_once),
        _init_l_Lean_Parser_Module_header___closed__9,
    );
    v___x_1219_ = l_Lean_Parser_andthen(v___x_1218_, v___x_1217_);
    return v___x_1219_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__11() -> *mut leanh::LeanObject {
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1220_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__10_once),
        _init_l_Lean_Parser_Module_header___closed__10,
    );
    v___x_1221_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__7_once),
        _init_l_Lean_Parser_Module_header___closed__7,
    );
    v___x_1222_ = l_Lean_Parser_andthen(v___x_1221_, v___x_1220_);
    return v___x_1222_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1223_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__11_once),
        _init_l_Lean_Parser_Module_header___closed__11,
    );
    v___x_1224_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__5_once),
        _init_l_Lean_Parser_Module_header___closed__5,
    );
    v___x_1225_ = l_Lean_Parser_andthen(v___x_1224_, v___x_1223_);
    return v___x_1225_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1226_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__12_once),
        _init_l_Lean_Parser_Module_header___closed__12,
    );
    v___x_1227_ = leanh::lean_unsigned_to_nat(1024);
    v___x_1228_ = l_Lean_Parser_Module_header___closed__1;
    v___x_1229_ = l_Lean_Parser_leadingNode(v___x_1228_, v___x_1227_, v___x_1226_);
    return v___x_1229_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__14() -> *mut leanh::LeanObject {
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1230_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__13_once),
        _init_l_Lean_Parser_Module_header___closed__13,
    );
    v___x_1231_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__2_once),
        _init_l_Lean_Parser_Module_header___closed__2,
    );
    v___x_1232_ = l_Lean_Parser_withAntiquot(v___x_1231_, v___x_1230_);
    return v___x_1232_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1233_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__14_once),
        _init_l_Lean_Parser_Module_header___closed__14,
    );
    v___x_1234_ = l_Lean_Parser_Module_header___closed__1;
    v___x_1235_ = l_Lean_Parser_withCache(v___x_1234_, v___x_1233_);
    return v___x_1235_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header() -> *mut leanh::LeanObject {
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1236_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__15_once),
        _init_l_Lean_Parser_Module_header___closed__15,
    );
    return v___x_1236_;
}
pub unsafe fn l_Lean_Parser_Module_moduleTk_formatter(
    mut v_a_1250_: *mut leanh::LeanObject,
    mut v_a_1251_: *mut leanh::LeanObject,
    mut v_a_1252_: *mut leanh::LeanObject,
    mut v_a_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_1258_: *mut leanh::LeanObject,
    mut v_a_1259_: *mut leanh::LeanObject,
    mut v_a_1260_: *mut leanh::LeanObject,
    mut v_a_1261_: *mut leanh::LeanObject,
    mut v_a_1262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1263_ =
        l_Lean_Parser_Module_moduleTk_formatter(v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
    leanh::lean_dec(v_a_1261_);
    leanh::lean_dec_ref(v_a_1260_);
    leanh::lean_dec(v_a_1259_);
    leanh::lean_dec_ref(v_a_1258_);
    return v_res_1263_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3()
-> *mut leanh::LeanObject {
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1272_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1273_ = l_Lean_Parser_Module_moduleTk___closed__4;
    v___x_1274_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1;
    v___x_1275_ = leanh::lean_alloc_closure(
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
    mut v_a_1277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1278_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3();
    return v_res_1278_;
}
pub unsafe fn l_Lean_Parser_Module_prelude_formatter(
    mut v_a_1292_: *mut leanh::LeanObject,
    mut v_a_1293_: *mut leanh::LeanObject,
    mut v_a_1294_: *mut leanh::LeanObject,
    mut v_a_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_1300_: *mut leanh::LeanObject,
    mut v_a_1301_: *mut leanh::LeanObject,
    mut v_a_1302_: *mut leanh::LeanObject,
    mut v_a_1303_: *mut leanh::LeanObject,
    mut v_a_1304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1305_ =
        l_Lean_Parser_Module_prelude_formatter(v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
    leanh::lean_dec(v_a_1303_);
    leanh::lean_dec_ref(v_a_1302_);
    leanh::lean_dec(v_a_1301_);
    leanh::lean_dec_ref(v_a_1300_);
    return v_res_1305_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7()
-> *mut leanh::LeanObject {
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1313_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1314_ = l_Lean_Parser_Module_prelude___closed__1;
    v___x_1315_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0;
    v___x_1316_ = leanh::lean_alloc_closure(
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
    mut v_a_1318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1319_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7();
    return v_res_1319_;
}
pub unsafe fn l_Lean_Parser_Module_public_formatter(
    mut v_a_1332_: *mut leanh::LeanObject,
    mut v_a_1333_: *mut leanh::LeanObject,
    mut v_a_1334_: *mut leanh::LeanObject,
    mut v_a_1335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_1340_: *mut leanh::LeanObject,
    mut v_a_1341_: *mut leanh::LeanObject,
    mut v_a_1342_: *mut leanh::LeanObject,
    mut v_a_1343_: *mut leanh::LeanObject,
    mut v_a_1344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1345_ = l_Lean_Parser_Module_public_formatter(v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_);
    leanh::lean_dec(v_a_1343_);
    leanh::lean_dec_ref(v_a_1342_);
    leanh::lean_dec(v_a_1341_);
    leanh::lean_dec_ref(v_a_1340_);
    return v_res_1345_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11()
-> *mut leanh::LeanObject {
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1353_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1354_ = l_Lean_Parser_Module_public___closed__1;
    v___x_1355_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0;
    v___x_1356_ = leanh::lean_alloc_closure(
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
    mut v_a_1358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1359_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11();
    return v_res_1359_;
}
pub unsafe fn l_Lean_Parser_Module_meta_formatter(
    mut v_a_1372_: *mut leanh::LeanObject,
    mut v_a_1373_: *mut leanh::LeanObject,
    mut v_a_1374_: *mut leanh::LeanObject,
    mut v_a_1375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_1380_: *mut leanh::LeanObject,
    mut v_a_1381_: *mut leanh::LeanObject,
    mut v_a_1382_: *mut leanh::LeanObject,
    mut v_a_1383_: *mut leanh::LeanObject,
    mut v_a_1384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1385_ = l_Lean_Parser_Module_meta_formatter(v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
    leanh::lean_dec(v_a_1383_);
    leanh::lean_dec_ref(v_a_1382_);
    leanh::lean_dec(v_a_1381_);
    leanh::lean_dec_ref(v_a_1380_);
    return v_res_1385_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15()
-> *mut leanh::LeanObject {
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1393_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1394_ = l_Lean_Parser_Module_meta___closed__1;
    v___x_1395_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0;
    v___x_1396_ = leanh::lean_alloc_closure(
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
    mut v_a_1398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1399_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15();
    return v_res_1399_;
}
pub unsafe fn l_Lean_Parser_Module_all_formatter(
    mut v_a_1412_: *mut leanh::LeanObject,
    mut v_a_1413_: *mut leanh::LeanObject,
    mut v_a_1414_: *mut leanh::LeanObject,
    mut v_a_1415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_1420_: *mut leanh::LeanObject,
    mut v_a_1421_: *mut leanh::LeanObject,
    mut v_a_1422_: *mut leanh::LeanObject,
    mut v_a_1423_: *mut leanh::LeanObject,
    mut v_a_1424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1425_ = l_Lean_Parser_Module_all_formatter(v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
    leanh::lean_dec(v_a_1423_);
    leanh::lean_dec_ref(v_a_1422_);
    leanh::lean_dec(v_a_1421_);
    leanh::lean_dec_ref(v_a_1420_);
    return v_res_1425_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19()
-> *mut leanh::LeanObject {
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1434_ = l_Lean_Parser_Module_all___closed__1;
    v___x_1435_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0;
    v___x_1436_ = leanh::lean_alloc_closure(
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
    mut v_a_1438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1439_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19();
    return v_res_1439_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_formatter___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1447_ = leanh::lean_alloc_closure(
        l_Lean_Parser_Module_public_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1448_ = leanh::lean_alloc_closure(
        l_Lean_Parser_optional_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_1448_, 0, v___x_1447_);
    return v___x_1448_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_formatter___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1449_ = leanh::lean_alloc_closure(
        l_Lean_Parser_Module_meta_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1450_ = leanh::lean_alloc_closure(
        l_Lean_Parser_optional_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_1450_, 0, v___x_1449_);
    return v___x_1450_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_formatter___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1453_ = l_Lean_Parser_Module_import_formatter___closed__3;
    v___x_1454_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__2_once),
        _init_l_Lean_Parser_Module_import_formatter___closed__2,
    );
    v___x_1455_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1455_, 0, v___x_1454_);
    leanh::lean_closure_set(v___x_1455_, 1, v___x_1453_);
    return v___x_1455_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_formatter___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1456_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__4_once),
        _init_l_Lean_Parser_Module_import_formatter___closed__4,
    );
    v___x_1457_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__1_once),
        _init_l_Lean_Parser_Module_import_formatter___closed__1,
    );
    v___x_1458_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1458_, 0, v___x_1457_);
    leanh::lean_closure_set(v___x_1458_, 1, v___x_1456_);
    return v___x_1458_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_formatter___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1459_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__5_once),
        _init_l_Lean_Parser_Module_import_formatter___closed__5,
    );
    v___x_1460_ = leanh::lean_alloc_closure(
        l_Lean_Parser_atomic_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_1460_, 0, v___x_1459_);
    return v___x_1460_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_formatter___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1461_ = leanh::lean_alloc_closure(
        l_Lean_Parser_Module_all_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1462_ = leanh::lean_alloc_closure(
        l_Lean_Parser_optional_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_1462_, 0, v___x_1461_);
    return v___x_1462_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_formatter___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1464_ = l_Lean_Parser_Module_import_formatter___closed__8;
    v___x_1465_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__7_once),
        _init_l_Lean_Parser_Module_import_formatter___closed__7,
    );
    v___x_1466_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1466_, 0, v___x_1465_);
    leanh::lean_closure_set(v___x_1466_, 1, v___x_1464_);
    return v___x_1466_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_formatter___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1467_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__9_once),
        _init_l_Lean_Parser_Module_import_formatter___closed__9,
    );
    v___x_1468_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__6_once),
        _init_l_Lean_Parser_Module_import_formatter___closed__6,
    );
    v___x_1469_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1469_, 0, v___x_1468_);
    leanh::lean_closure_set(v___x_1469_, 1, v___x_1467_);
    return v___x_1469_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_formatter___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1470_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_formatter___closed__10_once),
        _init_l_Lean_Parser_Module_import_formatter___closed__10,
    );
    v___x_1471_ = leanh::lean_unsigned_to_nat(1024);
    v___x_1472_ = l_Lean_Parser_Module_import___closed__1;
    v___x_1473_ = leanh::lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_1473_, 0, v___x_1472_);
    leanh::lean_closure_set(v___x_1473_, 1, v___x_1471_);
    leanh::lean_closure_set(v___x_1473_, 2, v___x_1470_);
    return v___x_1473_;
}
pub unsafe fn l_Lean_Parser_Module_import_formatter(
    mut v_a_1474_: *mut leanh::LeanObject,
    mut v_a_1475_: *mut leanh::LeanObject,
    mut v_a_1476_: *mut leanh::LeanObject,
    mut v_a_1477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1479_ = l_Lean_Parser_Module_import_formatter___closed__0;
    v___x_1480_ = leanh::lean_obj_once(
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
    mut v_a_1482_: *mut leanh::LeanObject,
    mut v_a_1483_: *mut leanh::LeanObject,
    mut v_a_1484_: *mut leanh::LeanObject,
    mut v_a_1485_: *mut leanh::LeanObject,
    mut v_a_1486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1487_ = l_Lean_Parser_Module_import_formatter(v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
    leanh::lean_dec(v_a_1485_);
    leanh::lean_dec_ref(v_a_1484_);
    leanh::lean_dec(v_a_1483_);
    leanh::lean_dec_ref(v_a_1482_);
    return v_res_1487_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23()
-> *mut leanh::LeanObject {
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1495_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1496_ = l_Lean_Parser_Module_import___closed__1;
    v___x_1497_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0;
    v___x_1498_ = leanh::lean_alloc_closure(
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
    mut v_a_1500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1501_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23();
    return v_res_1501_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1509_ = leanh::lean_alloc_closure(
        l_Lean_ppLine_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    leanh::lean_inc_ref(v___x_1509_);
    v___x_1510_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1510_, 0, v___x_1509_);
    leanh::lean_closure_set(v___x_1510_, 1, v___x_1509_);
    return v___x_1510_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1511_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__1_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__1,
    );
    v___x_1512_ = leanh::lean_alloc_closure(
        l_Lean_Parser_Module_moduleTk_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1513_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1513_, 0, v___x_1512_);
    leanh::lean_closure_set(v___x_1513_, 1, v___x_1511_);
    return v___x_1513_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1514_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__2_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__2,
    );
    v___x_1515_ = leanh::lean_alloc_closure(
        l_Lean_Parser_optional_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_1515_, 0, v___x_1514_);
    return v___x_1515_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1516_ = leanh::lean_alloc_closure(
        l_Lean_ppLine_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1517_ = leanh::lean_alloc_closure(
        l_Lean_Parser_Module_prelude_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1518_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1518_, 0, v___x_1517_);
    leanh::lean_closure_set(v___x_1518_, 1, v___x_1516_);
    return v___x_1518_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1519_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__4_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__4,
    );
    v___x_1520_ = leanh::lean_alloc_closure(
        l_Lean_Parser_optional_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_1520_, 0, v___x_1519_);
    return v___x_1520_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1521_ = leanh::lean_alloc_closure(
        l_Lean_ppLine_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1522_ = leanh::lean_alloc_closure(
        l_Lean_Parser_Module_import_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1523_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1523_, 0, v___x_1522_);
    leanh::lean_closure_set(v___x_1523_, 1, v___x_1521_);
    return v___x_1523_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1524_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__6_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__6,
    );
    v___x_1525_ = leanh::lean_alloc_closure(
        l_Lean_Parser_many_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_1525_, 0, v___x_1524_);
    return v___x_1525_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1526_ = leanh::lean_alloc_closure(
        l_Lean_ppLine_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1527_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__7_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__7,
    );
    v___x_1528_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1528_, 0, v___x_1527_);
    leanh::lean_closure_set(v___x_1528_, 1, v___x_1526_);
    return v___x_1528_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1529_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__8_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__8,
    );
    v___x_1530_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__5_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__5,
    );
    v___x_1531_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1531_, 0, v___x_1530_);
    leanh::lean_closure_set(v___x_1531_, 1, v___x_1529_);
    return v___x_1531_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1532_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__9_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__9,
    );
    v___x_1533_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__3_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__3,
    );
    v___x_1534_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1534_, 0, v___x_1533_);
    leanh::lean_closure_set(v___x_1534_, 1, v___x_1532_);
    return v___x_1534_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_formatter___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1535_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__10_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__10,
    );
    v___x_1536_ = leanh::lean_unsigned_to_nat(1024);
    v___x_1537_ = l_Lean_Parser_Module_header___closed__1;
    v___x_1538_ = leanh::lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_1538_, 0, v___x_1537_);
    leanh::lean_closure_set(v___x_1538_, 1, v___x_1536_);
    leanh::lean_closure_set(v___x_1538_, 2, v___x_1535_);
    return v___x_1538_;
}
pub unsafe fn l_Lean_Parser_Module_header_formatter(
    mut v_a_1539_: *mut leanh::LeanObject,
    mut v_a_1540_: *mut leanh::LeanObject,
    mut v_a_1541_: *mut leanh::LeanObject,
    mut v_a_1542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1544_ = l_Lean_Parser_Module_header_formatter___closed__0;
    v___x_1545_ = leanh::lean_obj_once(
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
    mut v_a_1547_: *mut leanh::LeanObject,
    mut v_a_1548_: *mut leanh::LeanObject,
    mut v_a_1549_: *mut leanh::LeanObject,
    mut v_a_1550_: *mut leanh::LeanObject,
    mut v_a_1551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1552_ = l_Lean_Parser_Module_header_formatter(v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
    leanh::lean_dec(v_a_1550_);
    leanh::lean_dec_ref(v_a_1549_);
    leanh::lean_dec(v_a_1548_);
    leanh::lean_dec_ref(v_a_1547_);
    return v_res_1552_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27()
-> *mut leanh::LeanObject {
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1560_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1561_ = l_Lean_Parser_Module_header___closed__1;
    v___x_1562_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0;
    v___x_1563_ = leanh::lean_alloc_closure(
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
    mut v_a_1565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1566_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27();
    return v_res_1566_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module_formatter___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1581_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_formatter___closed__1_once),
        _init_l_Lean_Parser_Module_header_formatter___closed__1,
    );
    v___x_1582_ = l_Lean_Parser_Module_module_formatter___closed__2;
    v___x_1583_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1583_, 0, v___x_1582_);
    leanh::lean_closure_set(v___x_1583_, 1, v___x_1581_);
    return v___x_1583_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module_formatter___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1584_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_formatter___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_formatter___closed__3_once),
        _init_l_Lean_Parser_Module_module_formatter___closed__3,
    );
    v___x_1585_ = leanh::lean_alloc_closure(
        l_Lean_Parser_many_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_1585_, 0, v___x_1584_);
    return v___x_1585_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module_formatter___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1586_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_formatter___closed__4_once),
        _init_l_Lean_Parser_Module_module_formatter___closed__4,
    );
    v___x_1587_ = leanh::lean_alloc_closure(
        l_Lean_Parser_Module_header_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1588_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1588_, 0, v___x_1587_);
    leanh::lean_closure_set(v___x_1588_, 1, v___x_1586_);
    return v___x_1588_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module_formatter___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1589_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_formatter___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_formatter___closed__5_once),
        _init_l_Lean_Parser_Module_module_formatter___closed__5,
    );
    v___x_1590_ = leanh::lean_unsigned_to_nat(1024);
    v___x_1591_ = l_Lean_Parser_Module_module_formatter___closed__0;
    v___x_1592_ = leanh::lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_1592_, 0, v___x_1591_);
    leanh::lean_closure_set(v___x_1592_, 1, v___x_1590_);
    leanh::lean_closure_set(v___x_1592_, 2, v___x_1589_);
    return v___x_1592_;
}
pub unsafe fn l_Lean_Parser_Module_module_formatter(
    mut v_a_1593_: *mut leanh::LeanObject,
    mut v_a_1594_: *mut leanh::LeanObject,
    mut v_a_1595_: *mut leanh::LeanObject,
    mut v_a_1596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1598_ = l_Lean_Parser_Module_module_formatter___closed__1;
    v___x_1599_ = leanh::lean_obj_once(
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
    mut v_a_1601_: *mut leanh::LeanObject,
    mut v_a_1602_: *mut leanh::LeanObject,
    mut v_a_1603_: *mut leanh::LeanObject,
    mut v_a_1604_: *mut leanh::LeanObject,
    mut v_a_1605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1606_ = l_Lean_Parser_Module_module_formatter(v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
    leanh::lean_dec(v_a_1604_);
    leanh::lean_dec_ref(v_a_1603_);
    leanh::lean_dec(v_a_1602_);
    leanh::lean_dec_ref(v_a_1601_);
    return v_res_1606_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31()
-> *mut leanh::LeanObject {
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1615_ = l_Lean_Parser_Module_module_formatter___closed__0;
    v___x_1616_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0;
    v___x_1617_ = leanh::lean_alloc_closure(
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
    mut v_a_1619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1620_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31();
    return v_res_1620_;
}
pub unsafe fn l_Lean_Parser_Module_moduleTk_parenthesizer(
    mut v_a_1634_: *mut leanh::LeanObject,
    mut v_a_1635_: *mut leanh::LeanObject,
    mut v_a_1636_: *mut leanh::LeanObject,
    mut v_a_1637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_1642_: *mut leanh::LeanObject,
    mut v_a_1643_: *mut leanh::LeanObject,
    mut v_a_1644_: *mut leanh::LeanObject,
    mut v_a_1645_: *mut leanh::LeanObject,
    mut v_a_1646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1647_ =
        l_Lean_Parser_Module_moduleTk_parenthesizer(v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_);
    leanh::lean_dec(v_a_1645_);
    leanh::lean_dec_ref(v_a_1644_);
    leanh::lean_dec(v_a_1643_);
    leanh::lean_dec_ref(v_a_1642_);
    return v_res_1647_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35()
-> *mut leanh::LeanObject {
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1656_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1657_ = l_Lean_Parser_Module_moduleTk___closed__4;
    v___x_1658_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1;
    v___x_1659_ = leanh::lean_alloc_closure(
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
    mut v_a_1661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1662_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35();
    return v_res_1662_;
}
pub unsafe fn l_Lean_Parser_Module_prelude_parenthesizer(
    mut v_a_1676_: *mut leanh::LeanObject,
    mut v_a_1677_: *mut leanh::LeanObject,
    mut v_a_1678_: *mut leanh::LeanObject,
    mut v_a_1679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_1684_: *mut leanh::LeanObject,
    mut v_a_1685_: *mut leanh::LeanObject,
    mut v_a_1686_: *mut leanh::LeanObject,
    mut v_a_1687_: *mut leanh::LeanObject,
    mut v_a_1688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1689_ =
        l_Lean_Parser_Module_prelude_parenthesizer(v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
    leanh::lean_dec(v_a_1687_);
    leanh::lean_dec_ref(v_a_1686_);
    leanh::lean_dec(v_a_1685_);
    leanh::lean_dec_ref(v_a_1684_);
    return v_res_1689_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39()
-> *mut leanh::LeanObject {
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1697_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1698_ = l_Lean_Parser_Module_prelude___closed__1;
    v___x_1699_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0;
    v___x_1700_ = leanh::lean_alloc_closure(
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
    mut v_a_1702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1703_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39();
    return v_res_1703_;
}
pub unsafe fn l_Lean_Parser_Module_public_parenthesizer(
    mut v_a_1716_: *mut leanh::LeanObject,
    mut v_a_1717_: *mut leanh::LeanObject,
    mut v_a_1718_: *mut leanh::LeanObject,
    mut v_a_1719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_1724_: *mut leanh::LeanObject,
    mut v_a_1725_: *mut leanh::LeanObject,
    mut v_a_1726_: *mut leanh::LeanObject,
    mut v_a_1727_: *mut leanh::LeanObject,
    mut v_a_1728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1729_ =
        l_Lean_Parser_Module_public_parenthesizer(v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
    leanh::lean_dec(v_a_1727_);
    leanh::lean_dec_ref(v_a_1726_);
    leanh::lean_dec(v_a_1725_);
    leanh::lean_dec_ref(v_a_1724_);
    return v_res_1729_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43()
-> *mut leanh::LeanObject {
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1737_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1738_ = l_Lean_Parser_Module_public___closed__1;
    v___x_1739_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0;
    v___x_1740_ = leanh::lean_alloc_closure(
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
    mut v_a_1742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1743_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43();
    return v_res_1743_;
}
pub unsafe fn l_Lean_Parser_Module_meta_parenthesizer(
    mut v_a_1756_: *mut leanh::LeanObject,
    mut v_a_1757_: *mut leanh::LeanObject,
    mut v_a_1758_: *mut leanh::LeanObject,
    mut v_a_1759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_1764_: *mut leanh::LeanObject,
    mut v_a_1765_: *mut leanh::LeanObject,
    mut v_a_1766_: *mut leanh::LeanObject,
    mut v_a_1767_: *mut leanh::LeanObject,
    mut v_a_1768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1769_ =
        l_Lean_Parser_Module_meta_parenthesizer(v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
    leanh::lean_dec(v_a_1767_);
    leanh::lean_dec_ref(v_a_1766_);
    leanh::lean_dec(v_a_1765_);
    leanh::lean_dec_ref(v_a_1764_);
    return v_res_1769_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47()
-> *mut leanh::LeanObject {
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1778_ = l_Lean_Parser_Module_meta___closed__1;
    v___x_1779_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0;
    v___x_1780_ = leanh::lean_alloc_closure(
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
    mut v_a_1782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1783_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47();
    return v_res_1783_;
}
pub unsafe fn l_Lean_Parser_Module_all_parenthesizer(
    mut v_a_1796_: *mut leanh::LeanObject,
    mut v_a_1797_: *mut leanh::LeanObject,
    mut v_a_1798_: *mut leanh::LeanObject,
    mut v_a_1799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_1804_: *mut leanh::LeanObject,
    mut v_a_1805_: *mut leanh::LeanObject,
    mut v_a_1806_: *mut leanh::LeanObject,
    mut v_a_1807_: *mut leanh::LeanObject,
    mut v_a_1808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1809_ =
        l_Lean_Parser_Module_all_parenthesizer(v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
    leanh::lean_dec(v_a_1807_);
    leanh::lean_dec_ref(v_a_1806_);
    leanh::lean_dec(v_a_1805_);
    leanh::lean_dec_ref(v_a_1804_);
    return v_res_1809_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51()
-> *mut leanh::LeanObject {
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1817_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1818_ = l_Lean_Parser_Module_all___closed__1;
    v___x_1819_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0;
    v___x_1820_ = leanh::lean_alloc_closure(
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
    mut v_a_1822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1823_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51();
    return v_res_1823_;
}
pub unsafe fn l_Lean_Parser_Module_import_parenthesizer___lam__0(
    mut v___x_1824_: *mut leanh::LeanObject,
    mut v___x_1825_: *mut leanh::LeanObject,
    mut v___y_1826_: *mut leanh::LeanObject,
    mut v___y_1827_: *mut leanh::LeanObject,
    mut v___y_1828_: *mut leanh::LeanObject,
    mut v___y_1829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v___x_1832_: *mut leanh::LeanObject,
    mut v___x_1833_: *mut leanh::LeanObject,
    mut v___y_1834_: *mut leanh::LeanObject,
    mut v___y_1835_: *mut leanh::LeanObject,
    mut v___y_1836_: *mut leanh::LeanObject,
    mut v___y_1837_: *mut leanh::LeanObject,
    mut v___y_1838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1839_ = l_Lean_Parser_Module_import_parenthesizer___lam__0(
        v___x_1832_,
        v___x_1833_,
        v___y_1834_,
        v___y_1835_,
        v___y_1836_,
        v___y_1837_,
    );
    leanh::lean_dec(v___y_1837_);
    leanh::lean_dec_ref(v___y_1836_);
    leanh::lean_dec(v___y_1835_);
    leanh::lean_dec_ref(v___y_1834_);
    return v_res_1839_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_parenthesizer___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1847_ = leanh::lean_alloc_closure(
        l_Lean_Parser_Module_public_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1848_ = leanh::lean_alloc_closure(
        l_Lean_Parser_optional_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_1848_, 0, v___x_1847_);
    return v___x_1848_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_parenthesizer___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1849_ = leanh::lean_alloc_closure(
        l_Lean_Parser_Module_meta_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1850_ = leanh::lean_alloc_closure(
        l_Lean_Parser_optional_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_1850_, 0, v___x_1849_);
    return v___x_1850_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_parenthesizer___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1853_ = l_Lean_Parser_Module_import_parenthesizer___closed__3;
    v___x_1854_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__2_once),
        _init_l_Lean_Parser_Module_import_parenthesizer___closed__2,
    );
    v___x_1855_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1855_, 0, v___x_1854_);
    leanh::lean_closure_set(v___x_1855_, 1, v___x_1853_);
    return v___x_1855_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_parenthesizer___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1856_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__4_once),
        _init_l_Lean_Parser_Module_import_parenthesizer___closed__4,
    );
    v___x_1857_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__1_once),
        _init_l_Lean_Parser_Module_import_parenthesizer___closed__1,
    );
    v___f_1858_ = leanh::lean_alloc_closure(
        l_Lean_Parser_Module_import_parenthesizer___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_1858_, 0, v___x_1857_);
    leanh::lean_closure_set(v___f_1858_, 1, v___x_1856_);
    return v___f_1858_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_parenthesizer___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1859_ = leanh::lean_alloc_closure(
        l_Lean_Parser_Module_all_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1860_ = leanh::lean_alloc_closure(
        l_Lean_Parser_optional_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_1860_, 0, v___x_1859_);
    return v___x_1860_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_parenthesizer___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1862_ = l_Lean_Parser_Module_import_parenthesizer___closed__7;
    v___x_1863_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__6_once),
        _init_l_Lean_Parser_Module_import_parenthesizer___closed__6,
    );
    v___x_1864_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1864_, 0, v___x_1863_);
    leanh::lean_closure_set(v___x_1864_, 1, v___x_1862_);
    return v___x_1864_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_parenthesizer___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1865_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__8_once),
        _init_l_Lean_Parser_Module_import_parenthesizer___closed__8,
    );
    v___f_1866_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__5_once),
        _init_l_Lean_Parser_Module_import_parenthesizer___closed__5,
    );
    v___x_1867_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1867_, 0, v___f_1866_);
    leanh::lean_closure_set(v___x_1867_, 1, v___x_1865_);
    return v___x_1867_;
}
pub unsafe fn _init_l_Lean_Parser_Module_import_parenthesizer___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1868_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_import_parenthesizer___closed__9_once),
        _init_l_Lean_Parser_Module_import_parenthesizer___closed__9,
    );
    v___x_1869_ = leanh::lean_unsigned_to_nat(1024);
    v___x_1870_ = l_Lean_Parser_Module_import___closed__1;
    v___x_1871_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_1871_, 0, v___x_1870_);
    leanh::lean_closure_set(v___x_1871_, 1, v___x_1869_);
    leanh::lean_closure_set(v___x_1871_, 2, v___x_1868_);
    return v___x_1871_;
}
pub unsafe fn l_Lean_Parser_Module_import_parenthesizer(
    mut v_a_1872_: *mut leanh::LeanObject,
    mut v_a_1873_: *mut leanh::LeanObject,
    mut v_a_1874_: *mut leanh::LeanObject,
    mut v_a_1875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1877_ = l_Lean_Parser_Module_import_parenthesizer___closed__0;
    v___x_1878_ = leanh::lean_obj_once(
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
    mut v_a_1880_: *mut leanh::LeanObject,
    mut v_a_1881_: *mut leanh::LeanObject,
    mut v_a_1882_: *mut leanh::LeanObject,
    mut v_a_1883_: *mut leanh::LeanObject,
    mut v_a_1884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1885_ =
        l_Lean_Parser_Module_import_parenthesizer(v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
    leanh::lean_dec(v_a_1883_);
    leanh::lean_dec_ref(v_a_1882_);
    leanh::lean_dec(v_a_1881_);
    leanh::lean_dec_ref(v_a_1880_);
    return v_res_1885_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55()
-> *mut leanh::LeanObject {
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1893_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1894_ = l_Lean_Parser_Module_import___closed__1;
    v___x_1895_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0;
    v___x_1896_ = leanh::lean_alloc_closure(
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
    mut v_a_1898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1899_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55();
    return v_res_1899_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1910_ = l_Lean_Parser_Module_header_parenthesizer___closed__2;
    v___x_1911_ = leanh::lean_alloc_closure(
        l_Lean_Parser_Module_moduleTk_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1912_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1912_, 0, v___x_1911_);
    leanh::lean_closure_set(v___x_1912_, 1, v___x_1910_);
    return v___x_1912_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1913_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__3_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__3,
    );
    v___x_1914_ = leanh::lean_alloc_closure(
        l_Lean_Parser_optional_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_1914_, 0, v___x_1913_);
    return v___x_1914_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1915_ = l_Lean_Parser_Module_header_parenthesizer___closed__1;
    v___x_1916_ = leanh::lean_alloc_closure(
        l_Lean_Parser_Module_prelude_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1917_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1917_, 0, v___x_1916_);
    leanh::lean_closure_set(v___x_1917_, 1, v___x_1915_);
    return v___x_1917_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1918_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__5_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__5,
    );
    v___x_1919_ = leanh::lean_alloc_closure(
        l_Lean_Parser_optional_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_1919_, 0, v___x_1918_);
    return v___x_1919_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1920_ = l_Lean_Parser_Module_header_parenthesizer___closed__1;
    v___x_1921_ = leanh::lean_alloc_closure(
        l_Lean_Parser_Module_import_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1922_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1922_, 0, v___x_1921_);
    leanh::lean_closure_set(v___x_1922_, 1, v___x_1920_);
    return v___x_1922_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1923_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__7_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__7,
    );
    v___x_1924_ = leanh::lean_alloc_closure(
        l_Lean_Parser_many_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_1924_, 0, v___x_1923_);
    return v___x_1924_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1925_ = l_Lean_Parser_Module_header_parenthesizer___closed__1;
    v___x_1926_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__8_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__8,
    );
    v___x_1927_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1927_, 0, v___x_1926_);
    leanh::lean_closure_set(v___x_1927_, 1, v___x_1925_);
    return v___x_1927_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1928_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__9_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__9,
    );
    v___x_1929_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__6_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__6,
    );
    v___x_1930_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1930_, 0, v___x_1929_);
    leanh::lean_closure_set(v___x_1930_, 1, v___x_1928_);
    return v___x_1930_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1931_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__10_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__10,
    );
    v___x_1932_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__4_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__4,
    );
    v___x_1933_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1933_, 0, v___x_1932_);
    leanh::lean_closure_set(v___x_1933_, 1, v___x_1931_);
    return v___x_1933_;
}
pub unsafe fn _init_l_Lean_Parser_Module_header_parenthesizer___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1934_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header_parenthesizer___closed__11_once),
        _init_l_Lean_Parser_Module_header_parenthesizer___closed__11,
    );
    v___x_1935_ = leanh::lean_unsigned_to_nat(1024);
    v___x_1936_ = l_Lean_Parser_Module_header___closed__1;
    v___x_1937_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_1937_, 0, v___x_1936_);
    leanh::lean_closure_set(v___x_1937_, 1, v___x_1935_);
    leanh::lean_closure_set(v___x_1937_, 2, v___x_1934_);
    return v___x_1937_;
}
pub unsafe fn l_Lean_Parser_Module_header_parenthesizer(
    mut v_a_1938_: *mut leanh::LeanObject,
    mut v_a_1939_: *mut leanh::LeanObject,
    mut v_a_1940_: *mut leanh::LeanObject,
    mut v_a_1941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1943_ = l_Lean_Parser_Module_header_parenthesizer___closed__0;
    v___x_1944_ = leanh::lean_obj_once(
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
    mut v_a_1946_: *mut leanh::LeanObject,
    mut v_a_1947_: *mut leanh::LeanObject,
    mut v_a_1948_: *mut leanh::LeanObject,
    mut v_a_1949_: *mut leanh::LeanObject,
    mut v_a_1950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1951_ =
        l_Lean_Parser_Module_header_parenthesizer(v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
    leanh::lean_dec(v_a_1949_);
    leanh::lean_dec_ref(v_a_1948_);
    leanh::lean_dec(v_a_1947_);
    leanh::lean_dec_ref(v_a_1946_);
    return v_res_1951_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59()
-> *mut leanh::LeanObject {
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1959_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1960_ = l_Lean_Parser_Module_header___closed__1;
    v___x_1961_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0;
    v___x_1962_ = leanh::lean_alloc_closure(
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
    mut v_a_1964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1965_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59();
    return v_res_1965_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module_parenthesizer___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1980_ = l_Lean_Parser_Module_module_parenthesizer___closed__3;
    v___x_1981_ = leanh::lean_alloc_closure(
        l_Lean_Parser_Module_header_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1982_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1982_, 0, v___x_1981_);
    leanh::lean_closure_set(v___x_1982_, 1, v___x_1980_);
    return v___x_1982_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module_parenthesizer___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1983_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module_parenthesizer___closed__4_once),
        _init_l_Lean_Parser_Module_module_parenthesizer___closed__4,
    );
    v___x_1984_ = leanh::lean_unsigned_to_nat(1024);
    v___x_1985_ = l_Lean_Parser_Module_module_formatter___closed__0;
    v___x_1986_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_1986_, 0, v___x_1985_);
    leanh::lean_closure_set(v___x_1986_, 1, v___x_1984_);
    leanh::lean_closure_set(v___x_1986_, 2, v___x_1983_);
    return v___x_1986_;
}
pub unsafe fn l_Lean_Parser_Module_module_parenthesizer(
    mut v_a_1987_: *mut leanh::LeanObject,
    mut v_a_1988_: *mut leanh::LeanObject,
    mut v_a_1989_: *mut leanh::LeanObject,
    mut v_a_1990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1992_ = l_Lean_Parser_Module_module_parenthesizer___closed__0;
    v___x_1993_ = leanh::lean_obj_once(
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
    mut v_a_1995_: *mut leanh::LeanObject,
    mut v_a_1996_: *mut leanh::LeanObject,
    mut v_a_1997_: *mut leanh::LeanObject,
    mut v_a_1998_: *mut leanh::LeanObject,
    mut v_a_1999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2000_ =
        l_Lean_Parser_Module_module_parenthesizer(v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
    leanh::lean_dec(v_a_1998_);
    leanh::lean_dec_ref(v_a_1997_);
    leanh::lean_dec(v_a_1996_);
    leanh::lean_dec_ref(v_a_1995_);
    return v_res_2000_;
}
pub unsafe fn l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63()
-> *mut leanh::LeanObject {
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2008_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_2009_ = l_Lean_Parser_Module_module_formatter___closed__0;
    v___x_2010_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0;
    v___x_2011_ = leanh::lean_alloc_closure(
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
    mut v_a_2013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2014_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63();
    return v_res_2014_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_2015_: u8 = 0;
    let mut v___x_2016_: u8 = 0;
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2015_ = 0;
    v___x_2016_ = 1;
    v___x_2017_ = l_Lean_Parser_Module_module_formatter___closed__0;
    v___x_2018_ = l_Lean_Parser_Module_moduleTk___closed__6;
    v___x_2019_ = l_Lean_Parser_mkAntiquot(v___x_2018_, v___x_2017_, v___x_2016_, v___x_2015_);
    return v___x_2019_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2023_ = leanh::lean_unsigned_to_nat(0);
    v___x_2024_ = l_Lean_Parser_Module_module___closed__2;
    v___x_2025_ = l_Lean_Parser_categoryParser(v___x_2024_, v___x_2023_);
    return v___x_2025_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2026_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_header___closed__3_once),
        _init_l_Lean_Parser_Module_header___closed__3,
    );
    v___x_2027_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__3_once),
        _init_l_Lean_Parser_Module_module___closed__3,
    );
    v___x_2028_ = l_Lean_Parser_andthen(v___x_2027_, v___x_2026_);
    return v___x_2028_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2029_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__4_once),
        _init_l_Lean_Parser_Module_module___closed__4,
    );
    v___x_2030_ = l_Lean_Parser_many(v___x_2029_);
    return v___x_2030_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2031_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__5_once),
        _init_l_Lean_Parser_Module_module___closed__5,
    );
    v___x_2032_ = l_Lean_Parser_Module_header;
    v___x_2033_ = l_Lean_Parser_andthen(v___x_2032_, v___x_2031_);
    return v___x_2033_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2034_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__6_once),
        _init_l_Lean_Parser_Module_module___closed__6,
    );
    v___x_2035_ = leanh::lean_unsigned_to_nat(1024);
    v___x_2036_ = l_Lean_Parser_Module_module_formatter___closed__0;
    v___x_2037_ = l_Lean_Parser_leadingNode(v___x_2036_, v___x_2035_, v___x_2034_);
    return v___x_2037_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2038_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__7_once),
        _init_l_Lean_Parser_Module_module___closed__7,
    );
    v___x_2039_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__0_once),
        _init_l_Lean_Parser_Module_module___closed__0,
    );
    v___x_2040_ = l_Lean_Parser_withAntiquot(v___x_2039_, v___x_2038_);
    return v___x_2040_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2041_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__8_once),
        _init_l_Lean_Parser_Module_module___closed__8,
    );
    v___x_2042_ = l_Lean_Parser_Module_module_formatter___closed__0;
    v___x_2043_ = l_Lean_Parser_withCache(v___x_2042_, v___x_2041_);
    return v___x_2043_;
}
pub unsafe fn _init_l_Lean_Parser_Module_module() -> *mut leanh::LeanObject {
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2044_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Module_module___closed__9_once),
        _init_l_Lean_Parser_Module_module___closed__9,
    );
    return v___x_2044_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Parser_Module_Syntax(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Parser_Module_moduleTk = _init_l_Lean_Parser_Module_moduleTk();
    leanh::lean_mark_persistent(l_Lean_Parser_Module_moduleTk);
    l_Lean_Parser_Module_prelude = _init_l_Lean_Parser_Module_prelude();
    leanh::lean_mark_persistent(l_Lean_Parser_Module_prelude);
    l_Lean_Parser_Module_public = _init_l_Lean_Parser_Module_public();
    leanh::lean_mark_persistent(l_Lean_Parser_Module_public);
    l_Lean_Parser_Module_meta = _init_l_Lean_Parser_Module_meta();
    leanh::lean_mark_persistent(l_Lean_Parser_Module_meta);
    l_Lean_Parser_Module_all = _init_l_Lean_Parser_Module_all();
    leanh::lean_mark_persistent(l_Lean_Parser_Module_all);
    l_Lean_Parser_Module_import = _init_l_Lean_Parser_Module_import();
    leanh::lean_mark_persistent(l_Lean_Parser_Module_import);
    l_Lean_Parser_Module_header = _init_l_Lean_Parser_Module_header();
    leanh::lean_mark_persistent(l_Lean_Parser_Module_header);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Parser_Module_module = _init_l_Lean_Parser_Module_module();
    leanh::lean_mark_persistent(l_Lean_Parser_Module_module);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Parser_Module_Syntax(
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
pub unsafe fn initialize_Lean_Parser_Module_Syntax(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Module_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Parser_Module_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Parser_Module_Syntax(builtin);
}