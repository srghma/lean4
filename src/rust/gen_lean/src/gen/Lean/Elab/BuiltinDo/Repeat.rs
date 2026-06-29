// Lean compiler output
// Module: Lean.Elab.BuiltinDo.Repeat
// Imports: Lean.Elab.BuiltinDo.Basic Lean.Parser.Do Lean.Elab.BuiltinDo.For
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Macro_throwUnsupported___redArg, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node4, l_Lean_Syntax_node6, l_Lean_addMacroScope, l_Lean_replaceRef,
    l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Elab::BuiltinDo::Basic::{
    initialize_Lean_Elab_BuiltinDo_Basic, runtime_initialize_Lean_Elab_BuiltinDo_Basic,
};
use crate::r#gen::Lean::Elab::BuiltinDo::For::{
    initialize_Lean_Elab_BuiltinDo_For, runtime_initialize_Lean_Elab_BuiltinDo_For,
};
use crate::r#gen::Lean::Elab::Do::Basic::{
    l_Lean_Elab_Do_doElemElabAttribute, l_Lean_Elab_Do_elabDoElem, l_Lean_Elab_Do_mkPUnit___redArg,
};
use crate::r#gen::Lean::Elab::Do::InferControlInfo::l_Lean_Elab_Do_inferControlInfoSeq;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_withPushMacroExpansionStack___boxed;
use crate::r#gen::Lean::Elab::Util::l_Lean_Elab_macroAttribute;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_isExprDefEqGuarded;
use crate::r#gen::Lean::Parser::Do::{
    initialize_Lean_Parser_Do, runtime_initialize_Lean_Parser_Do,
};
use crate::ffi::lean_mk_empty_array_with_capacity;
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoRepeat___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Elab_Do_elabDoRepeat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lean_Elab_Do_elabDoRepeat___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__3_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [100, 111, 82, 101, 112, 101, 97, 116, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_elabDoRepeat___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoRepeat___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__3_value)
                as *mut crate::leanh::LeanObject,
            12861368609918422555 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__5_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [100, 111, 70, 111, 114, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_elabDoRepeat___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__6_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__6_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoRepeat___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__6_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__5_value)
                as *mut crate::leanh::LeanObject,
            16953626593407929508 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__7_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__7_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__9_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [100, 111, 70, 111, 114, 68, 101, 99, 108, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_elabDoRepeat___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__10_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__10_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__10_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoRepeat___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__10_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__9_value)
                as *mut crate::leanh::LeanObject,
            9513652089846993813 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Do_elabDoRepeat___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoRepeat___closed__12_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [104, 111, 108, 101, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__12_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_elabDoRepeat___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__13_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__13_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__13_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoRepeat___closed__13_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__13_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__12_value)
                as *mut crate::leanh::LeanObject,
            3984140175429830279 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__14_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [95, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__15_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [105, 110, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__16_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [76, 111, 111, 112, 46, 109, 107, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Do_elabDoRepeat___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoRepeat___closed__18_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [76, 111, 111, 112, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__19_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [109, 107, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__19_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_elabDoRepeat___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__18_value)
                as *mut crate::leanh::LeanObject,
            2025259594378479181 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoRepeat___closed__20_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__20_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__19_value)
                as *mut crate::leanh::LeanObject,
            14169524342265883513 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__20_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_elabDoRepeat___closed__21_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__21_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__21_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__18_value)
                as *mut crate::leanh::LeanObject,
            7119400049488606452 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoRepeat___closed__21_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__21_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__19_value)
                as *mut crate::leanh::LeanObject,
            9384228197008526428 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__22_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__21_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__23_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__21_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__24_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__23_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__25_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__22_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__24_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__26_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [100, 111, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__27_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [102, 111, 114, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__28_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [100, 111, 78, 101, 115, 116, 101, 100, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__28_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_elabDoRepeat___closed__29_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__29_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__29_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__29_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__29_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoRepeat___closed__29_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__29_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__28_value)
                as *mut crate::leanh::LeanObject,
            4570674678924417756 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__30_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [100, 111, 83, 101, 113, 73, 110, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__30_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_elabDoRepeat___closed__31_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__31_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__31_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__31_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__31_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoRepeat___closed__31_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__31_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__30_value)
                as *mut crate::leanh::LeanObject,
            3326968124746134365 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__32_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [100, 111, 83, 101, 113, 73, 116, 101, 109, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__32_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_elabDoRepeat___closed__33_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__33_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__33_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__33_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__33_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoRepeat___closed__33_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__33_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__32_value)
                as *mut crate::leanh::LeanObject,
            940684074193935882 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__34_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [59, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__35_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [100, 111, 69, 120, 112, 114, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__35_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_elabDoRepeat___closed__36_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__36_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__36_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__36_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__36_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoRepeat___closed__36_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__36_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__35_value)
                as *mut crate::leanh::LeanObject,
            5573444893818005634 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__37_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__37_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_elabDoRepeat___closed__38_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__38_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__38_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoRepeat___closed__38_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__38_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoRepeat___closed__38_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__38_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__37_value)
                as *mut crate::leanh::LeanObject,
            3719295731128710746 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoRepeat___closed__39_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 33, 0],
    };
static mut l_Lean_Elab_Do_elabDoRepeat___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__39_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__1_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__2_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 108, 97, 98, 68, 111, 82, 101, 112, 101, 97, 116, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__1_value) as *mut crate::leanh::LeanObject,102172329646148436 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__2_value) as *mut crate::leanh::LeanObject,11659378638883804225 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___closed__0_value: crate::leanh::LeanStringObject<607> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 607, m_capacity: 607, m_length: 604, m_data: [66, 117, 105, 108, 116, 105, 110, 32, 100, 111, 45, 101, 108, 101, 109, 101, 110, 116, 32, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 32, 102, 111, 114, 32, 96, 114, 101, 112, 101, 97, 116, 96, 32, 40, 115, 121, 110, 116, 97, 120, 32, 107, 105, 110, 100, 32, 96, 76, 101, 97, 110, 46, 80, 97, 114, 115, 101, 114, 46, 84, 101, 114, 109, 46, 100, 111, 82, 101, 112, 101, 97, 116, 96, 41, 46, 10, 10, 69, 120, 112, 97, 110, 100, 115, 32, 116, 111, 32, 96, 102, 111, 114, 32, 95, 32, 105, 110, 32, 76, 111, 111, 112, 46, 109, 107, 32, 100, 111, 32, 46, 46, 46, 96, 46, 32, 87, 104, 101, 110, 32, 116, 104, 101, 32, 98, 111, 100, 121, 32, 99, 97, 110, 110, 111, 116, 32, 96, 98, 114, 101, 97, 107, 96, 44, 32, 116, 104, 101, 32, 108, 111, 111, 112, 39, 115, 32, 111, 119, 110, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 10, 116, 121, 112, 101, 32, 105, 115, 32, 102, 105, 120, 101, 100, 32, 116, 111, 32, 96, 80, 85, 110, 105, 116, 96, 44, 32, 121, 101, 116, 32, 116, 104, 101, 32, 115, 117, 114, 114, 111, 117, 110, 100, 105, 110, 103, 32, 100, 111, 32, 98, 108, 111, 99, 107, 32, 109, 97, 121, 32, 114, 101, 113, 117, 105, 114, 101, 32, 97, 32, 100, 105, 102, 102, 101, 114, 101, 110, 116, 32, 114, 101, 115, 117, 108, 116, 32, 116, 121, 112, 101, 59, 10, 119, 101, 32, 97, 112, 112, 101, 110, 100, 32, 97, 110, 32, 96, 117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 33, 96, 32, 115, 111, 32, 116, 104, 101, 32, 99, 111, 110, 116, 105, 110, 117, 97, 116, 105, 111, 110, 32, 104, 97, 115, 32, 97, 32, 112, 111, 108, 121, 109, 111, 114, 112, 104, 105, 99, 32, 118, 97, 108, 117, 101, 32, 111, 102, 32, 97, 110, 121, 32, 116, 121, 112, 101, 46, 32, 84, 104, 101, 10, 96, 117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 33, 96, 32, 105, 115, 32, 110, 101, 118, 101, 114, 32, 97, 99, 116, 117, 97, 108, 108, 121, 32, 101, 120, 101, 99, 117, 116, 101, 100, 32, 40, 116, 104, 101, 32, 108, 111, 111, 112, 32, 110, 101, 118, 101, 114, 32, 116, 101, 114, 109, 105, 110, 97, 116, 101, 115, 32, 110, 111, 114, 109, 97, 108, 108, 121, 41, 44, 32, 97, 110, 100, 32, 97, 110, 121, 10, 100, 101, 97, 100, 45, 99, 111, 100, 101, 32, 119, 97, 114, 110, 105, 110, 103, 32, 116, 104, 97, 116, 32, 102, 105, 114, 101, 115, 32, 111, 110, 32, 116, 104, 101, 32, 115, 117, 114, 114, 111, 117, 110, 100, 105, 110, 103, 32, 99, 111, 110, 116, 105, 110, 117, 97, 116, 105, 111, 110, 32, 105, 115, 32, 97, 99, 116, 105, 111, 110, 97, 98, 108, 101, 32, 226, 128, 148, 32, 116, 104, 101, 32, 117, 115, 101, 114, 32, 99, 97, 110, 10, 114, 101, 109, 111, 118, 101, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 99, 111, 100, 101, 32, 119, 105, 116, 104, 111, 117, 116, 32, 98, 114, 101, 97, 107, 105, 110, 103, 32, 116, 104, 101, 32, 100, 111, 32, 98, 108, 111, 99, 107, 39, 115, 32, 116, 121, 112, 101, 46, 10, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoWhile___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [100, 111, 87, 104, 105, 108, 101, 0],
    };
static mut l_Lean_Elab_Do_expandDoWhile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_expandDoWhile___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_expandDoWhile___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_expandDoWhile___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_expandDoWhile___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15578602960905705005 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_expandDoWhile___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoWhile___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [114, 101, 112, 101, 97, 116, 0],
    };
static mut l_Lean_Elab_Do_expandDoWhile___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoWhile___closed__3_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [100, 111, 73, 102, 0],
    };
static mut l_Lean_Elab_Do_expandDoWhile___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_expandDoWhile___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_expandDoWhile___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_expandDoWhile___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_expandDoWhile___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__3_value)
                as *mut crate::leanh::LeanObject,
            6082561497774213 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_expandDoWhile___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoWhile___closed__5_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [105, 102, 0],
    };
static mut l_Lean_Elab_Do_expandDoWhile___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoWhile___closed__6_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [116, 104, 101, 110, 0],
    };
static mut l_Lean_Elab_Do_expandDoWhile___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoWhile___closed__7_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [101, 108, 115, 101, 0],
    };
static mut l_Lean_Elab_Do_expandDoWhile___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoWhile___closed__8_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [100, 111, 66, 114, 101, 97, 107, 0],
    };
static mut l_Lean_Elab_Do_expandDoWhile___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_expandDoWhile___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_expandDoWhile___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__9_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_expandDoWhile___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__9_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_expandDoWhile___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__9_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__8_value)
                as *mut crate::leanh::LeanObject,
            2827323648879505508 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_expandDoWhile___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoWhile___closed__10_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [98, 114, 101, 97, 107, 0],
    };
static mut l_Lean_Elab_Do_expandDoWhile___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoWhile___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 120, 112, 97, 110, 100, 68, 111, 87, 104, 105, 108, 101, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__1_value) as *mut crate::leanh::LeanObject,102172329646148436 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__0_value) as *mut crate::leanh::LeanObject,16793347916682396505 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoRepeatUntil___closed__0_value: crate::leanh::LeanStringObject<
    14,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        100, 111, 82, 101, 112, 101, 97, 116, 85, 110, 116, 105, 108, 0,
    ],
};
static mut l_Lean_Elab_Do_expandDoRepeatUntil___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoRepeatUntil___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoRepeatUntil___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16667460056651402030 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_expandDoRepeatUntil___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoRepeatUntil___closed__2_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [100, 111, 73, 102, 80, 114, 111, 112, 0],
    };
static mut l_Lean_Elab_Do_expandDoRepeatUntil___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoRepeatUntil___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoRepeatUntil___closed__2_value)
                as *mut crate::leanh::LeanObject,
            10892447550847226679 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_expandDoRepeatUntil___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__0_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 120, 112, 97, 110, 100, 68, 111, 82, 101, 112, 101, 97, 116, 85, 110, 116, 105, 108, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoRepeat___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__1_value) as *mut crate::leanh::LeanObject,102172329646148436 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__0_value) as *mut crate::leanh::LeanObject,4221256740692014021 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_848_ = crate::leanh::lean_box(0);
    v___x_849_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_850_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_850_, 0, v___x_849_);
    crate::leanh::lean_ctor_set(v___x_850_, 1, v___x_848_);
    return v___x_850_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_852_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0);
    v___x_853_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_853_, 0, v___x_852_);
    return v___x_853_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___boxed(
    mut v___y_854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_855_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
    return v_res_855_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0(
    mut v_00_u03b1_856_: *mut crate::leanh::LeanObject,
    mut v___y_857_: *mut crate::leanh::LeanObject,
    mut v___y_858_: *mut crate::leanh::LeanObject,
    mut v___y_859_: *mut crate::leanh::LeanObject,
    mut v___y_860_: *mut crate::leanh::LeanObject,
    mut v___y_861_: *mut crate::leanh::LeanObject,
    mut v___y_862_: *mut crate::leanh::LeanObject,
    mut v___y_863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_865_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
    return v___x_865_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___boxed(
    mut v_00_u03b1_866_: *mut crate::leanh::LeanObject,
    mut v___y_867_: *mut crate::leanh::LeanObject,
    mut v___y_868_: *mut crate::leanh::LeanObject,
    mut v___y_869_: *mut crate::leanh::LeanObject,
    mut v___y_870_: *mut crate::leanh::LeanObject,
    mut v___y_871_: *mut crate::leanh::LeanObject,
    mut v___y_872_: *mut crate::leanh::LeanObject,
    mut v___y_873_: *mut crate::leanh::LeanObject,
    mut v___y_874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_875_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0(
        v_00_u03b1_866_,
        v___y_867_,
        v___y_868_,
        v___y_869_,
        v___y_870_,
        v___y_871_,
        v___y_872_,
        v___y_873_,
    );
    crate::leanh::lean_dec(v___y_873_);
    crate::leanh::lean_dec_ref(v___y_872_);
    crate::leanh::lean_dec(v___y_871_);
    crate::leanh::lean_dec_ref(v___y_870_);
    crate::leanh::lean_dec(v___y_869_);
    crate::leanh::lean_dec_ref(v___y_868_);
    crate::leanh::lean_dec_ref(v___y_867_);
    return v_res_875_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoRepeat___lam__0(
    mut v_expanded_876_: *mut crate::leanh::LeanObject,
    mut v_dec_877_: *mut crate::leanh::LeanObject,
    mut v___x_878_: u8,
    mut v___y_879_: *mut crate::leanh::LeanObject,
    mut v___y_880_: *mut crate::leanh::LeanObject,
    mut v___y_881_: *mut crate::leanh::LeanObject,
    mut v___y_882_: *mut crate::leanh::LeanObject,
    mut v___y_883_: *mut crate::leanh::LeanObject,
    mut v___y_884_: *mut crate::leanh::LeanObject,
    mut v___y_885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_899_: u8 = 0;
    let mut v_cancelTk_x3f_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_901_: u8 = 0;
    let mut v_inheritedTraceOptions_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_887_ = crate::leanh::lean_ctor_get(v___y_884_, 0);
    v_fileMap_888_ = crate::leanh::lean_ctor_get(v___y_884_, 1);
    v_options_889_ = crate::leanh::lean_ctor_get(v___y_884_, 2);
    v_currRecDepth_890_ = crate::leanh::lean_ctor_get(v___y_884_, 3);
    v_maxRecDepth_891_ = crate::leanh::lean_ctor_get(v___y_884_, 4);
    v_ref_892_ = crate::leanh::lean_ctor_get(v___y_884_, 5);
    v_currNamespace_893_ = crate::leanh::lean_ctor_get(v___y_884_, 6);
    v_openDecls_894_ = crate::leanh::lean_ctor_get(v___y_884_, 7);
    v_initHeartbeats_895_ = crate::leanh::lean_ctor_get(v___y_884_, 8);
    v_maxHeartbeats_896_ = crate::leanh::lean_ctor_get(v___y_884_, 9);
    v_quotContext_897_ = crate::leanh::lean_ctor_get(v___y_884_, 10);
    v_currMacroScope_898_ = crate::leanh::lean_ctor_get(v___y_884_, 11);
    v_diag_899_ = crate::leanh::lean_ctor_get_uint8(
        v___y_884_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_900_ = crate::leanh::lean_ctor_get(v___y_884_, 12);
    v_suppressElabErrors_901_ = crate::leanh::lean_ctor_get_uint8(
        v___y_884_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_902_ = crate::leanh::lean_ctor_get(v___y_884_, 13);
    v_ref_903_ = l_Lean_replaceRef(v_expanded_876_, v_ref_892_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_902_);
    crate::leanh::lean_inc(v_cancelTk_x3f_900_);
    crate::leanh::lean_inc(v_currMacroScope_898_);
    crate::leanh::lean_inc(v_quotContext_897_);
    crate::leanh::lean_inc(v_maxHeartbeats_896_);
    crate::leanh::lean_inc(v_initHeartbeats_895_);
    crate::leanh::lean_inc(v_openDecls_894_);
    crate::leanh::lean_inc(v_currNamespace_893_);
    crate::leanh::lean_inc(v_maxRecDepth_891_);
    crate::leanh::lean_inc(v_currRecDepth_890_);
    crate::leanh::lean_inc_ref(v_options_889_);
    crate::leanh::lean_inc_ref(v_fileMap_888_);
    crate::leanh::lean_inc_ref(v_fileName_887_);
    v___x_904_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_904_, 0, v_fileName_887_);
    crate::leanh::lean_ctor_set(v___x_904_, 1, v_fileMap_888_);
    crate::leanh::lean_ctor_set(v___x_904_, 2, v_options_889_);
    crate::leanh::lean_ctor_set(v___x_904_, 3, v_currRecDepth_890_);
    crate::leanh::lean_ctor_set(v___x_904_, 4, v_maxRecDepth_891_);
    crate::leanh::lean_ctor_set(v___x_904_, 5, v_ref_903_);
    crate::leanh::lean_ctor_set(v___x_904_, 6, v_currNamespace_893_);
    crate::leanh::lean_ctor_set(v___x_904_, 7, v_openDecls_894_);
    crate::leanh::lean_ctor_set(v___x_904_, 8, v_initHeartbeats_895_);
    crate::leanh::lean_ctor_set(v___x_904_, 9, v_maxHeartbeats_896_);
    crate::leanh::lean_ctor_set(v___x_904_, 10, v_quotContext_897_);
    crate::leanh::lean_ctor_set(v___x_904_, 11, v_currMacroScope_898_);
    crate::leanh::lean_ctor_set(v___x_904_, 12, v_cancelTk_x3f_900_);
    crate::leanh::lean_ctor_set(v___x_904_, 13, v_inheritedTraceOptions_902_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_904_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_899_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_904_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_901_,
    );
    v___x_905_ = l_Lean_Elab_Do_elabDoElem(
        v_expanded_876_,
        v_dec_877_,
        v___x_878_,
        v___y_879_,
        v___y_880_,
        v___y_881_,
        v___y_882_,
        v___y_883_,
        v___x_904_,
        v___y_885_,
    );
    crate::leanh::lean_dec_ref_known(v___x_904_, 14);
    return v___x_905_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoRepeat___lam__0___boxed(
    mut v_expanded_906_: *mut crate::leanh::LeanObject,
    mut v_dec_907_: *mut crate::leanh::LeanObject,
    mut v___x_908_: *mut crate::leanh::LeanObject,
    mut v___y_909_: *mut crate::leanh::LeanObject,
    mut v___y_910_: *mut crate::leanh::LeanObject,
    mut v___y_911_: *mut crate::leanh::LeanObject,
    mut v___y_912_: *mut crate::leanh::LeanObject,
    mut v___y_913_: *mut crate::leanh::LeanObject,
    mut v___y_914_: *mut crate::leanh::LeanObject,
    mut v___y_915_: *mut crate::leanh::LeanObject,
    mut v___y_916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_15415__boxed_917_: u8 = 0;
    let mut v_res_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_15415__boxed_917_ = (crate::leanh::lean_unbox(v___x_908_) as u8);
    v_res_918_ = l_Lean_Elab_Do_elabDoRepeat___lam__0(
        v_expanded_906_,
        v_dec_907_,
        v___x_15415__boxed_917_,
        v___y_909_,
        v___y_910_,
        v___y_911_,
        v___y_912_,
        v___y_913_,
        v___y_914_,
        v___y_915_,
    );
    crate::leanh::lean_dec(v___y_915_);
    crate::leanh::lean_dec_ref(v___y_914_);
    crate::leanh::lean_dec(v___y_913_);
    crate::leanh::lean_dec_ref(v___y_912_);
    crate::leanh::lean_dec(v___y_911_);
    crate::leanh::lean_dec_ref(v___y_910_);
    crate::leanh::lean_dec_ref(v___y_909_);
    return v_res_918_;
}
pub unsafe fn l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0(
    mut v_x_919_: *mut crate::leanh::LeanObject,
    mut v___y_920_: *mut crate::leanh::LeanObject,
    mut v___y_921_: *mut crate::leanh::LeanObject,
    mut v___y_922_: *mut crate::leanh::LeanObject,
    mut v___y_923_: *mut crate::leanh::LeanObject,
    mut v___y_924_: *mut crate::leanh::LeanObject,
    mut v___y_925_: *mut crate::leanh::LeanObject,
    mut v___y_926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v___y_920_);
    v___x_928_ = crate::leanh::lean_apply_8(
        v_x_919_,
        v___y_920_,
        v___y_921_,
        v___y_922_,
        v___y_923_,
        v___y_924_,
        v___y_925_,
        v___y_926_,
        crate::leanh::lean_box(0),
    );
    return v___x_928_;
}
pub unsafe fn l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0___boxed(
    mut v_x_929_: *mut crate::leanh::LeanObject,
    mut v___y_930_: *mut crate::leanh::LeanObject,
    mut v___y_931_: *mut crate::leanh::LeanObject,
    mut v___y_932_: *mut crate::leanh::LeanObject,
    mut v___y_933_: *mut crate::leanh::LeanObject,
    mut v___y_934_: *mut crate::leanh::LeanObject,
    mut v___y_935_: *mut crate::leanh::LeanObject,
    mut v___y_936_: *mut crate::leanh::LeanObject,
    mut v___y_937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_938_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0(v_x_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
    crate::leanh::lean_dec_ref(v___y_930_);
    return v_res_938_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(
    mut v___y_939_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_940_: *mut crate::leanh::LeanObject,
    mut v___y_941_: *mut crate::leanh::LeanObject,
    mut v___y_942_: *mut crate::leanh::LeanObject,
    mut v___y_943_: *mut crate::leanh::LeanObject,
    mut v___y_944_: *mut crate::leanh::LeanObject,
    mut v___y_945_: *mut crate::leanh::LeanObject,
    mut v_a_946_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_956_: u8 = 0;
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_969_: u8 = 0;
    let mut v_enabled_970_: u8 = 0;
    let mut v_assignment_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_975_: u8 = 0;
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_988_: u8 = 0;
    let mut v_unused_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_990_: u8 = 0;
    let mut v_isSharedCheck_991_: u8 = 0;
    let mut v_a_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_995_: u8 = 0;
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_999_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_949_ = lean_st_ref_get(v___y_939_);
                v_infoState_950_ = crate::leanh::lean_ctor_get(v___x_949_, 7);
                crate::leanh::lean_inc_ref(v_infoState_950_);
                crate::leanh::lean_dec(v___x_949_);
                v_trees_951_ = crate::leanh::lean_ctor_get(v_infoState_950_, 2);
                crate::leanh::lean_inc_ref(v_trees_951_);
                crate::leanh::lean_dec_ref(v_infoState_950_);
                crate::leanh::lean_inc(v___y_939_);
                crate::leanh::lean_inc_ref(v___y_945_);
                crate::leanh::lean_inc(v___y_944_);
                crate::leanh::lean_inc_ref(v___y_943_);
                crate::leanh::lean_inc(v___y_942_);
                crate::leanh::lean_inc_ref(v___y_941_);
                v___x_952_ = crate::leanh::lean_apply_8(
                    v_mkInfoTree_940_,
                    v_trees_951_,
                    v___y_941_,
                    v___y_942_,
                    v___y_943_,
                    v___y_944_,
                    v___y_945_,
                    v___y_939_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_952_) == 0 {
                    v_a_953_ = crate::leanh::lean_ctor_get(v___x_952_, 0);
                    v_isSharedCheck_991_ = (!crate::leanh::lean_is_exclusive(v___x_952_)) as u8;
                    if v_isSharedCheck_991_ == 0 {
                        v___x_955_ = v___x_952_;
                        v_isShared_956_ = v_isSharedCheck_991_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_953_);
                        crate::leanh::lean_dec(v___x_952_);
                        v___x_955_ = crate::leanh::lean_box(0);
                        v_isShared_956_ = v_isSharedCheck_991_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_946_);
                    v_a_992_ = crate::leanh::lean_ctor_get(v___x_952_, 0);
                    v_isSharedCheck_999_ = (!crate::leanh::lean_is_exclusive(v___x_952_)) as u8;
                    if v_isSharedCheck_999_ == 0 {
                        v___x_994_ = v___x_952_;
                        v_isShared_995_ = v_isSharedCheck_999_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_992_);
                        crate::leanh::lean_dec(v___x_952_);
                        v___x_994_ = crate::leanh::lean_box(0);
                        v_isShared_995_ = v_isSharedCheck_999_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_957_ = lean_st_ref_take(v___y_939_);
                v_infoState_958_ = crate::leanh::lean_ctor_get(v___x_957_, 7);
                v_env_959_ = crate::leanh::lean_ctor_get(v___x_957_, 0);
                v_nextMacroScope_960_ = crate::leanh::lean_ctor_get(v___x_957_, 1);
                v_ngen_961_ = crate::leanh::lean_ctor_get(v___x_957_, 2);
                v_auxDeclNGen_962_ = crate::leanh::lean_ctor_get(v___x_957_, 3);
                v_traceState_963_ = crate::leanh::lean_ctor_get(v___x_957_, 4);
                v_cache_964_ = crate::leanh::lean_ctor_get(v___x_957_, 5);
                v_messages_965_ = crate::leanh::lean_ctor_get(v___x_957_, 6);
                v_snapshotTasks_966_ = crate::leanh::lean_ctor_get(v___x_957_, 8);
                v_isSharedCheck_990_ = (!crate::leanh::lean_is_exclusive(v___x_957_)) as u8;
                if v_isSharedCheck_990_ == 0 {
                    v___x_968_ = v___x_957_;
                    v_isShared_969_ = v_isSharedCheck_990_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_966_);
                    crate::leanh::lean_inc(v_infoState_958_);
                    crate::leanh::lean_inc(v_messages_965_);
                    crate::leanh::lean_inc(v_cache_964_);
                    crate::leanh::lean_inc(v_traceState_963_);
                    crate::leanh::lean_inc(v_auxDeclNGen_962_);
                    crate::leanh::lean_inc(v_ngen_961_);
                    crate::leanh::lean_inc(v_nextMacroScope_960_);
                    crate::leanh::lean_inc(v_env_959_);
                    crate::leanh::lean_dec(v___x_957_);
                    v___x_968_ = crate::leanh::lean_box(0);
                    v_isShared_969_ = v_isSharedCheck_990_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_970_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_958_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_971_ = crate::leanh::lean_ctor_get(v_infoState_958_, 0);
                v_lazyAssignment_972_ = crate::leanh::lean_ctor_get(v_infoState_958_, 1);
                v_isSharedCheck_988_ = (!crate::leanh::lean_is_exclusive(v_infoState_958_)) as u8;
                if v_isSharedCheck_988_ == 0 {
                    v_unused_989_ = crate::leanh::lean_ctor_get(v_infoState_958_, 2);
                    crate::leanh::lean_dec(v_unused_989_);
                    v___x_974_ = v_infoState_958_;
                    v_isShared_975_ = v_isSharedCheck_988_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_972_);
                    crate::leanh::lean_inc(v_assignment_971_);
                    crate::leanh::lean_dec(v_infoState_958_);
                    v___x_974_ = crate::leanh::lean_box(0);
                    v_isShared_975_ = v_isSharedCheck_988_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_976_ = l_Lean_PersistentArray_push___redArg(v_a_946_, v_a_953_);
                if v_isShared_975_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_974_, 2, v___x_976_);
                    v___x_978_ = v___x_974_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_987_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_987_, 0, v_assignment_971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_987_, 1, v_lazyAssignment_972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_987_, 2, v___x_976_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_987_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_970_,
                    );
                    v___x_978_ = v_reuseFailAlloc_987_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_969_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_968_, 7, v___x_978_);
                    v___x_980_ = v___x_968_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_986_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_986_, 0, v_env_959_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_986_, 1, v_nextMacroScope_960_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_986_, 2, v_ngen_961_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_986_, 3, v_auxDeclNGen_962_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_986_, 4, v_traceState_963_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_986_, 5, v_cache_964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_986_, 6, v_messages_965_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_986_, 7, v___x_978_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_986_, 8, v_snapshotTasks_966_);
                    v___x_980_ = v_reuseFailAlloc_986_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_981_ = lean_st_ref_set(v___y_939_, v___x_980_);
                v___x_982_ = crate::leanh::lean_box(0);
                if v_isShared_956_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_955_, 0, v___x_982_);
                    v___x_984_ = v___x_955_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_985_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
                    v___x_984_ = v_reuseFailAlloc_985_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_984_;
            }
            7 => {
                if v_isShared_995_ == 0 {
                    v___x_997_ = v___x_994_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_998_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
                    v___x_997_ = v_reuseFailAlloc_998_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_997_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0___boxed(
    mut v___y_1000_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_1001_: *mut crate::leanh::LeanObject,
    mut v___y_1002_: *mut crate::leanh::LeanObject,
    mut v___y_1003_: *mut crate::leanh::LeanObject,
    mut v___y_1004_: *mut crate::leanh::LeanObject,
    mut v___y_1005_: *mut crate::leanh::LeanObject,
    mut v___y_1006_: *mut crate::leanh::LeanObject,
    mut v_a_1007_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1008_: *mut crate::leanh::LeanObject,
    mut v___y_1009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1010_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(v___y_1000_, v_mkInfoTree_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v_a_1007_, v_a_x3f_1008_);
    crate::leanh::lean_dec(v_a_x3f_1008_);
    crate::leanh::lean_dec_ref(v___y_1006_);
    crate::leanh::lean_dec(v___y_1005_);
    crate::leanh::lean_dec_ref(v___y_1004_);
    crate::leanh::lean_dec(v___y_1003_);
    crate::leanh::lean_dec_ref(v___y_1002_);
    crate::leanh::lean_dec(v___y_1000_);
    return v_res_1010_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1011_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1012_ = lean_mk_empty_array_with_capacity(v___x_1011_);
    v___x_1013_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1013_, 0, v___x_1012_);
    return v___x_1013_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1014_: usize = 0;
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1014_ = 5usize;
    v___x_1015_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1016_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1017_ = lean_mk_empty_array_with_capacity(v___x_1016_);
    v___x_1018_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0);
    v___x_1019_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1019_, 0, v___x_1018_);
    crate::leanh::lean_ctor_set(v___x_1019_, 1, v___x_1017_);
    crate::leanh::lean_ctor_set(v___x_1019_, 2, v___x_1015_);
    crate::leanh::lean_ctor_set(v___x_1019_, 3, v___x_1015_);
    crate::leanh::lean_ctor_set_usize(v___x_1019_, 4, v___x_1014_);
    return v___x_1019_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(
    mut v___y_1020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1037_: u8 = 0;
    let mut v_enabled_1038_: u8 = 0;
    let mut v_assignment_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1043_: u8 = 0;
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1053_: u8 = 0;
    let mut v_unused_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1022_ = lean_st_ref_get(v___y_1020_);
                v_infoState_1023_ = crate::leanh::lean_ctor_get(v___x_1022_, 7);
                crate::leanh::lean_inc_ref(v_infoState_1023_);
                crate::leanh::lean_dec(v___x_1022_);
                v_trees_1024_ = crate::leanh::lean_ctor_get(v_infoState_1023_, 2);
                crate::leanh::lean_inc_ref(v_trees_1024_);
                crate::leanh::lean_dec_ref(v_infoState_1023_);
                v___x_1025_ = lean_st_ref_take(v___y_1020_);
                v_infoState_1026_ = crate::leanh::lean_ctor_get(v___x_1025_, 7);
                v_env_1027_ = crate::leanh::lean_ctor_get(v___x_1025_, 0);
                v_nextMacroScope_1028_ = crate::leanh::lean_ctor_get(v___x_1025_, 1);
                v_ngen_1029_ = crate::leanh::lean_ctor_get(v___x_1025_, 2);
                v_auxDeclNGen_1030_ = crate::leanh::lean_ctor_get(v___x_1025_, 3);
                v_traceState_1031_ = crate::leanh::lean_ctor_get(v___x_1025_, 4);
                v_cache_1032_ = crate::leanh::lean_ctor_get(v___x_1025_, 5);
                v_messages_1033_ = crate::leanh::lean_ctor_get(v___x_1025_, 6);
                v_snapshotTasks_1034_ = crate::leanh::lean_ctor_get(v___x_1025_, 8);
                v_isSharedCheck_1055_ = (!crate::leanh::lean_is_exclusive(v___x_1025_)) as u8;
                if v_isSharedCheck_1055_ == 0 {
                    v___x_1036_ = v___x_1025_;
                    v_isShared_1037_ = v_isSharedCheck_1055_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1034_);
                    crate::leanh::lean_inc(v_infoState_1026_);
                    crate::leanh::lean_inc(v_messages_1033_);
                    crate::leanh::lean_inc(v_cache_1032_);
                    crate::leanh::lean_inc(v_traceState_1031_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1030_);
                    crate::leanh::lean_inc(v_ngen_1029_);
                    crate::leanh::lean_inc(v_nextMacroScope_1028_);
                    crate::leanh::lean_inc(v_env_1027_);
                    crate::leanh::lean_dec(v___x_1025_);
                    v___x_1036_ = crate::leanh::lean_box(0);
                    v_isShared_1037_ = v_isSharedCheck_1055_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_1038_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_1026_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_1039_ = crate::leanh::lean_ctor_get(v_infoState_1026_, 0);
                v_lazyAssignment_1040_ = crate::leanh::lean_ctor_get(v_infoState_1026_, 1);
                v_isSharedCheck_1053_ = (!crate::leanh::lean_is_exclusive(v_infoState_1026_)) as u8;
                if v_isSharedCheck_1053_ == 0 {
                    v_unused_1054_ = crate::leanh::lean_ctor_get(v_infoState_1026_, 2);
                    crate::leanh::lean_dec(v_unused_1054_);
                    v___x_1042_ = v_infoState_1026_;
                    v_isShared_1043_ = v_isSharedCheck_1053_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_1040_);
                    crate::leanh::lean_inc(v_assignment_1039_);
                    crate::leanh::lean_dec(v_infoState_1026_);
                    v___x_1042_ = crate::leanh::lean_box(0);
                    v_isShared_1043_ = v_isSharedCheck_1053_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1044_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1);
                if v_isShared_1043_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1042_, 2, v___x_1044_);
                    v___x_1046_ = v___x_1042_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1052_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_assignment_1039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_lazyAssignment_1040_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1052_, 2, v___x_1044_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1052_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_1038_,
                    );
                    v___x_1046_ = v_reuseFailAlloc_1052_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1037_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1036_, 7, v___x_1046_);
                    v___x_1048_ = v___x_1036_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1051_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_env_1027_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_nextMacroScope_1028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1051_, 2, v_ngen_1029_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1051_, 3, v_auxDeclNGen_1030_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1051_, 4, v_traceState_1031_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1051_, 5, v_cache_1032_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1051_, 6, v_messages_1033_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1051_, 7, v___x_1046_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1051_, 8, v_snapshotTasks_1034_);
                    v___x_1048_ = v_reuseFailAlloc_1051_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1049_ = lean_st_ref_set(v___y_1020_, v___x_1048_);
                v___x_1050_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1050_, 0, v_trees_1024_);
                return v___x_1050_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___boxed(
    mut v___y_1056_: *mut crate::leanh::LeanObject,
    mut v___y_1057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1058_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_1056_);
    crate::leanh::lean_dec(v___y_1056_);
    return v_res_1058_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(
    mut v_x_1059_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_1060_: *mut crate::leanh::LeanObject,
    mut v___y_1061_: *mut crate::leanh::LeanObject,
    mut v___y_1062_: *mut crate::leanh::LeanObject,
    mut v___y_1063_: *mut crate::leanh::LeanObject,
    mut v___y_1064_: *mut crate::leanh::LeanObject,
    mut v___y_1065_: *mut crate::leanh::LeanObject,
    mut v___y_1066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_1070_: u8 = 0;
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1078_: u8 = 0;
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1084_: u8 = 0;
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1088_: u8 = 0;
    let mut v_unused_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1093_: u8 = 0;
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1097_: u8 = 0;
    let mut v_reuseFailAlloc_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1099_: u8 = 0;
    let mut v_a_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1105_: u8 = 0;
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1109_: u8 = 0;
    let mut v_unused_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1114_: u8 = 0;
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1118_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1068_ = lean_st_ref_get(v___y_1066_);
                v_infoState_1069_ = crate::leanh::lean_ctor_get(v___x_1068_, 7);
                crate::leanh::lean_inc_ref(v_infoState_1069_);
                crate::leanh::lean_dec(v___x_1068_);
                v_enabled_1070_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_1069_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_1069_);
                if v_enabled_1070_ == 0 {
                    crate::leanh::lean_dec_ref(v_mkInfoTree_1060_);
                    crate::leanh::lean_inc(v___y_1066_);
                    crate::leanh::lean_inc_ref(v___y_1065_);
                    crate::leanh::lean_inc(v___y_1064_);
                    crate::leanh::lean_inc_ref(v___y_1063_);
                    crate::leanh::lean_inc(v___y_1062_);
                    crate::leanh::lean_inc_ref(v___y_1061_);
                    v___x_1071_ = crate::leanh::lean_apply_7(
                        v_x_1059_,
                        v___y_1061_,
                        v___y_1062_,
                        v___y_1063_,
                        v___y_1064_,
                        v___y_1065_,
                        v___y_1066_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_1071_;
                } else {
                    v___x_1072_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_1066_);
                    v_a_1073_ = crate::leanh::lean_ctor_get(v___x_1072_, 0);
                    crate::leanh::lean_inc(v_a_1073_);
                    crate::leanh::lean_dec_ref(v___x_1072_);
                    crate::leanh::lean_inc(v___y_1066_);
                    crate::leanh::lean_inc_ref(v___y_1065_);
                    crate::leanh::lean_inc(v___y_1064_);
                    crate::leanh::lean_inc_ref(v___y_1063_);
                    crate::leanh::lean_inc(v___y_1062_);
                    crate::leanh::lean_inc_ref(v___y_1061_);
                    v_r_1074_ = crate::leanh::lean_apply_7(
                        v_x_1059_,
                        v___y_1061_,
                        v___y_1062_,
                        v___y_1063_,
                        v___y_1064_,
                        v___y_1065_,
                        v___y_1066_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v_r_1074_) == 0 {
                        v_a_1075_ = crate::leanh::lean_ctor_get(v_r_1074_, 0);
                        v_isSharedCheck_1099_ = (!crate::leanh::lean_is_exclusive(v_r_1074_)) as u8;
                        if v_isSharedCheck_1099_ == 0 {
                            v___x_1077_ = v_r_1074_;
                            v_isShared_1078_ = v_isSharedCheck_1099_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1075_);
                            crate::leanh::lean_dec(v_r_1074_);
                            v___x_1077_ = crate::leanh::lean_box(0);
                            v_isShared_1078_ = v_isSharedCheck_1099_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1100_ = crate::leanh::lean_ctor_get(v_r_1074_, 0);
                        crate::leanh::lean_inc(v_a_1100_);
                        crate::leanh::lean_dec_ref_known(v_r_1074_, 1);
                        v___x_1101_ = crate::leanh::lean_box(0);
                        v___x_1102_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(v___y_1066_, v_mkInfoTree_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v_a_1073_, v___x_1101_);
                        if crate::leanh::lean_obj_tag(v___x_1102_) == 0 {
                            v_isSharedCheck_1109_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1102_)) as u8;
                            if v_isSharedCheck_1109_ == 0 {
                                v_unused_1110_ = crate::leanh::lean_ctor_get(v___x_1102_, 0);
                                crate::leanh::lean_dec(v_unused_1110_);
                                v___x_1104_ = v___x_1102_;
                                v_isShared_1105_ = v_isSharedCheck_1109_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1102_);
                                v___x_1104_ = crate::leanh::lean_box(0);
                                v_isShared_1105_ = v_isSharedCheck_1109_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1100_);
                            v_a_1111_ = crate::leanh::lean_ctor_get(v___x_1102_, 0);
                            v_isSharedCheck_1118_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1102_)) as u8;
                            if v_isSharedCheck_1118_ == 0 {
                                v___x_1113_ = v___x_1102_;
                                v_isShared_1114_ = v_isSharedCheck_1118_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1111_);
                                crate::leanh::lean_dec(v___x_1102_);
                                v___x_1113_ = crate::leanh::lean_box(0);
                                v_isShared_1114_ = v_isSharedCheck_1118_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_1075_);
                if v_isShared_1078_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1077_, 1);
                    v___x_1080_ = v___x_1077_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1098_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1075_);
                    v___x_1080_ = v_reuseFailAlloc_1098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1081_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(v___y_1066_, v_mkInfoTree_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v_a_1073_, v___x_1080_);
                crate::leanh::lean_dec_ref(v___x_1080_);
                if crate::leanh::lean_obj_tag(v___x_1081_) == 0 {
                    v_isSharedCheck_1088_ = (!crate::leanh::lean_is_exclusive(v___x_1081_)) as u8;
                    if v_isSharedCheck_1088_ == 0 {
                        v_unused_1089_ = crate::leanh::lean_ctor_get(v___x_1081_, 0);
                        crate::leanh::lean_dec(v_unused_1089_);
                        v___x_1083_ = v___x_1081_;
                        v_isShared_1084_ = v_isSharedCheck_1088_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1081_);
                        v___x_1083_ = crate::leanh::lean_box(0);
                        v_isShared_1084_ = v_isSharedCheck_1088_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1075_);
                    v_a_1090_ = crate::leanh::lean_ctor_get(v___x_1081_, 0);
                    v_isSharedCheck_1097_ = (!crate::leanh::lean_is_exclusive(v___x_1081_)) as u8;
                    if v_isSharedCheck_1097_ == 0 {
                        v___x_1092_ = v___x_1081_;
                        v_isShared_1093_ = v_isSharedCheck_1097_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1090_);
                        crate::leanh::lean_dec(v___x_1081_);
                        v___x_1092_ = crate::leanh::lean_box(0);
                        v_isShared_1093_ = v_isSharedCheck_1097_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1084_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1083_, 0, v_a_1075_);
                    v___x_1086_ = v___x_1083_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1087_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1075_);
                    v___x_1086_ = v_reuseFailAlloc_1087_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1086_;
            }
            5 => {
                if v_isShared_1093_ == 0 {
                    v___x_1095_ = v___x_1092_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1096_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
                    v___x_1095_ = v_reuseFailAlloc_1096_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1095_;
            }
            7 => {
                if v_isShared_1105_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1104_, 1);
                    crate::leanh::lean_ctor_set(v___x_1104_, 0, v_a_1100_);
                    v___x_1107_ = v___x_1104_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1108_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1100_);
                    v___x_1107_ = v_reuseFailAlloc_1108_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1107_;
            }
            9 => {
                if v_isShared_1114_ == 0 {
                    v___x_1116_ = v___x_1113_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1117_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
                    v___x_1116_ = v_reuseFailAlloc_1117_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1116_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_x_1119_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_1120_: *mut crate::leanh::LeanObject,
    mut v___y_1121_: *mut crate::leanh::LeanObject,
    mut v___y_1122_: *mut crate::leanh::LeanObject,
    mut v___y_1123_: *mut crate::leanh::LeanObject,
    mut v___y_1124_: *mut crate::leanh::LeanObject,
    mut v___y_1125_: *mut crate::leanh::LeanObject,
    mut v___y_1126_: *mut crate::leanh::LeanObject,
    mut v___y_1127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1128_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_1119_, v_mkInfoTree_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
    crate::leanh::lean_dec(v___y_1126_);
    crate::leanh::lean_dec_ref(v___y_1125_);
    crate::leanh::lean_dec(v___y_1124_);
    crate::leanh::lean_dec_ref(v___y_1123_);
    crate::leanh::lean_dec(v___y_1122_);
    crate::leanh::lean_dec_ref(v___y_1121_);
    return v_res_1128_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0(
    mut v_stx_1129_: *mut crate::leanh::LeanObject,
    mut v_output_1130_: *mut crate::leanh::LeanObject,
    mut v_trees_1131_: *mut crate::leanh::LeanObject,
    mut v___y_1132_: *mut crate::leanh::LeanObject,
    mut v___y_1133_: *mut crate::leanh::LeanObject,
    mut v___y_1134_: *mut crate::leanh::LeanObject,
    mut v___y_1135_: *mut crate::leanh::LeanObject,
    mut v___y_1136_: *mut crate::leanh::LeanObject,
    mut v___y_1137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lctx_1139_ = crate::leanh::lean_ctor_get(v___y_1134_, 2);
    crate::leanh::lean_inc_ref(v_lctx_1139_);
    v___x_1140_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1140_, 0, v_lctx_1139_);
    crate::leanh::lean_ctor_set(v___x_1140_, 1, v_stx_1129_);
    crate::leanh::lean_ctor_set(v___x_1140_, 2, v_output_1130_);
    v___x_1141_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1141_, 0, v___x_1140_);
    v___x_1142_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1142_, 0, v___x_1141_);
    crate::leanh::lean_ctor_set(v___x_1142_, 1, v_trees_1131_);
    v___x_1143_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1143_, 0, v___x_1142_);
    return v___x_1143_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0___boxed(
    mut v_stx_1144_: *mut crate::leanh::LeanObject,
    mut v_output_1145_: *mut crate::leanh::LeanObject,
    mut v_trees_1146_: *mut crate::leanh::LeanObject,
    mut v___y_1147_: *mut crate::leanh::LeanObject,
    mut v___y_1148_: *mut crate::leanh::LeanObject,
    mut v___y_1149_: *mut crate::leanh::LeanObject,
    mut v___y_1150_: *mut crate::leanh::LeanObject,
    mut v___y_1151_: *mut crate::leanh::LeanObject,
    mut v___y_1152_: *mut crate::leanh::LeanObject,
    mut v___y_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0(v_stx_1144_, v_output_1145_, v_trees_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
    crate::leanh::lean_dec(v___y_1152_);
    crate::leanh::lean_dec_ref(v___y_1151_);
    crate::leanh::lean_dec(v___y_1150_);
    crate::leanh::lean_dec_ref(v___y_1149_);
    crate::leanh::lean_dec(v___y_1148_);
    crate::leanh::lean_dec_ref(v___y_1147_);
    return v_res_1154_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(
    mut v_stx_1155_: *mut crate::leanh::LeanObject,
    mut v_output_1156_: *mut crate::leanh::LeanObject,
    mut v_x_1157_: *mut crate::leanh::LeanObject,
    mut v___y_1158_: *mut crate::leanh::LeanObject,
    mut v___y_1159_: *mut crate::leanh::LeanObject,
    mut v___y_1160_: *mut crate::leanh::LeanObject,
    mut v___y_1161_: *mut crate::leanh::LeanObject,
    mut v___y_1162_: *mut crate::leanh::LeanObject,
    mut v___y_1163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1165_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 2);
    crate::leanh::lean_closure_set(v___f_1165_, 0, v_stx_1155_);
    crate::leanh::lean_closure_set(v___f_1165_, 1, v_output_1156_);
    v___x_1166_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_1157_, v___f_1165_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
    return v___x_1166_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___boxed(
    mut v_stx_1167_: *mut crate::leanh::LeanObject,
    mut v_output_1168_: *mut crate::leanh::LeanObject,
    mut v_x_1169_: *mut crate::leanh::LeanObject,
    mut v___y_1170_: *mut crate::leanh::LeanObject,
    mut v___y_1171_: *mut crate::leanh::LeanObject,
    mut v___y_1172_: *mut crate::leanh::LeanObject,
    mut v___y_1173_: *mut crate::leanh::LeanObject,
    mut v___y_1174_: *mut crate::leanh::LeanObject,
    mut v___y_1175_: *mut crate::leanh::LeanObject,
    mut v___y_1176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1177_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_stx_1167_, v_output_1168_, v_x_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
    crate::leanh::lean_dec(v___y_1175_);
    crate::leanh::lean_dec_ref(v___y_1174_);
    crate::leanh::lean_dec(v___y_1173_);
    crate::leanh::lean_dec_ref(v___y_1172_);
    crate::leanh::lean_dec(v___y_1171_);
    crate::leanh::lean_dec_ref(v___y_1170_);
    return v_res_1177_;
}
pub unsafe fn l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(
    mut v_beforeStx_1178_: *mut crate::leanh::LeanObject,
    mut v_afterStx_1179_: *mut crate::leanh::LeanObject,
    mut v_x_1180_: *mut crate::leanh::LeanObject,
    mut v___y_1181_: *mut crate::leanh::LeanObject,
    mut v___y_1182_: *mut crate::leanh::LeanObject,
    mut v___y_1183_: *mut crate::leanh::LeanObject,
    mut v___y_1184_: *mut crate::leanh::LeanObject,
    mut v___y_1185_: *mut crate::leanh::LeanObject,
    mut v___y_1186_: *mut crate::leanh::LeanObject,
    mut v___y_1187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1195_: u8 = 0;
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v___y_1181_);
                v___f_1189_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                crate::leanh::lean_closure_set(v___f_1189_, 0, v_x_1180_);
                crate::leanh::lean_closure_set(v___f_1189_, 1, v___y_1181_);
                crate::leanh::lean_inc(v_afterStx_1179_);
                crate::leanh::lean_inc(v_beforeStx_1178_);
                v___x_1190_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Term_withPushMacroExpansionStack___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_1190_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_1190_, 1, v_beforeStx_1178_);
                crate::leanh::lean_closure_set(v___x_1190_, 2, v_afterStx_1179_);
                crate::leanh::lean_closure_set(v___x_1190_, 3, v___f_1189_);
                v___x_1191_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_beforeStx_1178_, v_afterStx_1179_, v___x_1190_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
                if crate::leanh::lean_obj_tag(v___x_1191_) == 0 {
                    return v___x_1191_;
                } else {
                    v_a_1192_ = crate::leanh::lean_ctor_get(v___x_1191_, 0);
                    v_isSharedCheck_1199_ = (!crate::leanh::lean_is_exclusive(v___x_1191_)) as u8;
                    if v_isSharedCheck_1199_ == 0 {
                        v___x_1194_ = v___x_1191_;
                        v_isShared_1195_ = v_isSharedCheck_1199_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1192_);
                        crate::leanh::lean_dec(v___x_1191_);
                        v___x_1194_ = crate::leanh::lean_box(0);
                        v_isShared_1195_ = v_isSharedCheck_1199_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1195_ == 0 {
                    v___x_1197_ = v___x_1194_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1198_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
                    v___x_1197_ = v_reuseFailAlloc_1198_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1197_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___boxed(
    mut v_beforeStx_1200_: *mut crate::leanh::LeanObject,
    mut v_afterStx_1201_: *mut crate::leanh::LeanObject,
    mut v_x_1202_: *mut crate::leanh::LeanObject,
    mut v___y_1203_: *mut crate::leanh::LeanObject,
    mut v___y_1204_: *mut crate::leanh::LeanObject,
    mut v___y_1205_: *mut crate::leanh::LeanObject,
    mut v___y_1206_: *mut crate::leanh::LeanObject,
    mut v___y_1207_: *mut crate::leanh::LeanObject,
    mut v___y_1208_: *mut crate::leanh::LeanObject,
    mut v___y_1209_: *mut crate::leanh::LeanObject,
    mut v___y_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1211_ =
        l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(
            v_beforeStx_1200_,
            v_afterStx_1201_,
            v_x_1202_,
            v___y_1203_,
            v___y_1204_,
            v___y_1205_,
            v___y_1206_,
            v___y_1207_,
            v___y_1208_,
            v___y_1209_,
        );
    crate::leanh::lean_dec(v___y_1209_);
    crate::leanh::lean_dec_ref(v___y_1208_);
    crate::leanh::lean_dec(v___y_1207_);
    crate::leanh::lean_dec_ref(v___y_1206_);
    crate::leanh::lean_dec(v___y_1205_);
    crate::leanh::lean_dec_ref(v___y_1204_);
    crate::leanh::lean_dec_ref(v___y_1203_);
    return v_res_1211_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoRepeat___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1236_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_1236_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoRepeat___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1246_ = l_Lean_Elab_Do_elabDoRepeat___closed__16;
    v___x_1247_ = l_String_toRawSubstring_x27(v___x_1246_);
    return v___x_1247_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoRepeat(
    mut v_stx_1302_: *mut crate::leanh::LeanObject,
    mut v_dec_1303_: *mut crate::leanh::LeanObject,
    mut v_a_1304_: *mut crate::leanh::LeanObject,
    mut v_a_1305_: *mut crate::leanh::LeanObject,
    mut v_a_1306_: *mut crate::leanh::LeanObject,
    mut v_a_1307_: *mut crate::leanh::LeanObject,
    mut v_a_1308_: *mut crate::leanh::LeanObject,
    mut v_a_1309_: *mut crate::leanh::LeanObject,
    mut v_a_1310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: u8 = 0;
    let mut v_expanded_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seq_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: u8 = 0;
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_breaks_1354_: u8 = 0;
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: u8 = 0;
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1392_: u8 = 0;
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1396_: u8 = 0;
    let mut v_a_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1400_: u8 = 0;
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1404_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1312_ = l_Lean_Elab_Do_elabDoRepeat___closed__4;
                crate::leanh::lean_inc(v_stx_1302_);
                v___x_1313_ = l_Lean_Syntax_isOfKind(v_stx_1302_, v___x_1312_);
                if v___x_1313_ == 0 {
                    crate::leanh::lean_dec_ref(v_dec_1303_);
                    crate::leanh::lean_dec(v_stx_1302_);
                    v___x_1326_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
                    return v___x_1326_;
                } else {
                    v_ref_1327_ = crate::leanh::lean_ctor_get(v_a_1309_, 5);
                    v_quotContext_1328_ = crate::leanh::lean_ctor_get(v_a_1309_, 10);
                    v_currMacroScope_1329_ = crate::leanh::lean_ctor_get(v_a_1309_, 11);
                    v___x_1330_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_seq_1331_ = l_Lean_Syntax_getArg(v_stx_1302_, v___x_1330_);
                    v___x_1332_ = 0;
                    v___x_1333_ = l_Lean_SourceInfo_fromRef(v_ref_1327_, v___x_1332_);
                    v___x_1334_ = l_Lean_Elab_Do_elabDoRepeat___closed__6;
                    v___x_1335_ = l_Lean_Elab_Do_elabDoRepeat___closed__8;
                    v___x_1336_ = l_Lean_Elab_Do_elabDoRepeat___closed__10;
                    v___x_1337_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoRepeat___closed__11),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoRepeat___closed__11_once),
                        _init_l_Lean_Elab_Do_elabDoRepeat___closed__11,
                    );
                    crate::leanh::lean_inc_n(v___x_1333_, 6);
                    v___x_1338_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1338_, 0, v___x_1333_);
                    crate::leanh::lean_ctor_set(v___x_1338_, 1, v___x_1335_);
                    crate::leanh::lean_ctor_set(v___x_1338_, 2, v___x_1337_);
                    v___x_1339_ = l_Lean_Elab_Do_elabDoRepeat___closed__13;
                    v___x_1340_ = l_Lean_Elab_Do_elabDoRepeat___closed__14;
                    v___x_1341_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1341_, 0, v___x_1333_);
                    crate::leanh::lean_ctor_set(v___x_1341_, 1, v___x_1340_);
                    v___x_1342_ = l_Lean_Syntax_node1(v___x_1333_, v___x_1339_, v___x_1341_);
                    v___x_1343_ = l_Lean_Elab_Do_elabDoRepeat___closed__15;
                    v___x_1344_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1344_, 0, v___x_1333_);
                    crate::leanh::lean_ctor_set(v___x_1344_, 1, v___x_1343_);
                    v___x_1345_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoRepeat___closed__17),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoRepeat___closed__17_once),
                        _init_l_Lean_Elab_Do_elabDoRepeat___closed__17,
                    );
                    v___x_1346_ = l_Lean_Elab_Do_elabDoRepeat___closed__20;
                    crate::leanh::lean_inc(v_currMacroScope_1329_);
                    crate::leanh::lean_inc(v_quotContext_1328_);
                    v___x_1347_ = l_Lean_addMacroScope(
                        v_quotContext_1328_,
                        v___x_1346_,
                        v_currMacroScope_1329_,
                    );
                    v___x_1348_ = l_Lean_Elab_Do_elabDoRepeat___closed__25;
                    v___x_1349_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1349_, 0, v___x_1333_);
                    crate::leanh::lean_ctor_set(v___x_1349_, 1, v___x_1345_);
                    crate::leanh::lean_ctor_set(v___x_1349_, 2, v___x_1347_);
                    crate::leanh::lean_ctor_set(v___x_1349_, 3, v___x_1348_);
                    v___x_1350_ = l_Lean_Syntax_node4(
                        v___x_1333_,
                        v___x_1336_,
                        v___x_1338_,
                        v___x_1342_,
                        v___x_1344_,
                        v___x_1349_,
                    );
                    crate::leanh::lean_inc(v_seq_1331_);
                    v___x_1351_ = l_Lean_Elab_Do_inferControlInfoSeq(
                        v_seq_1331_,
                        v_a_1305_,
                        v_a_1306_,
                        v_a_1307_,
                        v_a_1308_,
                        v_a_1309_,
                        v_a_1310_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1351_) == 0 {
                        v_a_1352_ = crate::leanh::lean_ctor_get(v___x_1351_, 0);
                        crate::leanh::lean_inc(v_a_1352_);
                        crate::leanh::lean_dec_ref_known(v___x_1351_, 1);
                        crate::leanh::lean_inc_n(v___x_1333_, 2);
                        v___x_1353_ = l_Lean_Syntax_node1(v___x_1333_, v___x_1335_, v___x_1350_);
                        v_breaks_1354_ = crate::leanh::lean_ctor_get_uint8(
                            v_a_1352_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        crate::leanh::lean_dec(v_a_1352_);
                        v___x_1355_ = l_Lean_Elab_Do_elabDoRepeat___closed__26;
                        v___x_1356_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1356_, 0, v___x_1333_);
                        crate::leanh::lean_ctor_set(v___x_1356_, 1, v___x_1355_);
                        v___x_1357_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_tk_1358_ = l_Lean_Syntax_getArg(v_stx_1302_, v___x_1357_);
                        v___x_1359_ = l_Lean_SourceInfo_fromRef(v_tk_1358_, v___x_1313_);
                        crate::leanh::lean_dec(v_tk_1358_);
                        v___x_1360_ = l_Lean_Elab_Do_elabDoRepeat___closed__27;
                        v___x_1361_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1361_, 0, v___x_1359_);
                        crate::leanh::lean_ctor_set(v___x_1361_, 1, v___x_1360_);
                        v___x_1362_ = l_Lean_Syntax_node4(
                            v___x_1333_,
                            v___x_1334_,
                            v___x_1361_,
                            v___x_1353_,
                            v___x_1356_,
                            v_seq_1331_,
                        );
                        if v_breaks_1354_ == 0 {
                            if v___x_1313_ == 0 {
                                v_expanded_1315_ = v___x_1362_;
                                v___y_1316_ = v_a_1304_;
                                v___y_1317_ = v_a_1305_;
                                v___y_1318_ = v_a_1306_;
                                v___y_1319_ = v_a_1307_;
                                v___y_1320_ = v_a_1308_;
                                v___y_1321_ = v_a_1309_;
                                v___y_1322_ = v_a_1310_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1363_ = l_Lean_Elab_Do_mkPUnit___redArg(v_a_1304_);
                                if crate::leanh::lean_obj_tag(v___x_1363_) == 0 {
                                    v_a_1364_ = crate::leanh::lean_ctor_get(v___x_1363_, 0);
                                    crate::leanh::lean_inc(v_a_1364_);
                                    crate::leanh::lean_dec_ref_known(v___x_1363_, 1);
                                    v_resultType_1365_ =
                                        crate::leanh::lean_ctor_get(v_dec_1303_, 1);
                                    crate::leanh::lean_inc_ref(v_resultType_1365_);
                                    v___x_1366_ = l_Lean_Meta_isExprDefEqGuarded(
                                        v_resultType_1365_,
                                        v_a_1364_,
                                        v_a_1307_,
                                        v_a_1308_,
                                        v_a_1309_,
                                        v_a_1310_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_1366_) == 0 {
                                        v_a_1367_ = crate::leanh::lean_ctor_get(v___x_1366_, 0);
                                        crate::leanh::lean_inc(v_a_1367_);
                                        crate::leanh::lean_dec_ref_known(v___x_1366_, 1);
                                        v___x_1368_ = (crate::leanh::lean_unbox(v_a_1367_) as u8);
                                        crate::leanh::lean_dec(v_a_1367_);
                                        if v___x_1368_ == 0 {
                                            v___x_1369_ = l_Lean_SourceInfo_fromRef(
                                                v_ref_1327_,
                                                v_breaks_1354_,
                                            );
                                            v___x_1370_ = l_Lean_Elab_Do_elabDoRepeat___closed__29;
                                            crate::leanh::lean_inc_n(v___x_1369_, 11);
                                            v___x_1371_ =
                                                crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1371_,
                                                0,
                                                v___x_1369_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_1371_,
                                                1,
                                                v___x_1355_,
                                            );
                                            v___x_1372_ = l_Lean_Elab_Do_elabDoRepeat___closed__31;
                                            v___x_1373_ = l_Lean_Elab_Do_elabDoRepeat___closed__33;
                                            v___x_1374_ = l_Lean_Elab_Do_elabDoRepeat___closed__34;
                                            v___x_1375_ =
                                                crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1375_,
                                                0,
                                                v___x_1369_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_1375_,
                                                1,
                                                v___x_1374_,
                                            );
                                            v___x_1376_ = l_Lean_Syntax_node1(
                                                v___x_1369_,
                                                v___x_1335_,
                                                v___x_1375_,
                                            );
                                            v___x_1377_ = l_Lean_Syntax_node2(
                                                v___x_1369_,
                                                v___x_1373_,
                                                v___x_1362_,
                                                v___x_1376_,
                                            );
                                            v___x_1378_ = l_Lean_Elab_Do_elabDoRepeat___closed__36;
                                            v___x_1379_ = l_Lean_Elab_Do_elabDoRepeat___closed__38;
                                            v___x_1380_ = l_Lean_Elab_Do_elabDoRepeat___closed__39;
                                            v___x_1381_ =
                                                crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1381_,
                                                0,
                                                v___x_1369_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_1381_,
                                                1,
                                                v___x_1380_,
                                            );
                                            v___x_1382_ = l_Lean_Syntax_node1(
                                                v___x_1369_,
                                                v___x_1379_,
                                                v___x_1381_,
                                            );
                                            v___x_1383_ = l_Lean_Syntax_node1(
                                                v___x_1369_,
                                                v___x_1378_,
                                                v___x_1382_,
                                            );
                                            v___x_1384_ =
                                                crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1384_,
                                                0,
                                                v___x_1369_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_1384_,
                                                1,
                                                v___x_1335_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_1384_,
                                                2,
                                                v___x_1337_,
                                            );
                                            v___x_1385_ = l_Lean_Syntax_node2(
                                                v___x_1369_,
                                                v___x_1373_,
                                                v___x_1383_,
                                                v___x_1384_,
                                            );
                                            v___x_1386_ = l_Lean_Syntax_node2(
                                                v___x_1369_,
                                                v___x_1335_,
                                                v___x_1377_,
                                                v___x_1385_,
                                            );
                                            v___x_1387_ = l_Lean_Syntax_node1(
                                                v___x_1369_,
                                                v___x_1372_,
                                                v___x_1386_,
                                            );
                                            v___x_1388_ = l_Lean_Syntax_node2(
                                                v___x_1369_,
                                                v___x_1370_,
                                                v___x_1371_,
                                                v___x_1387_,
                                            );
                                            v_expanded_1315_ = v___x_1388_;
                                            v___y_1316_ = v_a_1304_;
                                            v___y_1317_ = v_a_1305_;
                                            v___y_1318_ = v_a_1306_;
                                            v___y_1319_ = v_a_1307_;
                                            v___y_1320_ = v_a_1308_;
                                            v___y_1321_ = v_a_1309_;
                                            v___y_1322_ = v_a_1310_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_expanded_1315_ = v___x_1362_;
                                            v___y_1316_ = v_a_1304_;
                                            v___y_1317_ = v_a_1305_;
                                            v___y_1318_ = v_a_1306_;
                                            v___y_1319_ = v_a_1307_;
                                            v___y_1320_ = v_a_1308_;
                                            v___y_1321_ = v_a_1309_;
                                            v___y_1322_ = v_a_1310_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v___x_1362_);
                                        crate::leanh::lean_dec_ref(v_dec_1303_);
                                        crate::leanh::lean_dec(v_stx_1302_);
                                        v_a_1389_ = crate::leanh::lean_ctor_get(v___x_1366_, 0);
                                        v_isSharedCheck_1396_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1366_)) as u8;
                                        if v_isSharedCheck_1396_ == 0 {
                                            v___x_1391_ = v___x_1366_;
                                            v_isShared_1392_ = v_isSharedCheck_1396_;
                                            state = 2;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1389_);
                                            crate::leanh::lean_dec(v___x_1366_);
                                            v___x_1391_ = crate::leanh::lean_box(0);
                                            v_isShared_1392_ = v_isSharedCheck_1396_;
                                            state = 2;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_1362_);
                                    crate::leanh::lean_dec_ref(v_dec_1303_);
                                    crate::leanh::lean_dec(v_stx_1302_);
                                    return v___x_1363_;
                                }
                            }
                        } else {
                            v_expanded_1315_ = v___x_1362_;
                            v___y_1316_ = v_a_1304_;
                            v___y_1317_ = v_a_1305_;
                            v___y_1318_ = v_a_1306_;
                            v___y_1319_ = v_a_1307_;
                            v___y_1320_ = v_a_1308_;
                            v___y_1321_ = v_a_1309_;
                            v___y_1322_ = v_a_1310_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1350_);
                        crate::leanh::lean_dec(v___x_1333_);
                        crate::leanh::lean_dec(v_seq_1331_);
                        crate::leanh::lean_dec_ref(v_dec_1303_);
                        crate::leanh::lean_dec(v_stx_1302_);
                        v_a_1397_ = crate::leanh::lean_ctor_get(v___x_1351_, 0);
                        v_isSharedCheck_1404_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1351_)) as u8;
                        if v_isSharedCheck_1404_ == 0 {
                            v___x_1399_ = v___x_1351_;
                            v_isShared_1400_ = v_isSharedCheck_1404_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1397_);
                            crate::leanh::lean_dec(v___x_1351_);
                            v___x_1399_ = crate::leanh::lean_box(0);
                            v_isShared_1400_ = v_isSharedCheck_1404_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1323_ = crate::leanh::lean_box((v___x_1313_) as usize);
                crate::leanh::lean_inc(v_expanded_1315_);
                v___f_1324_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoRepeat___lam__0___boxed as *mut core::ffi::c_void,
                    11,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_1324_, 0, v_expanded_1315_);
                crate::leanh::lean_closure_set(v___f_1324_, 1, v_dec_1303_);
                crate::leanh::lean_closure_set(v___f_1324_, 2, v___x_1323_);
                v___x_1325_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_stx_1302_, v_expanded_1315_, v___f_1324_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
                return v___x_1325_;
            }
            2 => {
                if v_isShared_1392_ == 0 {
                    v___x_1394_ = v___x_1391_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1395_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
                    v___x_1394_ = v_reuseFailAlloc_1395_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1394_;
            }
            4 => {
                if v_isShared_1400_ == 0 {
                    v___x_1402_ = v___x_1399_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1403_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
                    v___x_1402_ = v_reuseFailAlloc_1403_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1402_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoRepeat___boxed(
    mut v_stx_1405_: *mut crate::leanh::LeanObject,
    mut v_dec_1406_: *mut crate::leanh::LeanObject,
    mut v_a_1407_: *mut crate::leanh::LeanObject,
    mut v_a_1408_: *mut crate::leanh::LeanObject,
    mut v_a_1409_: *mut crate::leanh::LeanObject,
    mut v_a_1410_: *mut crate::leanh::LeanObject,
    mut v_a_1411_: *mut crate::leanh::LeanObject,
    mut v_a_1412_: *mut crate::leanh::LeanObject,
    mut v_a_1413_: *mut crate::leanh::LeanObject,
    mut v_a_1414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1415_ = l_Lean_Elab_Do_elabDoRepeat(
        v_stx_1405_,
        v_dec_1406_,
        v_a_1407_,
        v_a_1408_,
        v_a_1409_,
        v_a_1410_,
        v_a_1411_,
        v_a_1412_,
        v_a_1413_,
    );
    crate::leanh::lean_dec(v_a_1413_);
    crate::leanh::lean_dec_ref(v_a_1412_);
    crate::leanh::lean_dec(v_a_1411_);
    crate::leanh::lean_dec_ref(v_a_1410_);
    crate::leanh::lean_dec(v_a_1409_);
    crate::leanh::lean_dec_ref(v_a_1408_);
    crate::leanh::lean_dec_ref(v_a_1407_);
    return v_res_1415_;
}
pub unsafe fn l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1(
    mut v_00_u03b1_1416_: *mut crate::leanh::LeanObject,
    mut v_beforeStx_1417_: *mut crate::leanh::LeanObject,
    mut v_afterStx_1418_: *mut crate::leanh::LeanObject,
    mut v_x_1419_: *mut crate::leanh::LeanObject,
    mut v___y_1420_: *mut crate::leanh::LeanObject,
    mut v___y_1421_: *mut crate::leanh::LeanObject,
    mut v___y_1422_: *mut crate::leanh::LeanObject,
    mut v___y_1423_: *mut crate::leanh::LeanObject,
    mut v___y_1424_: *mut crate::leanh::LeanObject,
    mut v___y_1425_: *mut crate::leanh::LeanObject,
    mut v___y_1426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1428_ =
        l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(
            v_beforeStx_1417_,
            v_afterStx_1418_,
            v_x_1419_,
            v___y_1420_,
            v___y_1421_,
            v___y_1422_,
            v___y_1423_,
            v___y_1424_,
            v___y_1425_,
            v___y_1426_,
        );
    return v___x_1428_;
}
pub unsafe fn l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___boxed(
    mut v_00_u03b1_1429_: *mut crate::leanh::LeanObject,
    mut v_beforeStx_1430_: *mut crate::leanh::LeanObject,
    mut v_afterStx_1431_: *mut crate::leanh::LeanObject,
    mut v_x_1432_: *mut crate::leanh::LeanObject,
    mut v___y_1433_: *mut crate::leanh::LeanObject,
    mut v___y_1434_: *mut crate::leanh::LeanObject,
    mut v___y_1435_: *mut crate::leanh::LeanObject,
    mut v___y_1436_: *mut crate::leanh::LeanObject,
    mut v___y_1437_: *mut crate::leanh::LeanObject,
    mut v___y_1438_: *mut crate::leanh::LeanObject,
    mut v___y_1439_: *mut crate::leanh::LeanObject,
    mut v___y_1440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1441_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1(
        v_00_u03b1_1429_,
        v_beforeStx_1430_,
        v_afterStx_1431_,
        v_x_1432_,
        v___y_1433_,
        v___y_1434_,
        v___y_1435_,
        v___y_1436_,
        v___y_1437_,
        v___y_1438_,
        v___y_1439_,
    );
    crate::leanh::lean_dec(v___y_1439_);
    crate::leanh::lean_dec_ref(v___y_1438_);
    crate::leanh::lean_dec(v___y_1437_);
    crate::leanh::lean_dec_ref(v___y_1436_);
    crate::leanh::lean_dec(v___y_1435_);
    crate::leanh::lean_dec_ref(v___y_1434_);
    crate::leanh::lean_dec_ref(v___y_1433_);
    return v_res_1441_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1(
    mut v_00_u03b1_1442_: *mut crate::leanh::LeanObject,
    mut v_stx_1443_: *mut crate::leanh::LeanObject,
    mut v_output_1444_: *mut crate::leanh::LeanObject,
    mut v_x_1445_: *mut crate::leanh::LeanObject,
    mut v___y_1446_: *mut crate::leanh::LeanObject,
    mut v___y_1447_: *mut crate::leanh::LeanObject,
    mut v___y_1448_: *mut crate::leanh::LeanObject,
    mut v___y_1449_: *mut crate::leanh::LeanObject,
    mut v___y_1450_: *mut crate::leanh::LeanObject,
    mut v___y_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1453_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_stx_1443_, v_output_1444_, v_x_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
    return v___x_1453_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___boxed(
    mut v_00_u03b1_1454_: *mut crate::leanh::LeanObject,
    mut v_stx_1455_: *mut crate::leanh::LeanObject,
    mut v_output_1456_: *mut crate::leanh::LeanObject,
    mut v_x_1457_: *mut crate::leanh::LeanObject,
    mut v___y_1458_: *mut crate::leanh::LeanObject,
    mut v___y_1459_: *mut crate::leanh::LeanObject,
    mut v___y_1460_: *mut crate::leanh::LeanObject,
    mut v___y_1461_: *mut crate::leanh::LeanObject,
    mut v___y_1462_: *mut crate::leanh::LeanObject,
    mut v___y_1463_: *mut crate::leanh::LeanObject,
    mut v___y_1464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1465_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1(v_00_u03b1_1454_, v_stx_1455_, v_output_1456_, v_x_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
    crate::leanh::lean_dec(v___y_1463_);
    crate::leanh::lean_dec_ref(v___y_1462_);
    crate::leanh::lean_dec(v___y_1461_);
    crate::leanh::lean_dec_ref(v___y_1460_);
    crate::leanh::lean_dec(v___y_1459_);
    crate::leanh::lean_dec_ref(v___y_1458_);
    return v_res_1465_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3(
    mut v___y_1466_: *mut crate::leanh::LeanObject,
    mut v___y_1467_: *mut crate::leanh::LeanObject,
    mut v___y_1468_: *mut crate::leanh::LeanObject,
    mut v___y_1469_: *mut crate::leanh::LeanObject,
    mut v___y_1470_: *mut crate::leanh::LeanObject,
    mut v___y_1471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1473_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_1471_);
    return v___x_1473_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___boxed(
    mut v___y_1474_: *mut crate::leanh::LeanObject,
    mut v___y_1475_: *mut crate::leanh::LeanObject,
    mut v___y_1476_: *mut crate::leanh::LeanObject,
    mut v___y_1477_: *mut crate::leanh::LeanObject,
    mut v___y_1478_: *mut crate::leanh::LeanObject,
    mut v___y_1479_: *mut crate::leanh::LeanObject,
    mut v___y_1480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1481_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3(v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
    crate::leanh::lean_dec(v___y_1479_);
    crate::leanh::lean_dec_ref(v___y_1478_);
    crate::leanh::lean_dec(v___y_1477_);
    crate::leanh::lean_dec_ref(v___y_1476_);
    crate::leanh::lean_dec(v___y_1475_);
    crate::leanh::lean_dec_ref(v___y_1474_);
    return v_res_1481_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2(
    mut v_00_u03b1_1482_: *mut crate::leanh::LeanObject,
    mut v_x_1483_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_1484_: *mut crate::leanh::LeanObject,
    mut v___y_1485_: *mut crate::leanh::LeanObject,
    mut v___y_1486_: *mut crate::leanh::LeanObject,
    mut v___y_1487_: *mut crate::leanh::LeanObject,
    mut v___y_1488_: *mut crate::leanh::LeanObject,
    mut v___y_1489_: *mut crate::leanh::LeanObject,
    mut v___y_1490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1492_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_1483_, v_mkInfoTree_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
    return v___x_1492_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b1_1493_: *mut crate::leanh::LeanObject,
    mut v_x_1494_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_1495_: *mut crate::leanh::LeanObject,
    mut v___y_1496_: *mut crate::leanh::LeanObject,
    mut v___y_1497_: *mut crate::leanh::LeanObject,
    mut v___y_1498_: *mut crate::leanh::LeanObject,
    mut v___y_1499_: *mut crate::leanh::LeanObject,
    mut v___y_1500_: *mut crate::leanh::LeanObject,
    mut v___y_1501_: *mut crate::leanh::LeanObject,
    mut v___y_1502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1503_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2(v_00_u03b1_1493_, v_x_1494_, v_mkInfoTree_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
    crate::leanh::lean_dec(v___y_1501_);
    crate::leanh::lean_dec_ref(v___y_1500_);
    crate::leanh::lean_dec(v___y_1499_);
    crate::leanh::lean_dec_ref(v___y_1498_);
    crate::leanh::lean_dec(v___y_1497_);
    crate::leanh::lean_dec_ref(v___y_1496_);
    return v_res_1503_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1513_ = l_Lean_Elab_Do_doElemElabAttribute;
    v___x_1514_ = l_Lean_Elab_Do_elabDoRepeat___closed__4;
    v___x_1515_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3;
    v___x_1516_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Do_elabDoRepeat___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1517_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1513_,
        v___x_1514_,
        v___x_1515_,
        v___x_1516_,
    );
    return v___x_1517_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___boxed(
    mut v_a_1518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1519_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1();
    return v_res_1519_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1522_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3;
    v___x_1523_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___closed__0;
    v___x_1524_ = l_Lean_addBuiltinDocString(v___x_1522_, v___x_1523_);
    return v___x_1524_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___boxed(
    mut v_a_1525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1526_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3();
    return v_res_1526_;
}
pub unsafe fn l_Lean_Elab_Do_expandDoWhile(
    mut v_x_1550_: *mut crate::leanh::LeanObject,
    mut v_a_1551_: *mut crate::leanh::LeanObject,
    mut v_a_1552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: u8 = 0;
    v___x_1553_ = l_Lean_Elab_Do_expandDoWhile___closed__1;
    crate::leanh::lean_inc(v_x_1550_);
    v___x_1554_ = l_Lean_Syntax_isOfKind(v_x_1550_, v___x_1553_);
    if v___x_1554_ == 0 {
        let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1550_);
        v___x_1555_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1552_);
        return v___x_1555_;
    } else {
        let mut v_ref_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tk_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1563_: u8 = 0;
        let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_1556_ = crate::leanh::lean_ctor_get(v_a_1551_, 5);
        v___x_1557_ = crate::leanh::lean_unsigned_to_nat(0);
        v_tk_1558_ = l_Lean_Syntax_getArg(v_x_1550_, v___x_1557_);
        v___x_1559_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1560_ = l_Lean_Syntax_getArg(v_x_1550_, v___x_1559_);
        v___x_1561_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_1562_ = l_Lean_Syntax_getArg(v_x_1550_, v___x_1561_);
        crate::leanh::lean_dec(v_x_1550_);
        v___x_1563_ = 0;
        v___x_1564_ = l_Lean_SourceInfo_fromRef(v_ref_1556_, v___x_1563_);
        v___x_1565_ = l_Lean_Elab_Do_elabDoRepeat___closed__4;
        v___x_1566_ = l_Lean_SourceInfo_fromRef(v_tk_1558_, v___x_1554_);
        crate::leanh::lean_dec(v_tk_1558_);
        v___x_1567_ = l_Lean_Elab_Do_expandDoWhile___closed__2;
        v___x_1568_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1568_, 0, v___x_1566_);
        crate::leanh::lean_ctor_set(v___x_1568_, 1, v___x_1567_);
        v___x_1569_ = l_Lean_Elab_Do_elabDoRepeat___closed__31;
        v___x_1570_ = l_Lean_Elab_Do_elabDoRepeat___closed__8;
        v___x_1571_ = l_Lean_Elab_Do_elabDoRepeat___closed__33;
        v___x_1572_ = l_Lean_Elab_Do_expandDoWhile___closed__4;
        v___x_1573_ = l_Lean_Elab_Do_expandDoWhile___closed__5;
        crate::leanh::lean_inc_n(v___x_1564_, 14);
        v___x_1574_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1574_, 0, v___x_1564_);
        crate::leanh::lean_ctor_set(v___x_1574_, 1, v___x_1573_);
        v___x_1575_ = l_Lean_Elab_Do_expandDoWhile___closed__6;
        v___x_1576_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1576_, 0, v___x_1564_);
        crate::leanh::lean_ctor_set(v___x_1576_, 1, v___x_1575_);
        v___x_1577_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoRepeat___closed__11),
            core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoRepeat___closed__11_once),
            _init_l_Lean_Elab_Do_elabDoRepeat___closed__11,
        );
        v___x_1578_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1578_, 0, v___x_1564_);
        crate::leanh::lean_ctor_set(v___x_1578_, 1, v___x_1570_);
        crate::leanh::lean_ctor_set(v___x_1578_, 2, v___x_1577_);
        v___x_1579_ = l_Lean_Elab_Do_expandDoWhile___closed__7;
        v___x_1580_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1580_, 0, v___x_1564_);
        crate::leanh::lean_ctor_set(v___x_1580_, 1, v___x_1579_);
        v___x_1581_ = l_Lean_Elab_Do_expandDoWhile___closed__9;
        v___x_1582_ = l_Lean_Elab_Do_expandDoWhile___closed__10;
        v___x_1583_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1583_, 0, v___x_1564_);
        crate::leanh::lean_ctor_set(v___x_1583_, 1, v___x_1582_);
        v___x_1584_ = l_Lean_Syntax_node1(v___x_1564_, v___x_1581_, v___x_1583_);
        crate::leanh::lean_inc_ref_n(v___x_1578_, 2);
        v___x_1585_ = l_Lean_Syntax_node2(v___x_1564_, v___x_1571_, v___x_1584_, v___x_1578_);
        v___x_1586_ = l_Lean_Syntax_node1(v___x_1564_, v___x_1570_, v___x_1585_);
        v___x_1587_ = l_Lean_Syntax_node1(v___x_1564_, v___x_1569_, v___x_1586_);
        v___x_1588_ = l_Lean_Syntax_node2(v___x_1564_, v___x_1570_, v___x_1580_, v___x_1587_);
        v___x_1589_ = l_Lean_Syntax_node6(
            v___x_1564_,
            v___x_1572_,
            v___x_1574_,
            v___x_1560_,
            v___x_1576_,
            v___x_1562_,
            v___x_1578_,
            v___x_1588_,
        );
        v___x_1590_ = l_Lean_Syntax_node2(v___x_1564_, v___x_1571_, v___x_1589_, v___x_1578_);
        v___x_1591_ = l_Lean_Syntax_node1(v___x_1564_, v___x_1570_, v___x_1590_);
        v___x_1592_ = l_Lean_Syntax_node1(v___x_1564_, v___x_1569_, v___x_1591_);
        v___x_1593_ = l_Lean_Syntax_node2(v___x_1564_, v___x_1565_, v___x_1568_, v___x_1592_);
        v___x_1594_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1594_, 0, v___x_1593_);
        crate::leanh::lean_ctor_set(v___x_1594_, 1, v_a_1552_);
        return v___x_1594_;
    }
}
pub unsafe fn l_Lean_Elab_Do_expandDoWhile___boxed(
    mut v_x_1595_: *mut crate::leanh::LeanObject,
    mut v_a_1596_: *mut crate::leanh::LeanObject,
    mut v_a_1597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Lean_Elab_Do_expandDoWhile(v_x_1595_, v_a_1596_, v_a_1597_);
    crate::leanh::lean_dec_ref(v_a_1596_);
    return v_res_1598_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = l_Lean_Elab_macroAttribute;
    v___x_1607_ = l_Lean_Elab_Do_expandDoWhile___closed__1;
    v___x_1608_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1;
    v___x_1609_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Do_expandDoWhile___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_1610_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1606_,
        v___x_1607_,
        v___x_1608_,
        v___x_1609_,
    );
    return v___x_1610_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___boxed(
    mut v_a_1611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1612_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1();
    return v_res_1612_;
}
pub unsafe fn l_Lean_Elab_Do_expandDoRepeatUntil(
    mut v_x_1625_: *mut crate::leanh::LeanObject,
    mut v_a_1626_: *mut crate::leanh::LeanObject,
    mut v_a_1627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: u8 = 0;
    v___x_1628_ = l_Lean_Elab_Do_expandDoRepeatUntil___closed__1;
    crate::leanh::lean_inc(v_x_1625_);
    v___x_1629_ = l_Lean_Syntax_isOfKind(v_x_1625_, v___x_1628_);
    if v___x_1629_ == 0 {
        let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1625_);
        v___x_1630_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1627_);
        return v___x_1630_;
    } else {
        let mut v_ref_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tk_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1638_: u8 = 0;
        let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_1631_ = crate::leanh::lean_ctor_get(v_a_1626_, 5);
        v___x_1632_ = crate::leanh::lean_unsigned_to_nat(0);
        v_tk_1633_ = l_Lean_Syntax_getArg(v_x_1625_, v___x_1632_);
        v___x_1634_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1635_ = l_Lean_Syntax_getArg(v_x_1625_, v___x_1634_);
        v___x_1636_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_1637_ = l_Lean_Syntax_getArg(v_x_1625_, v___x_1636_);
        crate::leanh::lean_dec(v_x_1625_);
        v___x_1638_ = 0;
        v___x_1639_ = l_Lean_SourceInfo_fromRef(v_ref_1631_, v___x_1638_);
        v___x_1640_ = l_Lean_Elab_Do_elabDoRepeat___closed__4;
        v___x_1641_ = l_Lean_SourceInfo_fromRef(v_tk_1633_, v___x_1629_);
        crate::leanh::lean_dec(v_tk_1633_);
        v___x_1642_ = l_Lean_Elab_Do_expandDoWhile___closed__2;
        v___x_1643_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1643_, 0, v___x_1641_);
        crate::leanh::lean_ctor_set(v___x_1643_, 1, v___x_1642_);
        v___x_1644_ = l_Lean_Elab_Do_elabDoRepeat___closed__31;
        v___x_1645_ = l_Lean_Elab_Do_elabDoRepeat___closed__8;
        v___x_1646_ = l_Lean_Elab_Do_elabDoRepeat___closed__33;
        v___x_1647_ = l_Lean_Elab_Do_elabDoRepeat___closed__29;
        v___x_1648_ = l_Lean_Elab_Do_elabDoRepeat___closed__26;
        crate::leanh::lean_inc_n(v___x_1639_, 18);
        v___x_1649_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1649_, 0, v___x_1639_);
        crate::leanh::lean_ctor_set(v___x_1649_, 1, v___x_1648_);
        v___x_1650_ = l_Lean_Syntax_node2(v___x_1639_, v___x_1647_, v___x_1649_, v___x_1635_);
        v___x_1651_ = l_Lean_Elab_Do_elabDoRepeat___closed__34;
        v___x_1652_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1652_, 0, v___x_1639_);
        crate::leanh::lean_ctor_set(v___x_1652_, 1, v___x_1651_);
        v___x_1653_ = l_Lean_Syntax_node1(v___x_1639_, v___x_1645_, v___x_1652_);
        v___x_1654_ = l_Lean_Syntax_node2(v___x_1639_, v___x_1646_, v___x_1650_, v___x_1653_);
        v___x_1655_ = l_Lean_Elab_Do_expandDoWhile___closed__4;
        v___x_1656_ = l_Lean_Elab_Do_expandDoWhile___closed__5;
        v___x_1657_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1657_, 0, v___x_1639_);
        crate::leanh::lean_ctor_set(v___x_1657_, 1, v___x_1656_);
        v___x_1658_ = l_Lean_Elab_Do_expandDoRepeatUntil___closed__3;
        v___x_1659_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoRepeat___closed__11),
            core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoRepeat___closed__11_once),
            _init_l_Lean_Elab_Do_elabDoRepeat___closed__11,
        );
        v___x_1660_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1660_, 0, v___x_1639_);
        crate::leanh::lean_ctor_set(v___x_1660_, 1, v___x_1645_);
        crate::leanh::lean_ctor_set(v___x_1660_, 2, v___x_1659_);
        crate::leanh::lean_inc_ref_n(v___x_1660_, 4);
        v___x_1661_ = l_Lean_Syntax_node2(v___x_1639_, v___x_1658_, v___x_1660_, v___x_1637_);
        v___x_1662_ = l_Lean_Elab_Do_expandDoWhile___closed__6;
        v___x_1663_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1663_, 0, v___x_1639_);
        crate::leanh::lean_ctor_set(v___x_1663_, 1, v___x_1662_);
        v___x_1664_ = l_Lean_Elab_Do_expandDoWhile___closed__9;
        v___x_1665_ = l_Lean_Elab_Do_expandDoWhile___closed__10;
        v___x_1666_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1666_, 0, v___x_1639_);
        crate::leanh::lean_ctor_set(v___x_1666_, 1, v___x_1665_);
        v___x_1667_ = l_Lean_Syntax_node1(v___x_1639_, v___x_1664_, v___x_1666_);
        v___x_1668_ = l_Lean_Syntax_node2(v___x_1639_, v___x_1646_, v___x_1667_, v___x_1660_);
        v___x_1669_ = l_Lean_Syntax_node1(v___x_1639_, v___x_1645_, v___x_1668_);
        v___x_1670_ = l_Lean_Syntax_node1(v___x_1639_, v___x_1644_, v___x_1669_);
        v___x_1671_ = l_Lean_Syntax_node6(
            v___x_1639_,
            v___x_1655_,
            v___x_1657_,
            v___x_1661_,
            v___x_1663_,
            v___x_1670_,
            v___x_1660_,
            v___x_1660_,
        );
        v___x_1672_ = l_Lean_Syntax_node2(v___x_1639_, v___x_1646_, v___x_1671_, v___x_1660_);
        v___x_1673_ = l_Lean_Syntax_node2(v___x_1639_, v___x_1645_, v___x_1654_, v___x_1672_);
        v___x_1674_ = l_Lean_Syntax_node1(v___x_1639_, v___x_1644_, v___x_1673_);
        v___x_1675_ = l_Lean_Syntax_node2(v___x_1639_, v___x_1640_, v___x_1643_, v___x_1674_);
        v___x_1676_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1676_, 0, v___x_1675_);
        crate::leanh::lean_ctor_set(v___x_1676_, 1, v_a_1627_);
        return v___x_1676_;
    }
}
pub unsafe fn l_Lean_Elab_Do_expandDoRepeatUntil___boxed(
    mut v_x_1677_: *mut crate::leanh::LeanObject,
    mut v_a_1678_: *mut crate::leanh::LeanObject,
    mut v_a_1679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1680_ = l_Lean_Elab_Do_expandDoRepeatUntil(v_x_1677_, v_a_1678_, v_a_1679_);
    crate::leanh::lean_dec_ref(v_a_1678_);
    return v_res_1680_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1688_ = l_Lean_Elab_macroAttribute;
    v___x_1689_ = l_Lean_Elab_Do_expandDoRepeatUntil___closed__1;
    v___x_1690_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1;
    v___x_1691_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Do_expandDoRepeatUntil___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_1692_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1688_,
        v___x_1689_,
        v___x_1690_,
        v___x_1691_,
    );
    return v___x_1692_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___boxed(
    mut v_a_1693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1694_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1();
    return v_res_1694_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_BuiltinDo_Repeat(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_For(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_BuiltinDo_Repeat(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_BuiltinDo_Repeat(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_BuiltinDo_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinDo_For(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_Repeat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_BuiltinDo_Repeat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_BuiltinDo_Repeat(builtin);
}
