// Lean compiler output
// Module: Lean.Elab.BuiltinDo.Misc
// Imports: Lean.Elab.Do.Basic Lean.Parser.Do
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node4,
    l_Lean_Syntax_node6,
};
use crate::r#gen::Lean::Elab::Do::Basic::{
    initialize_Lean_Elab_Do_Basic, l_Lean_Elab_Do_DoElemCont_continueWithUnit,
    l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed, l_Lean_Elab_Do_DoElemCont_ensureUnitAt,
    l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure, l_Lean_Elab_Do_doElabToSyntax___redArg,
    l_Lean_Elab_Do_doElemElabAttribute, l_Lean_Elab_Do_elabDoElem, l_Lean_Elab_Do_elabDoSeq,
    l_Lean_Elab_Do_mkMonadApp, runtime_initialize_Lean_Elab_Do_Basic,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTerm, l_Lean_Elab_Term_elabTermEnsuringType,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Parser::Do::{
    initialize_Lean_Parser_Do, runtime_initialize_Lean_Parser_Do,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoSkip___closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Lean_Elab_Do_elabDoSkip___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoSkip___closed__1_value: leanh::LeanStringObject<7> =
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
static mut l_Lean_Elab_Do_elabDoSkip___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoSkip___closed__2_value: leanh::LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_Elab_Do_elabDoSkip___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoSkip___closed__3_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            73, 110, 116, 101, 114, 110, 97, 108, 83, 121, 110, 116, 97, 120, 0,
        ],
    };
static mut l_Lean_Elab_Do_elabDoSkip___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoSkip___closed__4_value: leanh::LeanStringObject<7> =
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
        m_data: [100, 111, 83, 107, 105, 112, 0],
    };
static mut l_Lean_Elab_Do_elabDoSkip___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_elabDoSkip___closed__5_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoSkip___closed__5_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__5_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoSkip___closed__5_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__5_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoSkip___closed__5_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__5_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__3_value)
                as *mut leanh::LeanObject,
            3428822669065651317 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoSkip___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__5_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__4_value)
                as *mut leanh::LeanObject,
            12861224375759052157 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoSkip___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__5_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__2_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 97, 98, 68, 111, 83, 107, 105, 112, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1_value) as *mut leanh::LeanObject,102172329646148436 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__2_value) as *mut leanh::LeanObject,9870218058514959007 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoExpr___closed__0_value: leanh::LeanStringObject<7> =
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
        m_data: [100, 111, 69, 120, 112, 114, 0],
    };
static mut l_Lean_Elab_Do_elabDoExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoExpr___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_elabDoExpr___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoExpr___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoExpr___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoExpr___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoExpr___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoExpr___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoExpr___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoExpr___closed__0_value)
                as *mut leanh::LeanObject,
            5573444893818005634 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoExpr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoExpr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__0_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 97, 98, 68, 111, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1_value) as *mut leanh::LeanObject,102172329646148436 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__0_value) as *mut leanh::LeanObject,1588399455808571551 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoNested___closed__0_value: leanh::LeanStringObject<9> =
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
        m_data: [100, 111, 78, 101, 115, 116, 101, 100, 0],
    };
static mut l_Lean_Elab_Do_elabDoNested___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoNested___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_elabDoNested___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoNested___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoNested___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoNested___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoNested___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoNested___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoNested___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoNested___closed__0_value)
                as *mut leanh::LeanObject,
            4570674678924417756 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoNested___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoNested___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 108, 97, 98, 68, 111, 78, 101, 115, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1_value) as *mut leanh::LeanObject,102172329646148436 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__0_value) as *mut leanh::LeanObject,6785553011720520139 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoUnless___closed__0_value: leanh::LeanStringObject<9> =
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
        m_data: [100, 111, 85, 110, 108, 101, 115, 115, 0],
    };
static mut l_Lean_Elab_Do_elabDoUnless___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_elabDoUnless___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoUnless___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoUnless___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoUnless___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__0_value)
                as *mut leanh::LeanObject,
            17291926084577229031 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoUnless___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoUnless___closed__2_value: leanh::LeanStringObject<5> =
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
        m_data: [100, 111, 73, 102, 0],
    };
static mut l_Lean_Elab_Do_elabDoUnless___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_elabDoUnless___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoUnless___closed__3_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoUnless___closed__3_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoUnless___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__3_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__2_value)
                as *mut leanh::LeanObject,
            6082561497774213 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoUnless___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoUnless___closed__4_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoUnless___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoUnless___closed__5_value: leanh::LeanStringObject<9> =
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
        m_data: [100, 111, 73, 102, 80, 114, 111, 112, 0],
    };
static mut l_Lean_Elab_Do_elabDoUnless___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_elabDoUnless___closed__6_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoUnless___closed__6_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__6_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoUnless___closed__6_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__6_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoUnless___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__6_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__5_value)
                as *mut leanh::LeanObject,
            10892447550847226679 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoUnless___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoUnless___closed__7_value: leanh::LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Elab_Do_elabDoUnless___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoUnless___closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__7_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoUnless___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_elabDoUnless___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_elabDoUnless___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoUnless___closed__10_value: leanh::LeanStringObject<5> =
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
        m_data: [116, 104, 101, 110, 0],
    };
static mut l_Lean_Elab_Do_elabDoUnless___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoUnless___closed__11_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoUnless___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__11_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_elabDoUnless___closed__12_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoUnless___closed__12_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__12_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoUnless___closed__12_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__12_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoUnless___closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__12_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__11_value)
                as *mut leanh::LeanObject,
            3326968124746134365 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoUnless___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoUnless___closed__13_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoUnless___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__13_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_elabDoUnless___closed__14_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoUnless___closed__14_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__14_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoUnless___closed__14_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__14_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoUnless___closed__14_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__14_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__13_value)
                as *mut leanh::LeanObject,
            940684074193935882 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoUnless___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoUnless___closed__15_value: leanh::LeanStringObject<5> =
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
        m_data: [115, 107, 105, 112, 0],
    };
static mut l_Lean_Elab_Do_elabDoUnless___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoUnless___closed__16_value: leanh::LeanStringObject<5> =
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
        m_data: [101, 108, 115, 101, 0],
    };
static mut l_Lean_Elab_Do_elabDoUnless___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoUnless___closed__16_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 108, 97, 98, 68, 111, 85, 110, 108, 101, 115, 115, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1_value) as *mut leanh::LeanObject,102172329646148436 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__0_value) as *mut leanh::LeanObject,8037545670634870368 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__0_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [100, 98, 103, 84, 114, 97, 99, 101, 0],
};
static mut l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__1_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [100, 98, 103, 95, 116, 114, 97, 99, 101, 0],
};
static mut l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__2_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoDbgTrace___closed__0_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [100, 111, 68, 98, 103, 84, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Elab_Do_elabDoDbgTrace___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDbgTrace___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_elabDoDbgTrace___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoDbgTrace___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDbgTrace___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoDbgTrace___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDbgTrace___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoDbgTrace___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDbgTrace___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDbgTrace___closed__0_value)
                as *mut leanh::LeanObject,
            14085378894401994018 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoDbgTrace___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDbgTrace___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoDbgTrace___closed__2_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            100, 98, 103, 95, 116, 114, 97, 99, 101, 32, 98, 111, 100, 121, 0,
        ],
    };
static mut l_Lean_Elab_Do_elabDoDbgTrace___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDbgTrace___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoDbgTrace___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDbgTrace___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoDbgTrace___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDbgTrace___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_elabDoDbgTrace___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_elabDoDbgTrace___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__0_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 108, 97, 98, 68, 111, 68, 98, 103, 84, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1_value) as *mut leanh::LeanObject,102172329646148436 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__0_value) as *mut leanh::LeanObject,9397287957419435238 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoAssert___lam__0___closed__0_value: leanh::LeanStringObject<
    7,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [97, 115, 115, 101, 114, 116, 0],
};
static mut l_Lean_Elab_Do_elabDoAssert___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoAssert___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoAssert___lam__0___closed__1_value: leanh::LeanStringObject<
    8,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [97, 115, 115, 101, 114, 116, 33, 0],
};
static mut l_Lean_Elab_Do_elabDoAssert___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoAssert___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoAssert___closed__0_value: leanh::LeanStringObject<9> =
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
        m_data: [100, 111, 65, 115, 115, 101, 114, 116, 0],
    };
static mut l_Lean_Elab_Do_elabDoAssert___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoAssert___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_elabDoAssert___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoAssert___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoAssert___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoAssert___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoAssert___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoAssert___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoAssert___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoAssert___closed__0_value)
                as *mut leanh::LeanObject,
            2448779720504119211 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoAssert___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoAssert___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoAssert___closed__2_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [97, 115, 115, 101, 114, 116, 33, 32, 98, 111, 100, 121, 0],
    };
static mut l_Lean_Elab_Do_elabDoAssert___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoAssert___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoAssert___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoAssert___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoAssert___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoAssert___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_elabDoAssert___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_elabDoAssert___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 108, 97, 98, 68, 111, 65, 115, 115, 101, 114, 116, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1_value) as *mut leanh::LeanObject,102172329646148436 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__0_value) as *mut leanh::LeanObject,12379507526797271934 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoDebugAssert___lam__0___closed__0_value:
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
    m_data: [100, 101, 98, 117, 103, 65, 115, 115, 101, 114, 116, 0],
};
static mut l_Lean_Elab_Do_elabDoDebugAssert___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDebugAssert___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoDebugAssert___lam__0___closed__1_value:
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
        100, 101, 98, 117, 103, 95, 97, 115, 115, 101, 114, 116, 33, 0,
    ],
};
static mut l_Lean_Elab_Do_elabDoDebugAssert___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDebugAssert___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoDebugAssert___closed__0_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
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
            100, 111, 68, 101, 98, 117, 103, 65, 115, 115, 101, 114, 116, 0,
        ],
    };
static mut l_Lean_Elab_Do_elabDoDebugAssert___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDebugAssert___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_elabDoDebugAssert___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoDebugAssert___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDebugAssert___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoDebugAssert___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDebugAssert___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoDebugAssert___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDebugAssert___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDebugAssert___closed__0_value)
                as *mut leanh::LeanObject,
            1496550499451600603 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoDebugAssert___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDebugAssert___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoDebugAssert___closed__2_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            100, 101, 98, 117, 103, 95, 97, 115, 115, 101, 114, 116, 33, 32, 98, 111, 100, 121, 0,
        ],
    };
static mut l_Lean_Elab_Do_elabDoDebugAssert___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDebugAssert___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoDebugAssert___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDebugAssert___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoDebugAssert___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoDebugAssert___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_elabDoDebugAssert___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_elabDoDebugAssert___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__0_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 108, 97, 98, 68, 111, 68, 101, 98, 117, 103, 65, 115, 115, 101, 114, 116, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoSkip___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__1_value) as *mut leanh::LeanObject,102172329646148436 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__0_value) as *mut leanh::LeanObject,16839604750408975889 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_674_ = leanh::lean_box(0);
    v___x_675_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_676_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_676_, 0, v___x_675_);
    leanh::lean_ctor_set(v___x_676_, 1, v___x_674_);
    return v___x_676_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_678_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___closed__0);
    v___x_679_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_679_, 0, v___x_678_);
    return v___x_679_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg___boxed(
    mut v___y_680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_681_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
    return v_res_681_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0(
    mut v_00_u03b1_682_: *mut leanh::LeanObject,
    mut v___y_683_: *mut leanh::LeanObject,
    mut v___y_684_: *mut leanh::LeanObject,
    mut v___y_685_: *mut leanh::LeanObject,
    mut v___y_686_: *mut leanh::LeanObject,
    mut v___y_687_: *mut leanh::LeanObject,
    mut v___y_688_: *mut leanh::LeanObject,
    mut v___y_689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_691_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
    return v___x_691_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___boxed(
    mut v_00_u03b1_692_: *mut leanh::LeanObject,
    mut v___y_693_: *mut leanh::LeanObject,
    mut v___y_694_: *mut leanh::LeanObject,
    mut v___y_695_: *mut leanh::LeanObject,
    mut v___y_696_: *mut leanh::LeanObject,
    mut v___y_697_: *mut leanh::LeanObject,
    mut v___y_698_: *mut leanh::LeanObject,
    mut v___y_699_: *mut leanh::LeanObject,
    mut v___y_700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_701_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0(
        v_00_u03b1_692_,
        v___y_693_,
        v___y_694_,
        v___y_695_,
        v___y_696_,
        v___y_697_,
        v___y_698_,
        v___y_699_,
    );
    leanh::lean_dec(v___y_699_);
    leanh::lean_dec_ref(v___y_698_);
    leanh::lean_dec(v___y_697_);
    leanh::lean_dec_ref(v___y_696_);
    leanh::lean_dec(v___y_695_);
    leanh::lean_dec_ref(v___y_694_);
    leanh::lean_dec_ref(v___y_693_);
    return v_res_701_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoSkip(
    mut v_stx_713_: *mut leanh::LeanObject,
    mut v_dec_714_: *mut leanh::LeanObject,
    mut v_a_715_: *mut leanh::LeanObject,
    mut v_a_716_: *mut leanh::LeanObject,
    mut v_a_717_: *mut leanh::LeanObject,
    mut v_a_718_: *mut leanh::LeanObject,
    mut v_a_719_: *mut leanh::LeanObject,
    mut v_a_720_: *mut leanh::LeanObject,
    mut v_a_721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: u8 = 0;
    let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_734_: u8 = 0;
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_738_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_723_ = l_Lean_Elab_Do_elabDoSkip___closed__5;
                leanh::lean_inc(v_stx_713_);
                v___x_724_ = l_Lean_Syntax_isOfKind(v_stx_713_, v___x_723_);
                if v___x_724_ == 0 {
                    leanh::lean_dec_ref(v_dec_714_);
                    leanh::lean_dec(v_stx_713_);
                    v___x_725_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
                    return v___x_725_;
                } else {
                    v___x_726_ = leanh::lean_unsigned_to_nat(0);
                    v_tk_727_ = l_Lean_Syntax_getArg(v_stx_713_, v___x_726_);
                    leanh::lean_dec(v_stx_713_);
                    v___x_728_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(
                        v_dec_714_, v_tk_727_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_,
                        v_a_720_, v_a_721_,
                    );
                    leanh::lean_dec(v_tk_727_);
                    if leanh::lean_obj_tag(v___x_728_) == 0 {
                        v_a_729_ = leanh::lean_ctor_get(v___x_728_, 0);
                        leanh::lean_inc(v_a_729_);
                        leanh::lean_dec_ref_known(v___x_728_, 1);
                        v___x_730_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(
                            v_a_729_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_,
                            v_a_721_,
                        );
                        return v___x_730_;
                    } else {
                        v_a_731_ = leanh::lean_ctor_get(v___x_728_, 0);
                        v_isSharedCheck_738_ = (!leanh::lean_is_exclusive(v___x_728_)) as u8;
                        if v_isSharedCheck_738_ == 0 {
                            v___x_733_ = v___x_728_;
                            v_isShared_734_ = v_isSharedCheck_738_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_731_);
                            leanh::lean_dec(v___x_728_);
                            v___x_733_ = leanh::lean_box(0);
                            v_isShared_734_ = v_isSharedCheck_738_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_734_ == 0 {
                    v___x_736_ = v___x_733_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_737_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
                    v___x_736_ = v_reuseFailAlloc_737_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_736_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoSkip___boxed(
    mut v_stx_739_: *mut leanh::LeanObject,
    mut v_dec_740_: *mut leanh::LeanObject,
    mut v_a_741_: *mut leanh::LeanObject,
    mut v_a_742_: *mut leanh::LeanObject,
    mut v_a_743_: *mut leanh::LeanObject,
    mut v_a_744_: *mut leanh::LeanObject,
    mut v_a_745_: *mut leanh::LeanObject,
    mut v_a_746_: *mut leanh::LeanObject,
    mut v_a_747_: *mut leanh::LeanObject,
    mut v_a_748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_749_ = l_Lean_Elab_Do_elabDoSkip(
        v_stx_739_, v_dec_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_,
        v_a_747_,
    );
    leanh::lean_dec(v_a_747_);
    leanh::lean_dec_ref(v_a_746_);
    leanh::lean_dec(v_a_745_);
    leanh::lean_dec_ref(v_a_744_);
    leanh::lean_dec(v_a_743_);
    leanh::lean_dec_ref(v_a_742_);
    leanh::lean_dec_ref(v_a_741_);
    return v_res_749_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1()
-> *mut leanh::LeanObject {
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_759_ = l_Lean_Elab_Do_doElemElabAttribute;
    v___x_760_ = l_Lean_Elab_Do_elabDoSkip___closed__5;
    v___x_761_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___closed__3;
    v___x_762_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Do_elabDoSkip___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_763_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_759_, v___x_760_, v___x_761_, v___x_762_,
    );
    return v___x_763_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1___boxed(
    mut v_a_764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_765_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1();
    return v_res_765_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoExpr(
    mut v_stx_772_: *mut leanh::LeanObject,
    mut v_dec_773_: *mut leanh::LeanObject,
    mut v_a_774_: *mut leanh::LeanObject,
    mut v_a_775_: *mut leanh::LeanObject,
    mut v_a_776_: *mut leanh::LeanObject,
    mut v_a_777_: *mut leanh::LeanObject,
    mut v_a_778_: *mut leanh::LeanObject,
    mut v_a_779_: *mut leanh::LeanObject,
    mut v_a_780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: u8 = 0;
    let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_790_: u8 = 0;
    let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_782_ = l_Lean_Elab_Do_elabDoExpr___closed__1;
                leanh::lean_inc(v_stx_772_);
                v___x_783_ = l_Lean_Syntax_isOfKind(v_stx_772_, v___x_782_);
                if v___x_783_ == 0 {
                    leanh::lean_dec_ref(v_dec_773_);
                    leanh::lean_dec(v_stx_772_);
                    v___x_784_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
                    return v___x_784_;
                } else {
                    v_resultType_785_ = leanh::lean_ctor_get(v_dec_773_, 1);
                    leanh::lean_inc_ref(v_resultType_785_);
                    v___x_786_ = l_Lean_Elab_Do_mkMonadApp(
                        v_resultType_785_,
                        v_a_774_,
                        v_a_775_,
                        v_a_776_,
                        v_a_777_,
                        v_a_778_,
                        v_a_779_,
                        v_a_780_,
                    );
                    if leanh::lean_obj_tag(v___x_786_) == 0 {
                        v_a_787_ = leanh::lean_ctor_get(v___x_786_, 0);
                        v_isSharedCheck_800_ = (!leanh::lean_is_exclusive(v___x_786_)) as u8;
                        if v_isSharedCheck_800_ == 0 {
                            v___x_789_ = v___x_786_;
                            v_isShared_790_ = v_isSharedCheck_800_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_787_);
                            leanh::lean_dec(v___x_786_);
                            v___x_789_ = leanh::lean_box(0);
                            v_isShared_790_ = v_isSharedCheck_800_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_dec_773_);
                        leanh::lean_dec(v_stx_772_);
                        return v___x_786_;
                    }
                }
            }
            1 => {
                v___x_791_ = leanh::lean_unsigned_to_nat(0);
                v___x_792_ = l_Lean_Syntax_getArg(v_stx_772_, v___x_791_);
                leanh::lean_dec(v_stx_772_);
                if v_isShared_790_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_789_, 1);
                    v___x_794_ = v___x_789_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_799_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_787_);
                    v___x_794_ = v_reuseFailAlloc_799_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_795_ = leanh::lean_box(0);
                v___x_796_ = l_Lean_Elab_Term_elabTermEnsuringType(
                    v___x_792_, v___x_794_, v___x_783_, v___x_783_, v___x_795_, v_a_775_, v_a_776_,
                    v_a_777_, v_a_778_, v_a_779_, v_a_780_,
                );
                if leanh::lean_obj_tag(v___x_796_) == 0 {
                    v_a_797_ = leanh::lean_ctor_get(v___x_796_, 0);
                    leanh::lean_inc(v_a_797_);
                    leanh::lean_dec_ref_known(v___x_796_, 1);
                    v___x_798_ = l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(
                        v_dec_773_, v_a_797_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_,
                        v_a_779_, v_a_780_,
                    );
                    return v___x_798_;
                } else {
                    leanh::lean_dec_ref(v_dec_773_);
                    return v___x_796_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoExpr___boxed(
    mut v_stx_801_: *mut leanh::LeanObject,
    mut v_dec_802_: *mut leanh::LeanObject,
    mut v_a_803_: *mut leanh::LeanObject,
    mut v_a_804_: *mut leanh::LeanObject,
    mut v_a_805_: *mut leanh::LeanObject,
    mut v_a_806_: *mut leanh::LeanObject,
    mut v_a_807_: *mut leanh::LeanObject,
    mut v_a_808_: *mut leanh::LeanObject,
    mut v_a_809_: *mut leanh::LeanObject,
    mut v_a_810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_811_ = l_Lean_Elab_Do_elabDoExpr(
        v_stx_801_, v_dec_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_,
        v_a_809_,
    );
    leanh::lean_dec(v_a_809_);
    leanh::lean_dec_ref(v_a_808_);
    leanh::lean_dec(v_a_807_);
    leanh::lean_dec_ref(v_a_806_);
    leanh::lean_dec(v_a_805_);
    leanh::lean_dec_ref(v_a_804_);
    leanh::lean_dec_ref(v_a_803_);
    return v_res_811_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1()
-> *mut leanh::LeanObject {
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_819_ = l_Lean_Elab_Do_doElemElabAttribute;
    v___x_820_ = l_Lean_Elab_Do_elabDoExpr___closed__1;
    v___x_821_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___closed__1;
    v___x_822_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Do_elabDoExpr___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_823_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_819_, v___x_820_, v___x_821_, v___x_822_,
    );
    return v___x_823_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1___boxed(
    mut v_a_824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_825_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1();
    return v_res_825_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoNested(
    mut v_stx_832_: *mut leanh::LeanObject,
    mut v_dec_833_: *mut leanh::LeanObject,
    mut v_a_834_: *mut leanh::LeanObject,
    mut v_a_835_: *mut leanh::LeanObject,
    mut v_a_836_: *mut leanh::LeanObject,
    mut v_a_837_: *mut leanh::LeanObject,
    mut v_a_838_: *mut leanh::LeanObject,
    mut v_a_839_: *mut leanh::LeanObject,
    mut v_a_840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: u8 = 0;
    v___x_842_ = l_Lean_Elab_Do_elabDoNested___closed__1;
    leanh::lean_inc(v_stx_832_);
    v___x_843_ = l_Lean_Syntax_isOfKind(v_stx_832_, v___x_842_);
    if v___x_843_ == 0 {
        let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_dec_833_);
        leanh::lean_dec(v_stx_832_);
        v___x_844_ =
            l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
        return v___x_844_;
    } else {
        let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_845_ = leanh::lean_unsigned_to_nat(1);
        v___x_846_ = l_Lean_Syntax_getArg(v_stx_832_, v___x_845_);
        leanh::lean_dec(v_stx_832_);
        v___x_847_ = l_Lean_Elab_Do_elabDoSeq(
            v___x_846_, v_dec_833_, v___x_843_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_,
            v_a_839_, v_a_840_,
        );
        return v___x_847_;
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoNested___boxed(
    mut v_stx_848_: *mut leanh::LeanObject,
    mut v_dec_849_: *mut leanh::LeanObject,
    mut v_a_850_: *mut leanh::LeanObject,
    mut v_a_851_: *mut leanh::LeanObject,
    mut v_a_852_: *mut leanh::LeanObject,
    mut v_a_853_: *mut leanh::LeanObject,
    mut v_a_854_: *mut leanh::LeanObject,
    mut v_a_855_: *mut leanh::LeanObject,
    mut v_a_856_: *mut leanh::LeanObject,
    mut v_a_857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_858_ = l_Lean_Elab_Do_elabDoNested(
        v_stx_848_, v_dec_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_,
        v_a_856_,
    );
    leanh::lean_dec(v_a_856_);
    leanh::lean_dec_ref(v_a_855_);
    leanh::lean_dec(v_a_854_);
    leanh::lean_dec_ref(v_a_853_);
    leanh::lean_dec(v_a_852_);
    leanh::lean_dec_ref(v_a_851_);
    leanh::lean_dec_ref(v_a_850_);
    return v_res_858_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1()
-> *mut leanh::LeanObject {
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_866_ = l_Lean_Elab_Do_doElemElabAttribute;
    v___x_867_ = l_Lean_Elab_Do_elabDoNested___closed__1;
    v___x_868_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___closed__1;
    v___x_869_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Do_elabDoNested___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_870_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_866_, v___x_867_, v___x_868_, v___x_869_,
    );
    return v___x_870_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1___boxed(
    mut v_a_871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_872_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1();
    return v_res_872_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoUnless___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_895_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_895_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoUnless(
    mut v_stx_911_: *mut leanh::LeanObject,
    mut v_dec_912_: *mut leanh::LeanObject,
    mut v_a_913_: *mut leanh::LeanObject,
    mut v_a_914_: *mut leanh::LeanObject,
    mut v_a_915_: *mut leanh::LeanObject,
    mut v_a_916_: *mut leanh::LeanObject,
    mut v_a_917_: *mut leanh::LeanObject,
    mut v_a_918_: *mut leanh::LeanObject,
    mut v_a_919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: u8 = 0;
    v___x_921_ = l_Lean_Elab_Do_elabDoUnless___closed__1;
    leanh::lean_inc(v_stx_911_);
    v___x_922_ = l_Lean_Syntax_isOfKind(v_stx_911_, v___x_921_);
    if v___x_922_ == 0 {
        let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_dec_912_);
        leanh::lean_dec(v_stx_911_);
        v___x_923_ =
            l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
        return v___x_923_;
    } else {
        let mut v_ref_924_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tk_926_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_931_: u8 = 0;
        let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_946_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ref_924_ = leanh::lean_ctor_get(v_a_918_, 5);
        v___x_925_ = leanh::lean_unsigned_to_nat(0);
        v_tk_926_ = l_Lean_Syntax_getArg(v_stx_911_, v___x_925_);
        v___x_927_ = leanh::lean_unsigned_to_nat(1);
        v___x_928_ = l_Lean_Syntax_getArg(v_stx_911_, v___x_927_);
        v___x_929_ = leanh::lean_unsigned_to_nat(3);
        v___x_930_ = l_Lean_Syntax_getArg(v_stx_911_, v___x_929_);
        leanh::lean_dec(v_stx_911_);
        v___x_931_ = 0;
        v___x_932_ = l_Lean_SourceInfo_fromRef(v_ref_924_, v___x_931_);
        v___x_933_ = l_Lean_Elab_Do_elabDoUnless___closed__3;
        v___x_934_ = l_Lean_Elab_Do_elabDoUnless___closed__4;
        leanh::lean_inc_n(v___x_932_, 10);
        v___x_935_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_935_, 0, v___x_932_);
        leanh::lean_ctor_set(v___x_935_, 1, v___x_934_);
        v___x_936_ = l_Lean_Elab_Do_elabDoUnless___closed__6;
        v___x_937_ = l_Lean_Elab_Do_elabDoUnless___closed__8;
        v___x_938_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoUnless___closed__9),
            core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoUnless___closed__9_once),
            _init_l_Lean_Elab_Do_elabDoUnless___closed__9,
        );
        v___x_939_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_939_, 0, v___x_932_);
        leanh::lean_ctor_set(v___x_939_, 1, v___x_937_);
        leanh::lean_ctor_set(v___x_939_, 2, v___x_938_);
        leanh::lean_inc_ref_n(v___x_939_, 2);
        v___x_940_ = l_Lean_Syntax_node2(v___x_932_, v___x_936_, v___x_939_, v___x_928_);
        v___x_941_ = l_Lean_Elab_Do_elabDoUnless___closed__10;
        v___x_942_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_942_, 0, v___x_932_);
        leanh::lean_ctor_set(v___x_942_, 1, v___x_941_);
        v___x_943_ = l_Lean_Elab_Do_elabDoUnless___closed__12;
        v___x_944_ = l_Lean_Elab_Do_elabDoUnless___closed__14;
        v___x_945_ = l_Lean_Elab_Do_elabDoSkip___closed__5;
        v___x_946_ = l_Lean_SourceInfo_fromRef(v_tk_926_, v___x_922_);
        leanh::lean_dec(v_tk_926_);
        v___x_947_ = l_Lean_Elab_Do_elabDoUnless___closed__15;
        v___x_948_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_948_, 0, v___x_946_);
        leanh::lean_ctor_set(v___x_948_, 1, v___x_947_);
        v___x_949_ = l_Lean_Syntax_node1(v___x_932_, v___x_945_, v___x_948_);
        v___x_950_ = l_Lean_Syntax_node2(v___x_932_, v___x_944_, v___x_949_, v___x_939_);
        v___x_951_ = l_Lean_Syntax_node1(v___x_932_, v___x_937_, v___x_950_);
        v___x_952_ = l_Lean_Syntax_node1(v___x_932_, v___x_943_, v___x_951_);
        v___x_953_ = l_Lean_Elab_Do_elabDoUnless___closed__16;
        v___x_954_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_954_, 0, v___x_932_);
        leanh::lean_ctor_set(v___x_954_, 1, v___x_953_);
        v___x_955_ = l_Lean_Syntax_node2(v___x_932_, v___x_937_, v___x_954_, v___x_930_);
        v___x_956_ = l_Lean_Syntax_node6(
            v___x_932_, v___x_933_, v___x_935_, v___x_940_, v___x_942_, v___x_952_, v___x_939_,
            v___x_955_,
        );
        v___x_957_ = l_Lean_Elab_Do_elabDoElem(
            v___x_956_, v_dec_912_, v___x_922_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_,
            v_a_918_, v_a_919_,
        );
        return v___x_957_;
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoUnless___boxed(
    mut v_stx_958_: *mut leanh::LeanObject,
    mut v_dec_959_: *mut leanh::LeanObject,
    mut v_a_960_: *mut leanh::LeanObject,
    mut v_a_961_: *mut leanh::LeanObject,
    mut v_a_962_: *mut leanh::LeanObject,
    mut v_a_963_: *mut leanh::LeanObject,
    mut v_a_964_: *mut leanh::LeanObject,
    mut v_a_965_: *mut leanh::LeanObject,
    mut v_a_966_: *mut leanh::LeanObject,
    mut v_a_967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_968_ = l_Lean_Elab_Do_elabDoUnless(
        v_stx_958_, v_dec_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_,
        v_a_966_,
    );
    leanh::lean_dec(v_a_966_);
    leanh::lean_dec_ref(v_a_965_);
    leanh::lean_dec(v_a_964_);
    leanh::lean_dec_ref(v_a_963_);
    leanh::lean_dec(v_a_962_);
    leanh::lean_dec_ref(v_a_961_);
    leanh::lean_dec_ref(v_a_960_);
    return v_res_968_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1()
-> *mut leanh::LeanObject {
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_976_ = l_Lean_Elab_Do_doElemElabAttribute;
    v___x_977_ = l_Lean_Elab_Do_elabDoUnless___closed__1;
    v___x_978_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___closed__1;
    v___x_979_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Do_elabDoUnless___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_980_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_976_, v___x_977_, v___x_978_, v___x_979_,
    );
    return v___x_980_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1___boxed(
    mut v_a_981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_982_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1();
    return v_res_982_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoDbgTrace___lam__0(
    mut v___x_986_: *mut leanh::LeanObject,
    mut v___x_987_: *mut leanh::LeanObject,
    mut v___x_988_: *mut leanh::LeanObject,
    mut v___x_989_: *mut leanh::LeanObject,
    mut v_a_990_: *mut leanh::LeanObject,
    mut v___x_991_: u8,
    mut v_body_992_: *mut leanh::LeanObject,
    mut v___y_993_: *mut leanh::LeanObject,
    mut v___y_994_: *mut leanh::LeanObject,
    mut v___y_995_: *mut leanh::LeanObject,
    mut v___y_996_: *mut leanh::LeanObject,
    mut v___y_997_: *mut leanh::LeanObject,
    mut v___y_998_: *mut leanh::LeanObject,
    mut v___y_999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: u8 = 0;
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1001_ = leanh::lean_ctor_get(v___y_998_, 5);
    v___x_1002_ = 0;
    v___x_1003_ = l_Lean_SourceInfo_fromRef(v_ref_1001_, v___x_1002_);
    v___x_1004_ = l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__0;
    v___x_1005_ = l_Lean_Name_mkStr4(v___x_986_, v___x_987_, v___x_988_, v___x_1004_);
    v___x_1006_ = l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__1;
    leanh::lean_inc_n(v___x_1003_, 2);
    v___x_1007_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1007_, 0, v___x_1003_);
    leanh::lean_ctor_set(v___x_1007_, 1, v___x_1006_);
    v___x_1008_ = l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__2;
    v___x_1009_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1009_, 0, v___x_1003_);
    leanh::lean_ctor_set(v___x_1009_, 1, v___x_1008_);
    v___x_1010_ = l_Lean_Syntax_node4(
        v___x_1003_,
        v___x_1005_,
        v___x_1007_,
        v___x_989_,
        v___x_1009_,
        v_body_992_,
    );
    v___x_1011_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1011_, 0, v_a_990_);
    v___x_1012_ = l_Lean_Elab_Term_elabTerm(
        v___x_1010_,
        v___x_1011_,
        v___x_991_,
        v___x_991_,
        v___y_994_,
        v___y_995_,
        v___y_996_,
        v___y_997_,
        v___y_998_,
        v___y_999_,
    );
    return v___x_1012_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoDbgTrace___lam__0___boxed(
    mut v___x_1013_: *mut leanh::LeanObject,
    mut v___x_1014_: *mut leanh::LeanObject,
    mut v___x_1015_: *mut leanh::LeanObject,
    mut v___x_1016_: *mut leanh::LeanObject,
    mut v_a_1017_: *mut leanh::LeanObject,
    mut v___x_1018_: *mut leanh::LeanObject,
    mut v_body_1019_: *mut leanh::LeanObject,
    mut v___y_1020_: *mut leanh::LeanObject,
    mut v___y_1021_: *mut leanh::LeanObject,
    mut v___y_1022_: *mut leanh::LeanObject,
    mut v___y_1023_: *mut leanh::LeanObject,
    mut v___y_1024_: *mut leanh::LeanObject,
    mut v___y_1025_: *mut leanh::LeanObject,
    mut v___y_1026_: *mut leanh::LeanObject,
    mut v___y_1027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3724__boxed_1028_: u8 = 0;
    let mut v_res_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3724__boxed_1028_ = (leanh::lean_unbox(v___x_1018_) as u8);
    v_res_1029_ = l_Lean_Elab_Do_elabDoDbgTrace___lam__0(
        v___x_1013_,
        v___x_1014_,
        v___x_1015_,
        v___x_1016_,
        v_a_1017_,
        v___x_3724__boxed_1028_,
        v_body_1019_,
        v___y_1020_,
        v___y_1021_,
        v___y_1022_,
        v___y_1023_,
        v___y_1024_,
        v___y_1025_,
        v___y_1026_,
    );
    leanh::lean_dec(v___y_1026_);
    leanh::lean_dec_ref(v___y_1025_);
    leanh::lean_dec(v___y_1024_);
    leanh::lean_dec_ref(v___y_1023_);
    leanh::lean_dec(v___y_1022_);
    leanh::lean_dec_ref(v___y_1021_);
    leanh::lean_dec_ref(v___y_1020_);
    return v_res_1029_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoDbgTrace___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1039_ = l_Lean_Elab_Do_elabDoDbgTrace___closed__3;
    v___x_1040_ = l_Lean_MessageData_ofFormat(v___x_1039_);
    return v___x_1040_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoDbgTrace(
    mut v_stx_1041_: *mut leanh::LeanObject,
    mut v_dec_1042_: *mut leanh::LeanObject,
    mut v_a_1043_: *mut leanh::LeanObject,
    mut v_a_1044_: *mut leanh::LeanObject,
    mut v_a_1045_: *mut leanh::LeanObject,
    mut v_a_1046_: *mut leanh::LeanObject,
    mut v_a_1047_: *mut leanh::LeanObject,
    mut v_a_1048_: *mut leanh::LeanObject,
    mut v_a_1049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: u8 = 0;
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doBlockResultType_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1075_: u8 = 0;
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1079_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1051_ = l_Lean_Elab_Do_elabDoSkip___closed__0;
                v___x_1052_ = l_Lean_Elab_Do_elabDoSkip___closed__1;
                v___x_1053_ = l_Lean_Elab_Do_elabDoSkip___closed__2;
                v___x_1054_ = l_Lean_Elab_Do_elabDoDbgTrace___closed__1;
                leanh::lean_inc(v_stx_1041_);
                v___x_1055_ = l_Lean_Syntax_isOfKind(v_stx_1041_, v___x_1054_);
                if v___x_1055_ == 0 {
                    leanh::lean_dec_ref(v_dec_1042_);
                    leanh::lean_dec(v_stx_1041_);
                    v___x_1056_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
                    return v___x_1056_;
                } else {
                    v_doBlockResultType_1057_ = leanh::lean_ctor_get(v_a_1043_, 3);
                    leanh::lean_inc_ref(v_doBlockResultType_1057_);
                    v___x_1058_ = l_Lean_Elab_Do_mkMonadApp(
                        v_doBlockResultType_1057_,
                        v_a_1043_,
                        v_a_1044_,
                        v_a_1045_,
                        v_a_1046_,
                        v_a_1047_,
                        v_a_1048_,
                        v_a_1049_,
                    );
                    if leanh::lean_obj_tag(v___x_1058_) == 0 {
                        v_a_1059_ = leanh::lean_ctor_get(v___x_1058_, 0);
                        leanh::lean_inc(v_a_1059_);
                        leanh::lean_dec_ref_known(v___x_1058_, 1);
                        v___x_1060_ = leanh::lean_unsigned_to_nat(0);
                        v_tk_1061_ = l_Lean_Syntax_getArg(v_stx_1041_, v___x_1060_);
                        v___x_1062_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(
                            v_dec_1042_,
                            v_tk_1061_,
                            v_a_1043_,
                            v_a_1044_,
                            v_a_1045_,
                            v_a_1046_,
                            v_a_1047_,
                            v_a_1048_,
                            v_a_1049_,
                        );
                        leanh::lean_dec(v_tk_1061_);
                        if leanh::lean_obj_tag(v___x_1062_) == 0 {
                            v_a_1063_ = leanh::lean_ctor_get(v___x_1062_, 0);
                            leanh::lean_inc(v_a_1063_);
                            leanh::lean_dec_ref_known(v___x_1062_, 1);
                            v___x_1064_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1065_ = l_Lean_Syntax_getArg(v_stx_1041_, v___x_1064_);
                            leanh::lean_dec(v_stx_1041_);
                            v___x_1066_ = leanh::lean_box((v___x_1055_) as usize);
                            v___f_1067_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_Do_elabDoDbgTrace___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                15,
                                6,
                            );
                            leanh::lean_closure_set(v___f_1067_, 0, v___x_1051_);
                            leanh::lean_closure_set(v___f_1067_, 1, v___x_1052_);
                            leanh::lean_closure_set(v___f_1067_, 2, v___x_1053_);
                            leanh::lean_closure_set(v___f_1067_, 3, v___x_1065_);
                            leanh::lean_closure_set(v___f_1067_, 4, v_a_1059_);
                            leanh::lean_closure_set(v___f_1067_, 5, v___x_1066_);
                            v___x_1068_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoDbgTrace___closed__4),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Do_elabDoDbgTrace___closed__4_once
                                ),
                                _init_l_Lean_Elab_Do_elabDoDbgTrace___closed__4,
                            );
                            v___x_1069_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed
                                    as *mut core::ffi::c_void,
                                9,
                                1,
                            );
                            leanh::lean_closure_set(v___x_1069_, 0, v_a_1063_);
                            v___x_1070_ = leanh::lean_box(0);
                            v___x_1071_ = l_Lean_Elab_Do_doElabToSyntax___redArg(
                                v___x_1068_,
                                v___x_1069_,
                                v___f_1067_,
                                v___x_1070_,
                                v_a_1043_,
                                v_a_1044_,
                                v_a_1045_,
                                v_a_1046_,
                                v_a_1047_,
                                v_a_1048_,
                                v_a_1049_,
                            );
                            return v___x_1071_;
                        } else {
                            leanh::lean_dec(v_a_1059_);
                            leanh::lean_dec(v_stx_1041_);
                            v_a_1072_ = leanh::lean_ctor_get(v___x_1062_, 0);
                            v_isSharedCheck_1079_ =
                                (!leanh::lean_is_exclusive(v___x_1062_)) as u8;
                            if v_isSharedCheck_1079_ == 0 {
                                v___x_1074_ = v___x_1062_;
                                v_isShared_1075_ = v_isSharedCheck_1079_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1072_);
                                leanh::lean_dec(v___x_1062_);
                                v___x_1074_ = leanh::lean_box(0);
                                v_isShared_1075_ = v_isSharedCheck_1079_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_dec_1042_);
                        leanh::lean_dec(v_stx_1041_);
                        return v___x_1058_;
                    }
                }
            }
            1 => {
                if v_isShared_1075_ == 0 {
                    v___x_1077_ = v___x_1074_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1078_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
                    v___x_1077_ = v_reuseFailAlloc_1078_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1077_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoDbgTrace___boxed(
    mut v_stx_1080_: *mut leanh::LeanObject,
    mut v_dec_1081_: *mut leanh::LeanObject,
    mut v_a_1082_: *mut leanh::LeanObject,
    mut v_a_1083_: *mut leanh::LeanObject,
    mut v_a_1084_: *mut leanh::LeanObject,
    mut v_a_1085_: *mut leanh::LeanObject,
    mut v_a_1086_: *mut leanh::LeanObject,
    mut v_a_1087_: *mut leanh::LeanObject,
    mut v_a_1088_: *mut leanh::LeanObject,
    mut v_a_1089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1090_ = l_Lean_Elab_Do_elabDoDbgTrace(
        v_stx_1080_,
        v_dec_1081_,
        v_a_1082_,
        v_a_1083_,
        v_a_1084_,
        v_a_1085_,
        v_a_1086_,
        v_a_1087_,
        v_a_1088_,
    );
    leanh::lean_dec(v_a_1088_);
    leanh::lean_dec_ref(v_a_1087_);
    leanh::lean_dec(v_a_1086_);
    leanh::lean_dec_ref(v_a_1085_);
    leanh::lean_dec(v_a_1084_);
    leanh::lean_dec_ref(v_a_1083_);
    leanh::lean_dec_ref(v_a_1082_);
    return v_res_1090_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1()
-> *mut leanh::LeanObject {
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1098_ = l_Lean_Elab_Do_doElemElabAttribute;
    v___x_1099_ = l_Lean_Elab_Do_elabDoDbgTrace___closed__1;
    v___x_1100_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___closed__1;
    v___x_1101_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Do_elabDoDbgTrace___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1102_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1098_,
        v___x_1099_,
        v___x_1100_,
        v___x_1101_,
    );
    return v___x_1102_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1___boxed(
    mut v_a_1103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1104_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1();
    return v_res_1104_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoAssert___lam__0(
    mut v___x_1107_: *mut leanh::LeanObject,
    mut v___x_1108_: *mut leanh::LeanObject,
    mut v___x_1109_: *mut leanh::LeanObject,
    mut v___x_1110_: *mut leanh::LeanObject,
    mut v_a_1111_: *mut leanh::LeanObject,
    mut v___x_1112_: u8,
    mut v_body_1113_: *mut leanh::LeanObject,
    mut v___y_1114_: *mut leanh::LeanObject,
    mut v___y_1115_: *mut leanh::LeanObject,
    mut v___y_1116_: *mut leanh::LeanObject,
    mut v___y_1117_: *mut leanh::LeanObject,
    mut v___y_1118_: *mut leanh::LeanObject,
    mut v___y_1119_: *mut leanh::LeanObject,
    mut v___y_1120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: u8 = 0;
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1122_ = leanh::lean_ctor_get(v___y_1119_, 5);
    v___x_1123_ = 0;
    v___x_1124_ = l_Lean_SourceInfo_fromRef(v_ref_1122_, v___x_1123_);
    v___x_1125_ = l_Lean_Elab_Do_elabDoAssert___lam__0___closed__0;
    v___x_1126_ = l_Lean_Name_mkStr4(v___x_1107_, v___x_1108_, v___x_1109_, v___x_1125_);
    v___x_1127_ = l_Lean_Elab_Do_elabDoAssert___lam__0___closed__1;
    leanh::lean_inc_n(v___x_1124_, 2);
    v___x_1128_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1128_, 0, v___x_1124_);
    leanh::lean_ctor_set(v___x_1128_, 1, v___x_1127_);
    v___x_1129_ = l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__2;
    v___x_1130_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1130_, 0, v___x_1124_);
    leanh::lean_ctor_set(v___x_1130_, 1, v___x_1129_);
    v___x_1131_ = l_Lean_Syntax_node4(
        v___x_1124_,
        v___x_1126_,
        v___x_1128_,
        v___x_1110_,
        v___x_1130_,
        v_body_1113_,
    );
    v___x_1132_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1132_, 0, v_a_1111_);
    v___x_1133_ = l_Lean_Elab_Term_elabTerm(
        v___x_1131_,
        v___x_1132_,
        v___x_1112_,
        v___x_1112_,
        v___y_1115_,
        v___y_1116_,
        v___y_1117_,
        v___y_1118_,
        v___y_1119_,
        v___y_1120_,
    );
    return v___x_1133_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoAssert___lam__0___boxed(
    mut v___x_1134_: *mut leanh::LeanObject,
    mut v___x_1135_: *mut leanh::LeanObject,
    mut v___x_1136_: *mut leanh::LeanObject,
    mut v___x_1137_: *mut leanh::LeanObject,
    mut v_a_1138_: *mut leanh::LeanObject,
    mut v___x_1139_: *mut leanh::LeanObject,
    mut v_body_1140_: *mut leanh::LeanObject,
    mut v___y_1141_: *mut leanh::LeanObject,
    mut v___y_1142_: *mut leanh::LeanObject,
    mut v___y_1143_: *mut leanh::LeanObject,
    mut v___y_1144_: *mut leanh::LeanObject,
    mut v___y_1145_: *mut leanh::LeanObject,
    mut v___y_1146_: *mut leanh::LeanObject,
    mut v___y_1147_: *mut leanh::LeanObject,
    mut v___y_1148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3713__boxed_1149_: u8 = 0;
    let mut v_res_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3713__boxed_1149_ = (leanh::lean_unbox(v___x_1139_) as u8);
    v_res_1150_ = l_Lean_Elab_Do_elabDoAssert___lam__0(
        v___x_1134_,
        v___x_1135_,
        v___x_1136_,
        v___x_1137_,
        v_a_1138_,
        v___x_3713__boxed_1149_,
        v_body_1140_,
        v___y_1141_,
        v___y_1142_,
        v___y_1143_,
        v___y_1144_,
        v___y_1145_,
        v___y_1146_,
        v___y_1147_,
    );
    leanh::lean_dec(v___y_1147_);
    leanh::lean_dec_ref(v___y_1146_);
    leanh::lean_dec(v___y_1145_);
    leanh::lean_dec_ref(v___y_1144_);
    leanh::lean_dec(v___y_1143_);
    leanh::lean_dec_ref(v___y_1142_);
    leanh::lean_dec_ref(v___y_1141_);
    return v_res_1150_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoAssert___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1160_ = l_Lean_Elab_Do_elabDoAssert___closed__3;
    v___x_1161_ = l_Lean_MessageData_ofFormat(v___x_1160_);
    return v___x_1161_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoAssert(
    mut v_stx_1162_: *mut leanh::LeanObject,
    mut v_dec_1163_: *mut leanh::LeanObject,
    mut v_a_1164_: *mut leanh::LeanObject,
    mut v_a_1165_: *mut leanh::LeanObject,
    mut v_a_1166_: *mut leanh::LeanObject,
    mut v_a_1167_: *mut leanh::LeanObject,
    mut v_a_1168_: *mut leanh::LeanObject,
    mut v_a_1169_: *mut leanh::LeanObject,
    mut v_a_1170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: u8 = 0;
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doBlockResultType_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1196_: u8 = 0;
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1200_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1172_ = l_Lean_Elab_Do_elabDoSkip___closed__0;
                v___x_1173_ = l_Lean_Elab_Do_elabDoSkip___closed__1;
                v___x_1174_ = l_Lean_Elab_Do_elabDoSkip___closed__2;
                v___x_1175_ = l_Lean_Elab_Do_elabDoAssert___closed__1;
                leanh::lean_inc(v_stx_1162_);
                v___x_1176_ = l_Lean_Syntax_isOfKind(v_stx_1162_, v___x_1175_);
                if v___x_1176_ == 0 {
                    leanh::lean_dec_ref(v_dec_1163_);
                    leanh::lean_dec(v_stx_1162_);
                    v___x_1177_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
                    return v___x_1177_;
                } else {
                    v_doBlockResultType_1178_ = leanh::lean_ctor_get(v_a_1164_, 3);
                    leanh::lean_inc_ref(v_doBlockResultType_1178_);
                    v___x_1179_ = l_Lean_Elab_Do_mkMonadApp(
                        v_doBlockResultType_1178_,
                        v_a_1164_,
                        v_a_1165_,
                        v_a_1166_,
                        v_a_1167_,
                        v_a_1168_,
                        v_a_1169_,
                        v_a_1170_,
                    );
                    if leanh::lean_obj_tag(v___x_1179_) == 0 {
                        v_a_1180_ = leanh::lean_ctor_get(v___x_1179_, 0);
                        leanh::lean_inc(v_a_1180_);
                        leanh::lean_dec_ref_known(v___x_1179_, 1);
                        v___x_1181_ = leanh::lean_unsigned_to_nat(0);
                        v_tk_1182_ = l_Lean_Syntax_getArg(v_stx_1162_, v___x_1181_);
                        v___x_1183_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(
                            v_dec_1163_,
                            v_tk_1182_,
                            v_a_1164_,
                            v_a_1165_,
                            v_a_1166_,
                            v_a_1167_,
                            v_a_1168_,
                            v_a_1169_,
                            v_a_1170_,
                        );
                        leanh::lean_dec(v_tk_1182_);
                        if leanh::lean_obj_tag(v___x_1183_) == 0 {
                            v_a_1184_ = leanh::lean_ctor_get(v___x_1183_, 0);
                            leanh::lean_inc(v_a_1184_);
                            leanh::lean_dec_ref_known(v___x_1183_, 1);
                            v___x_1185_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1186_ = l_Lean_Syntax_getArg(v_stx_1162_, v___x_1185_);
                            leanh::lean_dec(v_stx_1162_);
                            v___x_1187_ = leanh::lean_box((v___x_1176_) as usize);
                            v___f_1188_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_Do_elabDoAssert___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                15,
                                6,
                            );
                            leanh::lean_closure_set(v___f_1188_, 0, v___x_1172_);
                            leanh::lean_closure_set(v___f_1188_, 1, v___x_1173_);
                            leanh::lean_closure_set(v___f_1188_, 2, v___x_1174_);
                            leanh::lean_closure_set(v___f_1188_, 3, v___x_1186_);
                            leanh::lean_closure_set(v___f_1188_, 4, v_a_1180_);
                            leanh::lean_closure_set(v___f_1188_, 5, v___x_1187_);
                            v___x_1189_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoAssert___closed__4),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Do_elabDoAssert___closed__4_once
                                ),
                                _init_l_Lean_Elab_Do_elabDoAssert___closed__4,
                            );
                            v___x_1190_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed
                                    as *mut core::ffi::c_void,
                                9,
                                1,
                            );
                            leanh::lean_closure_set(v___x_1190_, 0, v_a_1184_);
                            v___x_1191_ = leanh::lean_box(0);
                            v___x_1192_ = l_Lean_Elab_Do_doElabToSyntax___redArg(
                                v___x_1189_,
                                v___x_1190_,
                                v___f_1188_,
                                v___x_1191_,
                                v_a_1164_,
                                v_a_1165_,
                                v_a_1166_,
                                v_a_1167_,
                                v_a_1168_,
                                v_a_1169_,
                                v_a_1170_,
                            );
                            return v___x_1192_;
                        } else {
                            leanh::lean_dec(v_a_1180_);
                            leanh::lean_dec(v_stx_1162_);
                            v_a_1193_ = leanh::lean_ctor_get(v___x_1183_, 0);
                            v_isSharedCheck_1200_ =
                                (!leanh::lean_is_exclusive(v___x_1183_)) as u8;
                            if v_isSharedCheck_1200_ == 0 {
                                v___x_1195_ = v___x_1183_;
                                v_isShared_1196_ = v_isSharedCheck_1200_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1193_);
                                leanh::lean_dec(v___x_1183_);
                                v___x_1195_ = leanh::lean_box(0);
                                v_isShared_1196_ = v_isSharedCheck_1200_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_dec_1163_);
                        leanh::lean_dec(v_stx_1162_);
                        return v___x_1179_;
                    }
                }
            }
            1 => {
                if v_isShared_1196_ == 0 {
                    v___x_1198_ = v___x_1195_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1199_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
                    v___x_1198_ = v_reuseFailAlloc_1199_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1198_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoAssert___boxed(
    mut v_stx_1201_: *mut leanh::LeanObject,
    mut v_dec_1202_: *mut leanh::LeanObject,
    mut v_a_1203_: *mut leanh::LeanObject,
    mut v_a_1204_: *mut leanh::LeanObject,
    mut v_a_1205_: *mut leanh::LeanObject,
    mut v_a_1206_: *mut leanh::LeanObject,
    mut v_a_1207_: *mut leanh::LeanObject,
    mut v_a_1208_: *mut leanh::LeanObject,
    mut v_a_1209_: *mut leanh::LeanObject,
    mut v_a_1210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1211_ = l_Lean_Elab_Do_elabDoAssert(
        v_stx_1201_,
        v_dec_1202_,
        v_a_1203_,
        v_a_1204_,
        v_a_1205_,
        v_a_1206_,
        v_a_1207_,
        v_a_1208_,
        v_a_1209_,
    );
    leanh::lean_dec(v_a_1209_);
    leanh::lean_dec_ref(v_a_1208_);
    leanh::lean_dec(v_a_1207_);
    leanh::lean_dec_ref(v_a_1206_);
    leanh::lean_dec(v_a_1205_);
    leanh::lean_dec_ref(v_a_1204_);
    leanh::lean_dec_ref(v_a_1203_);
    return v_res_1211_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1()
-> *mut leanh::LeanObject {
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1219_ = l_Lean_Elab_Do_doElemElabAttribute;
    v___x_1220_ = l_Lean_Elab_Do_elabDoAssert___closed__1;
    v___x_1221_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___closed__1;
    v___x_1222_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Do_elabDoAssert___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1223_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1219_,
        v___x_1220_,
        v___x_1221_,
        v___x_1222_,
    );
    return v___x_1223_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1___boxed(
    mut v_a_1224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1225_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1();
    return v_res_1225_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoDebugAssert___lam__0(
    mut v___x_1228_: *mut leanh::LeanObject,
    mut v___x_1229_: *mut leanh::LeanObject,
    mut v___x_1230_: *mut leanh::LeanObject,
    mut v___x_1231_: *mut leanh::LeanObject,
    mut v_a_1232_: *mut leanh::LeanObject,
    mut v___x_1233_: u8,
    mut v_body_1234_: *mut leanh::LeanObject,
    mut v___y_1235_: *mut leanh::LeanObject,
    mut v___y_1236_: *mut leanh::LeanObject,
    mut v___y_1237_: *mut leanh::LeanObject,
    mut v___y_1238_: *mut leanh::LeanObject,
    mut v___y_1239_: *mut leanh::LeanObject,
    mut v___y_1240_: *mut leanh::LeanObject,
    mut v___y_1241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: u8 = 0;
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1243_ = leanh::lean_ctor_get(v___y_1240_, 5);
    v___x_1244_ = 0;
    v___x_1245_ = l_Lean_SourceInfo_fromRef(v_ref_1243_, v___x_1244_);
    v___x_1246_ = l_Lean_Elab_Do_elabDoDebugAssert___lam__0___closed__0;
    v___x_1247_ = l_Lean_Name_mkStr4(v___x_1228_, v___x_1229_, v___x_1230_, v___x_1246_);
    v___x_1248_ = l_Lean_Elab_Do_elabDoDebugAssert___lam__0___closed__1;
    leanh::lean_inc_n(v___x_1245_, 2);
    v___x_1249_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1249_, 0, v___x_1245_);
    leanh::lean_ctor_set(v___x_1249_, 1, v___x_1248_);
    v___x_1250_ = l_Lean_Elab_Do_elabDoDbgTrace___lam__0___closed__2;
    v___x_1251_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1251_, 0, v___x_1245_);
    leanh::lean_ctor_set(v___x_1251_, 1, v___x_1250_);
    v___x_1252_ = l_Lean_Syntax_node4(
        v___x_1245_,
        v___x_1247_,
        v___x_1249_,
        v___x_1231_,
        v___x_1251_,
        v_body_1234_,
    );
    v___x_1253_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1253_, 0, v_a_1232_);
    v___x_1254_ = l_Lean_Elab_Term_elabTerm(
        v___x_1252_,
        v___x_1253_,
        v___x_1233_,
        v___x_1233_,
        v___y_1236_,
        v___y_1237_,
        v___y_1238_,
        v___y_1239_,
        v___y_1240_,
        v___y_1241_,
    );
    return v___x_1254_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoDebugAssert___lam__0___boxed(
    mut v___x_1255_: *mut leanh::LeanObject,
    mut v___x_1256_: *mut leanh::LeanObject,
    mut v___x_1257_: *mut leanh::LeanObject,
    mut v___x_1258_: *mut leanh::LeanObject,
    mut v_a_1259_: *mut leanh::LeanObject,
    mut v___x_1260_: *mut leanh::LeanObject,
    mut v_body_1261_: *mut leanh::LeanObject,
    mut v___y_1262_: *mut leanh::LeanObject,
    mut v___y_1263_: *mut leanh::LeanObject,
    mut v___y_1264_: *mut leanh::LeanObject,
    mut v___y_1265_: *mut leanh::LeanObject,
    mut v___y_1266_: *mut leanh::LeanObject,
    mut v___y_1267_: *mut leanh::LeanObject,
    mut v___y_1268_: *mut leanh::LeanObject,
    mut v___y_1269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3713__boxed_1270_: u8 = 0;
    let mut v_res_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3713__boxed_1270_ = (leanh::lean_unbox(v___x_1260_) as u8);
    v_res_1271_ = l_Lean_Elab_Do_elabDoDebugAssert___lam__0(
        v___x_1255_,
        v___x_1256_,
        v___x_1257_,
        v___x_1258_,
        v_a_1259_,
        v___x_3713__boxed_1270_,
        v_body_1261_,
        v___y_1262_,
        v___y_1263_,
        v___y_1264_,
        v___y_1265_,
        v___y_1266_,
        v___y_1267_,
        v___y_1268_,
    );
    leanh::lean_dec(v___y_1268_);
    leanh::lean_dec_ref(v___y_1267_);
    leanh::lean_dec(v___y_1266_);
    leanh::lean_dec_ref(v___y_1265_);
    leanh::lean_dec(v___y_1264_);
    leanh::lean_dec_ref(v___y_1263_);
    leanh::lean_dec_ref(v___y_1262_);
    return v_res_1271_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoDebugAssert___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ = l_Lean_Elab_Do_elabDoDebugAssert___closed__3;
    v___x_1282_ = l_Lean_MessageData_ofFormat(v___x_1281_);
    return v___x_1282_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoDebugAssert(
    mut v_stx_1283_: *mut leanh::LeanObject,
    mut v_dec_1284_: *mut leanh::LeanObject,
    mut v_a_1285_: *mut leanh::LeanObject,
    mut v_a_1286_: *mut leanh::LeanObject,
    mut v_a_1287_: *mut leanh::LeanObject,
    mut v_a_1288_: *mut leanh::LeanObject,
    mut v_a_1289_: *mut leanh::LeanObject,
    mut v_a_1290_: *mut leanh::LeanObject,
    mut v_a_1291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: u8 = 0;
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doBlockResultType_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1317_: u8 = 0;
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1321_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1293_ = l_Lean_Elab_Do_elabDoSkip___closed__0;
                v___x_1294_ = l_Lean_Elab_Do_elabDoSkip___closed__1;
                v___x_1295_ = l_Lean_Elab_Do_elabDoSkip___closed__2;
                v___x_1296_ = l_Lean_Elab_Do_elabDoDebugAssert___closed__1;
                leanh::lean_inc(v_stx_1283_);
                v___x_1297_ = l_Lean_Syntax_isOfKind(v_stx_1283_, v___x_1296_);
                if v___x_1297_ == 0 {
                    leanh::lean_dec_ref(v_dec_1284_);
                    leanh::lean_dec(v_stx_1283_);
                    v___x_1298_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoSkip_spec__0___redArg();
                    return v___x_1298_;
                } else {
                    v_doBlockResultType_1299_ = leanh::lean_ctor_get(v_a_1285_, 3);
                    leanh::lean_inc_ref(v_doBlockResultType_1299_);
                    v___x_1300_ = l_Lean_Elab_Do_mkMonadApp(
                        v_doBlockResultType_1299_,
                        v_a_1285_,
                        v_a_1286_,
                        v_a_1287_,
                        v_a_1288_,
                        v_a_1289_,
                        v_a_1290_,
                        v_a_1291_,
                    );
                    if leanh::lean_obj_tag(v___x_1300_) == 0 {
                        v_a_1301_ = leanh::lean_ctor_get(v___x_1300_, 0);
                        leanh::lean_inc(v_a_1301_);
                        leanh::lean_dec_ref_known(v___x_1300_, 1);
                        v___x_1302_ = leanh::lean_unsigned_to_nat(0);
                        v_tk_1303_ = l_Lean_Syntax_getArg(v_stx_1283_, v___x_1302_);
                        v___x_1304_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(
                            v_dec_1284_,
                            v_tk_1303_,
                            v_a_1285_,
                            v_a_1286_,
                            v_a_1287_,
                            v_a_1288_,
                            v_a_1289_,
                            v_a_1290_,
                            v_a_1291_,
                        );
                        leanh::lean_dec(v_tk_1303_);
                        if leanh::lean_obj_tag(v___x_1304_) == 0 {
                            v_a_1305_ = leanh::lean_ctor_get(v___x_1304_, 0);
                            leanh::lean_inc(v_a_1305_);
                            leanh::lean_dec_ref_known(v___x_1304_, 1);
                            v___x_1306_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1307_ = l_Lean_Syntax_getArg(v_stx_1283_, v___x_1306_);
                            leanh::lean_dec(v_stx_1283_);
                            v___x_1308_ = leanh::lean_box((v___x_1297_) as usize);
                            v___f_1309_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_Do_elabDoDebugAssert___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                15,
                                6,
                            );
                            leanh::lean_closure_set(v___f_1309_, 0, v___x_1293_);
                            leanh::lean_closure_set(v___f_1309_, 1, v___x_1294_);
                            leanh::lean_closure_set(v___f_1309_, 2, v___x_1295_);
                            leanh::lean_closure_set(v___f_1309_, 3, v___x_1307_);
                            leanh::lean_closure_set(v___f_1309_, 4, v_a_1301_);
                            leanh::lean_closure_set(v___f_1309_, 5, v___x_1308_);
                            v___x_1310_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Do_elabDoDebugAssert___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Do_elabDoDebugAssert___closed__4_once
                                ),
                                _init_l_Lean_Elab_Do_elabDoDebugAssert___closed__4,
                            );
                            v___x_1311_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed
                                    as *mut core::ffi::c_void,
                                9,
                                1,
                            );
                            leanh::lean_closure_set(v___x_1311_, 0, v_a_1305_);
                            v___x_1312_ = leanh::lean_box(0);
                            v___x_1313_ = l_Lean_Elab_Do_doElabToSyntax___redArg(
                                v___x_1310_,
                                v___x_1311_,
                                v___f_1309_,
                                v___x_1312_,
                                v_a_1285_,
                                v_a_1286_,
                                v_a_1287_,
                                v_a_1288_,
                                v_a_1289_,
                                v_a_1290_,
                                v_a_1291_,
                            );
                            return v___x_1313_;
                        } else {
                            leanh::lean_dec(v_a_1301_);
                            leanh::lean_dec(v_stx_1283_);
                            v_a_1314_ = leanh::lean_ctor_get(v___x_1304_, 0);
                            v_isSharedCheck_1321_ =
                                (!leanh::lean_is_exclusive(v___x_1304_)) as u8;
                            if v_isSharedCheck_1321_ == 0 {
                                v___x_1316_ = v___x_1304_;
                                v_isShared_1317_ = v_isSharedCheck_1321_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1314_);
                                leanh::lean_dec(v___x_1304_);
                                v___x_1316_ = leanh::lean_box(0);
                                v_isShared_1317_ = v_isSharedCheck_1321_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_dec_1284_);
                        leanh::lean_dec(v_stx_1283_);
                        return v___x_1300_;
                    }
                }
            }
            1 => {
                if v_isShared_1317_ == 0 {
                    v___x_1319_ = v___x_1316_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1320_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
                    v___x_1319_ = v_reuseFailAlloc_1320_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1319_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoDebugAssert___boxed(
    mut v_stx_1322_: *mut leanh::LeanObject,
    mut v_dec_1323_: *mut leanh::LeanObject,
    mut v_a_1324_: *mut leanh::LeanObject,
    mut v_a_1325_: *mut leanh::LeanObject,
    mut v_a_1326_: *mut leanh::LeanObject,
    mut v_a_1327_: *mut leanh::LeanObject,
    mut v_a_1328_: *mut leanh::LeanObject,
    mut v_a_1329_: *mut leanh::LeanObject,
    mut v_a_1330_: *mut leanh::LeanObject,
    mut v_a_1331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1332_ = l_Lean_Elab_Do_elabDoDebugAssert(
        v_stx_1322_,
        v_dec_1323_,
        v_a_1324_,
        v_a_1325_,
        v_a_1326_,
        v_a_1327_,
        v_a_1328_,
        v_a_1329_,
        v_a_1330_,
    );
    leanh::lean_dec(v_a_1330_);
    leanh::lean_dec_ref(v_a_1329_);
    leanh::lean_dec(v_a_1328_);
    leanh::lean_dec_ref(v_a_1327_);
    leanh::lean_dec(v_a_1326_);
    leanh::lean_dec_ref(v_a_1325_);
    leanh::lean_dec_ref(v_a_1324_);
    return v_res_1332_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1()
-> *mut leanh::LeanObject {
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1340_ = l_Lean_Elab_Do_doElemElabAttribute;
    v___x_1341_ = l_Lean_Elab_Do_elabDoDebugAssert___closed__1;
    v___x_1342_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___closed__1;
    v___x_1343_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Do_elabDoDebugAssert___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1344_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1340_,
        v___x_1341_,
        v___x_1342_,
        v___x_1343_,
    );
    return v___x_1344_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1___boxed(
    mut v_a_1345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1346_ = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1();
    return v_res_1346_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_BuiltinDo_Misc(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoSkip___regBuiltin_Lean_Elab_Do_elabDoSkip__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoExpr___regBuiltin_Lean_Elab_Do_elabDoExpr__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoNested___regBuiltin_Lean_Elab_Do_elabDoNested__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoUnless___regBuiltin_Lean_Elab_Do_elabDoUnless__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDbgTrace___regBuiltin_Lean_Elab_Do_elabDoDbgTrace__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoAssert___regBuiltin_Lean_Elab_Do_elabDoAssert__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_Misc_0__Lean_Elab_Do_elabDoDebugAssert___regBuiltin_Lean_Elab_Do_elabDoDebugAssert__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_BuiltinDo_Misc(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Do(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_BuiltinDo_Misc(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Do_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Do(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_Misc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_BuiltinDo_Misc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_BuiltinDo_Misc(builtin);
}