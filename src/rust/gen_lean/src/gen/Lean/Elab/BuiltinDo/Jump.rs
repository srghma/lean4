// Lean compiler output
// Module: Lean.Elab.BuiltinDo.Jump
// Imports: Lean.Elab.Do.Basic Lean.Parser.Do
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
};
use crate::r#gen::Lean::Elab::Do::Basic::{
    initialize_Lean_Elab_Do_Basic, l_Lean_Elab_Do_DoElemCont_elabAsSyntacticallyDeadCode,
    l_Lean_Elab_Do_doElemElabAttribute, l_Lean_Elab_Do_getBreakCont___redArg,
    l_Lean_Elab_Do_getContinueCont___redArg, l_Lean_Elab_Do_getReturnCont___redArg,
    l_Lean_Elab_Do_mkPUnitUnit___redArg, runtime_initialize_Lean_Elab_Do_Basic,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTermEnsuringType, l_Lean_Elab_Term_ensureHasType,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Parser::Do::{
    initialize_Lean_Parser_Do, runtime_initialize_Lean_Parser_Do,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoReturn___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Elab_Do_elabDoReturn___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoReturn___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lean_Elab_Do_elabDoReturn___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoReturn___closed__2_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Elab_Do_elabDoReturn___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoReturn___closed__3_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [100, 111, 82, 101, 116, 117, 114, 110, 0],
    };
static mut l_Lean_Elab_Do_elabDoReturn___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_elabDoReturn___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoReturn___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoReturn___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoReturn___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__3_value)
                as *mut crate::leanh::LeanObject,
            2825454143963843026 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoReturn___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__1_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__2_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 108, 97, 98, 68, 111, 82, 101, 116, 117, 114, 110, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__1_value) as *mut crate::leanh::LeanObject,102172329646148436 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__2_value) as *mut crate::leanh::LeanObject,8339942460513942955 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoBreak___redArg___closed__0_value: crate::leanh::LeanStringObject<
    37,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        96, 98, 114, 101, 97, 107, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 110, 101, 115, 116,
        101, 100, 32, 105, 110, 115, 105, 100, 101, 32, 97, 32, 108, 111, 111, 112, 0,
    ],
};
static mut l_Lean_Elab_Do_elabDoBreak___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoBreak___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Do_elabDoBreak___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_elabDoBreak___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 111, 66, 114, 101, 97, 107, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__0_value) as *mut crate::leanh::LeanObject,2827323648879505508 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__2_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 108, 97, 98, 68, 111, 66, 114, 101, 97, 107, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__1_value) as *mut crate::leanh::LeanObject,102172329646148436 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__2_value) as *mut crate::leanh::LeanObject,9538125624861310281 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoContinue___redArg___closed__0_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        96, 99, 111, 110, 116, 105, 110, 117, 101, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32,
        110, 101, 115, 116, 101, 100, 32, 105, 110, 115, 105, 100, 101, 32, 97, 32, 108, 111, 111,
        112, 0,
    ],
};
static mut l_Lean_Elab_Do_elabDoContinue___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoContinue___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Do_elabDoContinue___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_elabDoContinue___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 111, 67, 111, 110, 116, 105, 110, 117, 101, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__0_value) as *mut crate::leanh::LeanObject,13683945405148812387 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__2_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 108, 97, 98, 68, 111, 67, 111, 110, 116, 105, 110, 117, 101, 0]};
static mut l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Do_elabDoReturn___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__1_value) as *mut crate::leanh::LeanObject,102172329646148436 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__2_value) as *mut crate::leanh::LeanObject,13746095854647233560 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_395_ = crate::leanh::lean_box(0);
    v___x_396_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_397_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_397_, 0, v___x_396_);
    crate::leanh::lean_ctor_set(v___x_397_, 1, v___x_395_);
    return v___x_397_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_399_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___closed__0);
    v___x_400_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_400_, 0, v___x_399_);
    return v___x_400_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg___boxed(
    mut v___y_401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_402_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg();
    return v_res_402_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0(
    mut v_00_u03b1_403_: *mut crate::leanh::LeanObject,
    mut v___y_404_: *mut crate::leanh::LeanObject,
    mut v___y_405_: *mut crate::leanh::LeanObject,
    mut v___y_406_: *mut crate::leanh::LeanObject,
    mut v___y_407_: *mut crate::leanh::LeanObject,
    mut v___y_408_: *mut crate::leanh::LeanObject,
    mut v___y_409_: *mut crate::leanh::LeanObject,
    mut v___y_410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_412_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg();
    return v___x_412_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___boxed(
    mut v_00_u03b1_413_: *mut crate::leanh::LeanObject,
    mut v___y_414_: *mut crate::leanh::LeanObject,
    mut v___y_415_: *mut crate::leanh::LeanObject,
    mut v___y_416_: *mut crate::leanh::LeanObject,
    mut v___y_417_: *mut crate::leanh::LeanObject,
    mut v___y_418_: *mut crate::leanh::LeanObject,
    mut v___y_419_: *mut crate::leanh::LeanObject,
    mut v___y_420_: *mut crate::leanh::LeanObject,
    mut v___y_421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_422_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0(
        v_00_u03b1_413_,
        v___y_414_,
        v___y_415_,
        v___y_416_,
        v___y_417_,
        v___y_418_,
        v___y_419_,
        v___y_420_,
    );
    crate::leanh::lean_dec(v___y_420_);
    crate::leanh::lean_dec_ref(v___y_419_);
    crate::leanh::lean_dec(v___y_418_);
    crate::leanh::lean_dec_ref(v___y_417_);
    crate::leanh::lean_dec(v___y_416_);
    crate::leanh::lean_dec_ref(v___y_415_);
    crate::leanh::lean_dec_ref(v___y_414_);
    return v_res_422_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoReturn(
    mut v_stx_432_: *mut crate::leanh::LeanObject,
    mut v_dec_433_: *mut crate::leanh::LeanObject,
    mut v_a_434_: *mut crate::leanh::LeanObject,
    mut v_a_435_: *mut crate::leanh::LeanObject,
    mut v_a_436_: *mut crate::leanh::LeanObject,
    mut v_a_437_: *mut crate::leanh::LeanObject,
    mut v_a_438_: *mut crate::leanh::LeanObject,
    mut v_a_439_: *mut crate::leanh::LeanObject,
    mut v_a_440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_458_: u8 = 0;
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_462_: u8 = 0;
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: u8 = 0;
    let mut v_e_x3f_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_480_: u8 = 0;
    let mut v_resultType_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_488_: u8 = 0;
    let mut v_a_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_493_: u8 = 0;
    let mut v_resultType_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_501_: u8 = 0;
    let mut v_a_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_505_: u8 = 0;
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_509_: u8 = 0;
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: u8 = 0;
    let mut v___x_514_: u8 = 0;
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_463_ = l_Lean_Elab_Do_elabDoReturn___closed__4;
                crate::leanh::lean_inc(v_stx_432_);
                v___x_464_ = l_Lean_Syntax_isOfKind(v_stx_432_, v___x_463_);
                if v___x_464_ == 0 {
                    crate::leanh::lean_dec_ref(v_dec_433_);
                    crate::leanh::lean_dec(v_stx_432_);
                    v___x_510_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg();
                    return v___x_510_;
                } else {
                    v___x_511_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_512_ = l_Lean_Syntax_getArg(v_stx_432_, v___x_511_);
                    crate::leanh::lean_dec(v_stx_432_);
                    v___x_513_ = l_Lean_Syntax_isNone(v___x_512_);
                    if v___x_513_ == 0 {
                        crate::leanh::lean_inc(v___x_512_);
                        v___x_514_ = l_Lean_Syntax_matchesNull(v___x_512_, v___x_511_);
                        if v___x_514_ == 0 {
                            crate::leanh::lean_dec(v___x_512_);
                            crate::leanh::lean_dec_ref(v_dec_433_);
                            v___x_515_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoReturn_spec__0___redArg();
                            return v___x_515_;
                        } else {
                            v___x_516_ = crate::leanh::lean_unsigned_to_nat(0);
                            v_e_x3f_517_ = l_Lean_Syntax_getArg(v___x_512_, v___x_516_);
                            crate::leanh::lean_dec(v___x_512_);
                            v___x_518_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_518_, 0, v_e_x3f_517_);
                            v_e_x3f_466_ = v___x_518_;
                            v___y_467_ = v_a_434_;
                            v___y_468_ = v_a_435_;
                            v___y_469_ = v_a_436_;
                            v___y_470_ = v_a_437_;
                            v___y_471_ = v_a_438_;
                            v___y_472_ = v_a_439_;
                            v___y_473_ = v_a_440_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_512_);
                        v___x_519_ = crate::leanh::lean_box(0);
                        v_e_x3f_466_ = v___x_519_;
                        v___y_467_ = v_a_434_;
                        v___y_468_ = v_a_435_;
                        v___y_469_ = v_a_436_;
                        v___y_470_ = v_a_437_;
                        v___y_471_ = v_a_438_;
                        v___y_472_ = v_a_439_;
                        v___y_473_ = v_a_440_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_452_ = l_Lean_Elab_Do_DoElemCont_elabAsSyntacticallyDeadCode(
                    v_dec_433_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_,
                    v___y_450_, v___y_451_,
                );
                if crate::leanh::lean_obj_tag(v___x_452_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_452_, 1);
                    v_k_453_ = crate::leanh::lean_ctor_get(v___y_443_, 1);
                    crate::leanh::lean_inc_ref(v_k_453_);
                    crate::leanh::lean_dec_ref(v___y_443_);
                    crate::leanh::lean_inc(v___y_451_);
                    crate::leanh::lean_inc_ref(v___y_450_);
                    crate::leanh::lean_inc(v___y_449_);
                    crate::leanh::lean_inc_ref(v___y_448_);
                    crate::leanh::lean_inc(v___y_447_);
                    crate::leanh::lean_inc_ref(v___y_446_);
                    crate::leanh::lean_inc_ref(v___y_445_);
                    v___x_454_ = crate::leanh::lean_apply_9(
                        v_k_453_,
                        v_e_444_,
                        v___y_445_,
                        v___y_446_,
                        v___y_447_,
                        v___y_448_,
                        v___y_449_,
                        v___y_450_,
                        v___y_451_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_454_;
                } else {
                    crate::leanh::lean_dec_ref(v_e_444_);
                    crate::leanh::lean_dec_ref(v___y_443_);
                    v_a_455_ = crate::leanh::lean_ctor_get(v___x_452_, 0);
                    v_isSharedCheck_462_ = (!crate::leanh::lean_is_exclusive(v___x_452_)) as u8;
                    if v_isSharedCheck_462_ == 0 {
                        v___x_457_ = v___x_452_;
                        v_isShared_458_ = v_isSharedCheck_462_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_455_);
                        crate::leanh::lean_dec(v___x_452_);
                        v___x_457_ = crate::leanh::lean_box(0);
                        v_isShared_458_ = v_isSharedCheck_462_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_458_ == 0 {
                    v___x_460_ = v___x_457_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_461_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
                    v___x_460_ = v_reuseFailAlloc_461_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_460_;
            }
            4 => {
                v___x_474_ = l_Lean_Elab_Do_getReturnCont___redArg(v___y_467_);
                if crate::leanh::lean_obj_tag(v___x_474_) == 0 {
                    if crate::leanh::lean_obj_tag(v_e_x3f_466_) == 0 {
                        v_a_475_ = crate::leanh::lean_ctor_get(v___x_474_, 0);
                        crate::leanh::lean_inc(v_a_475_);
                        crate::leanh::lean_dec_ref_known(v___x_474_, 1);
                        v___x_476_ = l_Lean_Elab_Do_mkPUnitUnit___redArg(v___y_467_);
                        if crate::leanh::lean_obj_tag(v___x_476_) == 0 {
                            v_a_477_ = crate::leanh::lean_ctor_get(v___x_476_, 0);
                            v_isSharedCheck_488_ =
                                (!crate::leanh::lean_is_exclusive(v___x_476_)) as u8;
                            if v_isSharedCheck_488_ == 0 {
                                v___x_479_ = v___x_476_;
                                v_isShared_480_ = v_isSharedCheck_488_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_477_);
                                crate::leanh::lean_dec(v___x_476_);
                                v___x_479_ = crate::leanh::lean_box(0);
                                v_isShared_480_ = v_isSharedCheck_488_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_475_);
                            crate::leanh::lean_dec_ref(v_dec_433_);
                            return v___x_476_;
                        }
                    } else {
                        v_a_489_ = crate::leanh::lean_ctor_get(v___x_474_, 0);
                        crate::leanh::lean_inc(v_a_489_);
                        crate::leanh::lean_dec_ref_known(v___x_474_, 1);
                        v_val_490_ = crate::leanh::lean_ctor_get(v_e_x3f_466_, 0);
                        v_isSharedCheck_501_ =
                            (!crate::leanh::lean_is_exclusive(v_e_x3f_466_)) as u8;
                        if v_isSharedCheck_501_ == 0 {
                            v___x_492_ = v_e_x3f_466_;
                            v_isShared_493_ = v_isSharedCheck_501_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_490_);
                            crate::leanh::lean_dec(v_e_x3f_466_);
                            v___x_492_ = crate::leanh::lean_box(0);
                            v_isShared_493_ = v_isSharedCheck_501_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_e_x3f_466_);
                    crate::leanh::lean_dec_ref(v_dec_433_);
                    v_a_502_ = crate::leanh::lean_ctor_get(v___x_474_, 0);
                    v_isSharedCheck_509_ = (!crate::leanh::lean_is_exclusive(v___x_474_)) as u8;
                    if v_isSharedCheck_509_ == 0 {
                        v___x_504_ = v___x_474_;
                        v_isShared_505_ = v_isSharedCheck_509_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_502_);
                        crate::leanh::lean_dec(v___x_474_);
                        v___x_504_ = crate::leanh::lean_box(0);
                        v_isShared_505_ = v_isSharedCheck_509_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v_resultType_481_ = crate::leanh::lean_ctor_get(v_a_475_, 0);
                crate::leanh::lean_inc_ref(v_resultType_481_);
                if v_isShared_480_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_479_, 1);
                    crate::leanh::lean_ctor_set(v___x_479_, 0, v_resultType_481_);
                    v___x_483_ = v___x_479_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_487_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_487_, 0, v_resultType_481_);
                    v___x_483_ = v_reuseFailAlloc_487_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_484_ = crate::leanh::lean_box(0);
                v___x_485_ = l_Lean_Elab_Term_ensureHasType(
                    v___x_483_, v_a_477_, v___x_484_, v___x_484_, v___y_468_, v___y_469_,
                    v___y_470_, v___y_471_, v___y_472_, v___y_473_,
                );
                if crate::leanh::lean_obj_tag(v___x_485_) == 0 {
                    v_a_486_ = crate::leanh::lean_ctor_get(v___x_485_, 0);
                    crate::leanh::lean_inc(v_a_486_);
                    crate::leanh::lean_dec_ref_known(v___x_485_, 1);
                    v___y_443_ = v_a_475_;
                    v_e_444_ = v_a_486_;
                    v___y_445_ = v___y_467_;
                    v___y_446_ = v___y_468_;
                    v___y_447_ = v___y_469_;
                    v___y_448_ = v___y_470_;
                    v___y_449_ = v___y_471_;
                    v___y_450_ = v___y_472_;
                    v___y_451_ = v___y_473_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_475_);
                    crate::leanh::lean_dec_ref(v_dec_433_);
                    return v___x_485_;
                }
            }
            7 => {
                v_resultType_494_ = crate::leanh::lean_ctor_get(v_a_489_, 0);
                crate::leanh::lean_inc_ref(v_resultType_494_);
                if v_isShared_493_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_492_, 0, v_resultType_494_);
                    v___x_496_ = v___x_492_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_500_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_500_, 0, v_resultType_494_);
                    v___x_496_ = v_reuseFailAlloc_500_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_497_ = crate::leanh::lean_box(0);
                v___x_498_ = l_Lean_Elab_Term_elabTermEnsuringType(
                    v_val_490_, v___x_496_, v___x_464_, v___x_464_, v___x_497_, v___y_468_,
                    v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_,
                );
                if crate::leanh::lean_obj_tag(v___x_498_) == 0 {
                    v_a_499_ = crate::leanh::lean_ctor_get(v___x_498_, 0);
                    crate::leanh::lean_inc(v_a_499_);
                    crate::leanh::lean_dec_ref_known(v___x_498_, 1);
                    v___y_443_ = v_a_489_;
                    v_e_444_ = v_a_499_;
                    v___y_445_ = v___y_467_;
                    v___y_446_ = v___y_468_;
                    v___y_447_ = v___y_469_;
                    v___y_448_ = v___y_470_;
                    v___y_449_ = v___y_471_;
                    v___y_450_ = v___y_472_;
                    v___y_451_ = v___y_473_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_489_);
                    crate::leanh::lean_dec_ref(v_dec_433_);
                    return v___x_498_;
                }
            }
            9 => {
                if v_isShared_505_ == 0 {
                    v___x_507_ = v___x_504_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_508_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
                    v___x_507_ = v_reuseFailAlloc_508_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_507_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoReturn___boxed(
    mut v_stx_520_: *mut crate::leanh::LeanObject,
    mut v_dec_521_: *mut crate::leanh::LeanObject,
    mut v_a_522_: *mut crate::leanh::LeanObject,
    mut v_a_523_: *mut crate::leanh::LeanObject,
    mut v_a_524_: *mut crate::leanh::LeanObject,
    mut v_a_525_: *mut crate::leanh::LeanObject,
    mut v_a_526_: *mut crate::leanh::LeanObject,
    mut v_a_527_: *mut crate::leanh::LeanObject,
    mut v_a_528_: *mut crate::leanh::LeanObject,
    mut v_a_529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_530_ = l_Lean_Elab_Do_elabDoReturn(
        v_stx_520_, v_dec_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_,
        v_a_528_,
    );
    crate::leanh::lean_dec(v_a_528_);
    crate::leanh::lean_dec_ref(v_a_527_);
    crate::leanh::lean_dec(v_a_526_);
    crate::leanh::lean_dec_ref(v_a_525_);
    crate::leanh::lean_dec(v_a_524_);
    crate::leanh::lean_dec_ref(v_a_523_);
    crate::leanh::lean_dec_ref(v_a_522_);
    return v_res_530_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_540_ = l_Lean_Elab_Do_doElemElabAttribute;
    v___x_541_ = l_Lean_Elab_Do_elabDoReturn___closed__4;
    v___x_542_ = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___closed__3;
    v___x_543_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Do_elabDoReturn___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_544_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_540_, v___x_541_, v___x_542_, v___x_543_,
    );
    return v___x_544_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1___boxed(
    mut v_a_545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_546_ = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1();
    return v_res_546_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_spec__0(
    mut v_msgData_547_: *mut crate::leanh::LeanObject,
    mut v___y_548_: *mut crate::leanh::LeanObject,
    mut v___y_549_: *mut crate::leanh::LeanObject,
    mut v___y_550_: *mut crate::leanh::LeanObject,
    mut v___y_551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_553_ = lean_st_ref_get(v___y_551_);
    v_env_554_ = crate::leanh::lean_ctor_get(v___x_553_, 0);
    crate::leanh::lean_inc_ref(v_env_554_);
    crate::leanh::lean_dec(v___x_553_);
    v___x_555_ = lean_st_ref_get(v___y_549_);
    v_mctx_556_ = crate::leanh::lean_ctor_get(v___x_555_, 0);
    crate::leanh::lean_inc_ref(v_mctx_556_);
    crate::leanh::lean_dec(v___x_555_);
    v_lctx_557_ = crate::leanh::lean_ctor_get(v___y_548_, 2);
    v_options_558_ = crate::leanh::lean_ctor_get(v___y_550_, 2);
    crate::leanh::lean_inc_ref(v_options_558_);
    crate::leanh::lean_inc_ref(v_lctx_557_);
    v___x_559_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_559_, 0, v_env_554_);
    crate::leanh::lean_ctor_set(v___x_559_, 1, v_mctx_556_);
    crate::leanh::lean_ctor_set(v___x_559_, 2, v_lctx_557_);
    crate::leanh::lean_ctor_set(v___x_559_, 3, v_options_558_);
    v___x_560_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_560_, 0, v___x_559_);
    crate::leanh::lean_ctor_set(v___x_560_, 1, v_msgData_547_);
    v___x_561_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_561_, 0, v___x_560_);
    return v___x_561_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_spec__0___boxed(
    mut v_msgData_562_: *mut crate::leanh::LeanObject,
    mut v___y_563_: *mut crate::leanh::LeanObject,
    mut v___y_564_: *mut crate::leanh::LeanObject,
    mut v___y_565_: *mut crate::leanh::LeanObject,
    mut v___y_566_: *mut crate::leanh::LeanObject,
    mut v___y_567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_568_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_spec__0(v_msgData_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
    crate::leanh::lean_dec(v___y_566_);
    crate::leanh::lean_dec_ref(v___y_565_);
    crate::leanh::lean_dec(v___y_564_);
    crate::leanh::lean_dec_ref(v___y_563_);
    return v_res_568_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg(
    mut v_msg_569_: *mut crate::leanh::LeanObject,
    mut v___y_570_: *mut crate::leanh::LeanObject,
    mut v___y_571_: *mut crate::leanh::LeanObject,
    mut v___y_572_: *mut crate::leanh::LeanObject,
    mut v___y_573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_580_: u8 = 0;
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_585_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_575_ = crate::leanh::lean_ctor_get(v___y_572_, 5);
                v___x_576_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0_spec__0(v_msg_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
                v_a_577_ = crate::leanh::lean_ctor_get(v___x_576_, 0);
                v_isSharedCheck_585_ = (!crate::leanh::lean_is_exclusive(v___x_576_)) as u8;
                if v_isSharedCheck_585_ == 0 {
                    v___x_579_ = v___x_576_;
                    v_isShared_580_ = v_isSharedCheck_585_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_577_);
                    crate::leanh::lean_dec(v___x_576_);
                    v___x_579_ = crate::leanh::lean_box(0);
                    v_isShared_580_ = v_isSharedCheck_585_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_575_);
                v___x_581_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_581_, 0, v_ref_575_);
                crate::leanh::lean_ctor_set(v___x_581_, 1, v_a_577_);
                if v_isShared_580_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_579_, 1);
                    crate::leanh::lean_ctor_set(v___x_579_, 0, v___x_581_);
                    v___x_583_ = v___x_579_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_584_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
                    v___x_583_ = v_reuseFailAlloc_584_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_583_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg___boxed(
    mut v_msg_586_: *mut crate::leanh::LeanObject,
    mut v___y_587_: *mut crate::leanh::LeanObject,
    mut v___y_588_: *mut crate::leanh::LeanObject,
    mut v___y_589_: *mut crate::leanh::LeanObject,
    mut v___y_590_: *mut crate::leanh::LeanObject,
    mut v___y_591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_592_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg(
        v_msg_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_,
    );
    crate::leanh::lean_dec(v___y_590_);
    crate::leanh::lean_dec_ref(v___y_589_);
    crate::leanh::lean_dec(v___y_588_);
    crate::leanh::lean_dec_ref(v___y_587_);
    return v_res_592_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoBreak___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_594_ = l_Lean_Elab_Do_elabDoBreak___redArg___closed__0;
    v___x_595_ = l_Lean_stringToMessageData(v___x_594_);
    return v___x_595_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoBreak___redArg(
    mut v_dec_596_: *mut crate::leanh::LeanObject,
    mut v_a_597_: *mut crate::leanh::LeanObject,
    mut v_a_598_: *mut crate::leanh::LeanObject,
    mut v_a_599_: *mut crate::leanh::LeanObject,
    mut v_a_600_: *mut crate::leanh::LeanObject,
    mut v_a_601_: *mut crate::leanh::LeanObject,
    mut v_a_602_: *mut crate::leanh::LeanObject,
    mut v_a_603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_613_: u8 = 0;
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_617_: u8 = 0;
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_623_: u8 = 0;
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_627_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_605_ = l_Lean_Elab_Do_getBreakCont___redArg(v_a_597_);
                if crate::leanh::lean_obj_tag(v___x_605_) == 0 {
                    v_a_606_ = crate::leanh::lean_ctor_get(v___x_605_, 0);
                    crate::leanh::lean_inc(v_a_606_);
                    crate::leanh::lean_dec_ref_known(v___x_605_, 1);
                    if crate::leanh::lean_obj_tag(v_a_606_) == 1 {
                        v_val_607_ = crate::leanh::lean_ctor_get(v_a_606_, 0);
                        crate::leanh::lean_inc(v_val_607_);
                        crate::leanh::lean_dec_ref_known(v_a_606_, 1);
                        v___x_608_ = l_Lean_Elab_Do_DoElemCont_elabAsSyntacticallyDeadCode(
                            v_dec_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_,
                            v_a_603_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_608_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_608_, 1);
                            crate::leanh::lean_inc(v_a_603_);
                            crate::leanh::lean_inc_ref(v_a_602_);
                            crate::leanh::lean_inc(v_a_601_);
                            crate::leanh::lean_inc_ref(v_a_600_);
                            crate::leanh::lean_inc(v_a_599_);
                            crate::leanh::lean_inc_ref(v_a_598_);
                            crate::leanh::lean_inc_ref(v_a_597_);
                            v___x_609_ = crate::leanh::lean_apply_8(
                                v_val_607_,
                                v_a_597_,
                                v_a_598_,
                                v_a_599_,
                                v_a_600_,
                                v_a_601_,
                                v_a_602_,
                                v_a_603_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_609_;
                        } else {
                            crate::leanh::lean_dec(v_val_607_);
                            v_a_610_ = crate::leanh::lean_ctor_get(v___x_608_, 0);
                            v_isSharedCheck_617_ =
                                (!crate::leanh::lean_is_exclusive(v___x_608_)) as u8;
                            if v_isSharedCheck_617_ == 0 {
                                v___x_612_ = v___x_608_;
                                v_isShared_613_ = v_isSharedCheck_617_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_610_);
                                crate::leanh::lean_dec(v___x_608_);
                                v___x_612_ = crate::leanh::lean_box(0);
                                v_isShared_613_ = v_isSharedCheck_617_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_606_);
                        crate::leanh::lean_dec_ref(v_dec_596_);
                        v___x_618_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Do_elabDoBreak___redArg___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Do_elabDoBreak___redArg___closed__1_once
                            ),
                            _init_l_Lean_Elab_Do_elabDoBreak___redArg___closed__1,
                        );
                        v___x_619_ =
                            l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg(
                                v___x_618_, v_a_600_, v_a_601_, v_a_602_, v_a_603_,
                            );
                        return v___x_619_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_dec_596_);
                    v_a_620_ = crate::leanh::lean_ctor_get(v___x_605_, 0);
                    v_isSharedCheck_627_ = (!crate::leanh::lean_is_exclusive(v___x_605_)) as u8;
                    if v_isSharedCheck_627_ == 0 {
                        v___x_622_ = v___x_605_;
                        v_isShared_623_ = v_isSharedCheck_627_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_620_);
                        crate::leanh::lean_dec(v___x_605_);
                        v___x_622_ = crate::leanh::lean_box(0);
                        v_isShared_623_ = v_isSharedCheck_627_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_613_ == 0 {
                    v___x_615_ = v___x_612_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_616_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
                    v___x_615_ = v_reuseFailAlloc_616_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_615_;
            }
            3 => {
                if v_isShared_623_ == 0 {
                    v___x_625_ = v___x_622_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_626_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
                    v___x_625_ = v_reuseFailAlloc_626_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_625_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoBreak___redArg___boxed(
    mut v_dec_628_: *mut crate::leanh::LeanObject,
    mut v_a_629_: *mut crate::leanh::LeanObject,
    mut v_a_630_: *mut crate::leanh::LeanObject,
    mut v_a_631_: *mut crate::leanh::LeanObject,
    mut v_a_632_: *mut crate::leanh::LeanObject,
    mut v_a_633_: *mut crate::leanh::LeanObject,
    mut v_a_634_: *mut crate::leanh::LeanObject,
    mut v_a_635_: *mut crate::leanh::LeanObject,
    mut v_a_636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_637_ = l_Lean_Elab_Do_elabDoBreak___redArg(
        v_dec_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_,
    );
    crate::leanh::lean_dec(v_a_635_);
    crate::leanh::lean_dec_ref(v_a_634_);
    crate::leanh::lean_dec(v_a_633_);
    crate::leanh::lean_dec_ref(v_a_632_);
    crate::leanh::lean_dec(v_a_631_);
    crate::leanh::lean_dec_ref(v_a_630_);
    crate::leanh::lean_dec_ref(v_a_629_);
    return v_res_637_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoBreak(
    mut v___stx_638_: *mut crate::leanh::LeanObject,
    mut v_dec_639_: *mut crate::leanh::LeanObject,
    mut v_a_640_: *mut crate::leanh::LeanObject,
    mut v_a_641_: *mut crate::leanh::LeanObject,
    mut v_a_642_: *mut crate::leanh::LeanObject,
    mut v_a_643_: *mut crate::leanh::LeanObject,
    mut v_a_644_: *mut crate::leanh::LeanObject,
    mut v_a_645_: *mut crate::leanh::LeanObject,
    mut v_a_646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_648_ = l_Lean_Elab_Do_elabDoBreak___redArg(
        v_dec_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_,
    );
    return v___x_648_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoBreak___boxed(
    mut v___stx_649_: *mut crate::leanh::LeanObject,
    mut v_dec_650_: *mut crate::leanh::LeanObject,
    mut v_a_651_: *mut crate::leanh::LeanObject,
    mut v_a_652_: *mut crate::leanh::LeanObject,
    mut v_a_653_: *mut crate::leanh::LeanObject,
    mut v_a_654_: *mut crate::leanh::LeanObject,
    mut v_a_655_: *mut crate::leanh::LeanObject,
    mut v_a_656_: *mut crate::leanh::LeanObject,
    mut v_a_657_: *mut crate::leanh::LeanObject,
    mut v_a_658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_659_ = l_Lean_Elab_Do_elabDoBreak(
        v___stx_649_,
        v_dec_650_,
        v_a_651_,
        v_a_652_,
        v_a_653_,
        v_a_654_,
        v_a_655_,
        v_a_656_,
        v_a_657_,
    );
    crate::leanh::lean_dec(v_a_657_);
    crate::leanh::lean_dec_ref(v_a_656_);
    crate::leanh::lean_dec(v_a_655_);
    crate::leanh::lean_dec_ref(v_a_654_);
    crate::leanh::lean_dec(v_a_653_);
    crate::leanh::lean_dec_ref(v_a_652_);
    crate::leanh::lean_dec_ref(v_a_651_);
    crate::leanh::lean_dec(v___stx_649_);
    return v_res_659_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0(
    mut v_00_u03b1_660_: *mut crate::leanh::LeanObject,
    mut v_msg_661_: *mut crate::leanh::LeanObject,
    mut v___y_662_: *mut crate::leanh::LeanObject,
    mut v___y_663_: *mut crate::leanh::LeanObject,
    mut v___y_664_: *mut crate::leanh::LeanObject,
    mut v___y_665_: *mut crate::leanh::LeanObject,
    mut v___y_666_: *mut crate::leanh::LeanObject,
    mut v___y_667_: *mut crate::leanh::LeanObject,
    mut v___y_668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_670_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg(
        v_msg_661_, v___y_665_, v___y_666_, v___y_667_, v___y_668_,
    );
    return v___x_670_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___boxed(
    mut v_00_u03b1_671_: *mut crate::leanh::LeanObject,
    mut v_msg_672_: *mut crate::leanh::LeanObject,
    mut v___y_673_: *mut crate::leanh::LeanObject,
    mut v___y_674_: *mut crate::leanh::LeanObject,
    mut v___y_675_: *mut crate::leanh::LeanObject,
    mut v___y_676_: *mut crate::leanh::LeanObject,
    mut v___y_677_: *mut crate::leanh::LeanObject,
    mut v___y_678_: *mut crate::leanh::LeanObject,
    mut v___y_679_: *mut crate::leanh::LeanObject,
    mut v___y_680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_681_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0(
        v_00_u03b1_671_,
        v_msg_672_,
        v___y_673_,
        v___y_674_,
        v___y_675_,
        v___y_676_,
        v___y_677_,
        v___y_678_,
        v___y_679_,
    );
    crate::leanh::lean_dec(v___y_679_);
    crate::leanh::lean_dec_ref(v___y_678_);
    crate::leanh::lean_dec(v___y_677_);
    crate::leanh::lean_dec_ref(v___y_676_);
    crate::leanh::lean_dec(v___y_675_);
    crate::leanh::lean_dec_ref(v___y_674_);
    crate::leanh::lean_dec_ref(v___y_673_);
    return v_res_681_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_695_ = l_Lean_Elab_Do_doElemElabAttribute;
    v___x_696_ = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__1;
    v___x_697_ = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___closed__3;
    v___x_698_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Do_elabDoBreak___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_699_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_695_, v___x_696_, v___x_697_, v___x_698_,
    );
    return v___x_699_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1___boxed(
    mut v_a_700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_701_ = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1();
    return v_res_701_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoContinue___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_703_ = l_Lean_Elab_Do_elabDoContinue___redArg___closed__0;
    v___x_704_ = l_Lean_stringToMessageData(v___x_703_);
    return v___x_704_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoContinue___redArg(
    mut v_dec_705_: *mut crate::leanh::LeanObject,
    mut v_a_706_: *mut crate::leanh::LeanObject,
    mut v_a_707_: *mut crate::leanh::LeanObject,
    mut v_a_708_: *mut crate::leanh::LeanObject,
    mut v_a_709_: *mut crate::leanh::LeanObject,
    mut v_a_710_: *mut crate::leanh::LeanObject,
    mut v_a_711_: *mut crate::leanh::LeanObject,
    mut v_a_712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_722_: u8 = 0;
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_726_: u8 = 0;
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_732_: u8 = 0;
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_714_ = l_Lean_Elab_Do_getContinueCont___redArg(v_a_706_);
                if crate::leanh::lean_obj_tag(v___x_714_) == 0 {
                    v_a_715_ = crate::leanh::lean_ctor_get(v___x_714_, 0);
                    crate::leanh::lean_inc(v_a_715_);
                    crate::leanh::lean_dec_ref_known(v___x_714_, 1);
                    if crate::leanh::lean_obj_tag(v_a_715_) == 1 {
                        v_val_716_ = crate::leanh::lean_ctor_get(v_a_715_, 0);
                        crate::leanh::lean_inc(v_val_716_);
                        crate::leanh::lean_dec_ref_known(v_a_715_, 1);
                        v___x_717_ = l_Lean_Elab_Do_DoElemCont_elabAsSyntacticallyDeadCode(
                            v_dec_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_,
                            v_a_712_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_717_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_717_, 1);
                            crate::leanh::lean_inc(v_a_712_);
                            crate::leanh::lean_inc_ref(v_a_711_);
                            crate::leanh::lean_inc(v_a_710_);
                            crate::leanh::lean_inc_ref(v_a_709_);
                            crate::leanh::lean_inc(v_a_708_);
                            crate::leanh::lean_inc_ref(v_a_707_);
                            crate::leanh::lean_inc_ref(v_a_706_);
                            v___x_718_ = crate::leanh::lean_apply_8(
                                v_val_716_,
                                v_a_706_,
                                v_a_707_,
                                v_a_708_,
                                v_a_709_,
                                v_a_710_,
                                v_a_711_,
                                v_a_712_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_718_;
                        } else {
                            crate::leanh::lean_dec(v_val_716_);
                            v_a_719_ = crate::leanh::lean_ctor_get(v___x_717_, 0);
                            v_isSharedCheck_726_ =
                                (!crate::leanh::lean_is_exclusive(v___x_717_)) as u8;
                            if v_isSharedCheck_726_ == 0 {
                                v___x_721_ = v___x_717_;
                                v_isShared_722_ = v_isSharedCheck_726_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_719_);
                                crate::leanh::lean_dec(v___x_717_);
                                v___x_721_ = crate::leanh::lean_box(0);
                                v_isShared_722_ = v_isSharedCheck_726_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_715_);
                        crate::leanh::lean_dec_ref(v_dec_705_);
                        v___x_727_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Do_elabDoContinue___redArg___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Do_elabDoContinue___redArg___closed__1_once
                            ),
                            _init_l_Lean_Elab_Do_elabDoContinue___redArg___closed__1,
                        );
                        v___x_728_ =
                            l_Lean_throwError___at___00Lean_Elab_Do_elabDoBreak_spec__0___redArg(
                                v___x_727_, v_a_709_, v_a_710_, v_a_711_, v_a_712_,
                            );
                        return v___x_728_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_dec_705_);
                    v_a_729_ = crate::leanh::lean_ctor_get(v___x_714_, 0);
                    v_isSharedCheck_736_ = (!crate::leanh::lean_is_exclusive(v___x_714_)) as u8;
                    if v_isSharedCheck_736_ == 0 {
                        v___x_731_ = v___x_714_;
                        v_isShared_732_ = v_isSharedCheck_736_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_729_);
                        crate::leanh::lean_dec(v___x_714_);
                        v___x_731_ = crate::leanh::lean_box(0);
                        v_isShared_732_ = v_isSharedCheck_736_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_722_ == 0 {
                    v___x_724_ = v___x_721_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_725_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
                    v___x_724_ = v_reuseFailAlloc_725_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_724_;
            }
            3 => {
                if v_isShared_732_ == 0 {
                    v___x_734_ = v___x_731_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_735_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
                    v___x_734_ = v_reuseFailAlloc_735_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_734_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoContinue___redArg___boxed(
    mut v_dec_737_: *mut crate::leanh::LeanObject,
    mut v_a_738_: *mut crate::leanh::LeanObject,
    mut v_a_739_: *mut crate::leanh::LeanObject,
    mut v_a_740_: *mut crate::leanh::LeanObject,
    mut v_a_741_: *mut crate::leanh::LeanObject,
    mut v_a_742_: *mut crate::leanh::LeanObject,
    mut v_a_743_: *mut crate::leanh::LeanObject,
    mut v_a_744_: *mut crate::leanh::LeanObject,
    mut v_a_745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_746_ = l_Lean_Elab_Do_elabDoContinue___redArg(
        v_dec_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_,
    );
    crate::leanh::lean_dec(v_a_744_);
    crate::leanh::lean_dec_ref(v_a_743_);
    crate::leanh::lean_dec(v_a_742_);
    crate::leanh::lean_dec_ref(v_a_741_);
    crate::leanh::lean_dec(v_a_740_);
    crate::leanh::lean_dec_ref(v_a_739_);
    crate::leanh::lean_dec_ref(v_a_738_);
    return v_res_746_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoContinue(
    mut v___stx_747_: *mut crate::leanh::LeanObject,
    mut v_dec_748_: *mut crate::leanh::LeanObject,
    mut v_a_749_: *mut crate::leanh::LeanObject,
    mut v_a_750_: *mut crate::leanh::LeanObject,
    mut v_a_751_: *mut crate::leanh::LeanObject,
    mut v_a_752_: *mut crate::leanh::LeanObject,
    mut v_a_753_: *mut crate::leanh::LeanObject,
    mut v_a_754_: *mut crate::leanh::LeanObject,
    mut v_a_755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_757_ = l_Lean_Elab_Do_elabDoContinue___redArg(
        v_dec_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_,
    );
    return v___x_757_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoContinue___boxed(
    mut v___stx_758_: *mut crate::leanh::LeanObject,
    mut v_dec_759_: *mut crate::leanh::LeanObject,
    mut v_a_760_: *mut crate::leanh::LeanObject,
    mut v_a_761_: *mut crate::leanh::LeanObject,
    mut v_a_762_: *mut crate::leanh::LeanObject,
    mut v_a_763_: *mut crate::leanh::LeanObject,
    mut v_a_764_: *mut crate::leanh::LeanObject,
    mut v_a_765_: *mut crate::leanh::LeanObject,
    mut v_a_766_: *mut crate::leanh::LeanObject,
    mut v_a_767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_768_ = l_Lean_Elab_Do_elabDoContinue(
        v___stx_758_,
        v_dec_759_,
        v_a_760_,
        v_a_761_,
        v_a_762_,
        v_a_763_,
        v_a_764_,
        v_a_765_,
        v_a_766_,
    );
    crate::leanh::lean_dec(v_a_766_);
    crate::leanh::lean_dec_ref(v_a_765_);
    crate::leanh::lean_dec(v_a_764_);
    crate::leanh::lean_dec_ref(v_a_763_);
    crate::leanh::lean_dec(v_a_762_);
    crate::leanh::lean_dec_ref(v_a_761_);
    crate::leanh::lean_dec_ref(v_a_760_);
    crate::leanh::lean_dec(v___stx_758_);
    return v_res_768_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_782_ = l_Lean_Elab_Do_doElemElabAttribute;
    v___x_783_ = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__1;
    v___x_784_ = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___closed__3;
    v___x_785_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Do_elabDoContinue___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_786_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_782_, v___x_783_, v___x_784_, v___x_785_,
    );
    return v___x_786_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1___boxed(
    mut v_a_787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_788_ = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1();
    return v_res_788_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_BuiltinDo_Jump(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoReturn___regBuiltin_Lean_Elab_Do_elabDoReturn__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoBreak___regBuiltin_Lean_Elab_Do_elabDoBreak__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_Jump_0__Lean_Elab_Do_elabDoContinue___regBuiltin_Lean_Elab_Do_elabDoContinue__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_BuiltinDo_Jump(
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
pub unsafe fn initialize_Lean_Elab_BuiltinDo_Jump(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Do_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_Jump(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_BuiltinDo_Jump(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_BuiltinDo_Jump(builtin);
}
