// Lean compiler output
// Module: Lean.Util.TestExtern
// Imports: Lean.Meta.Tactic.Unfold Lean.Meta.Eval Lean.Compiler.ImplementedByAttr Lean.Elab.Command Init.Notation Lean.Exception Lean.Compiler.ExternAttr
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind};
use crate::r#gen::Lean::Compiler::ExternAttr::{
    initialize_Lean_Compiler_ExternAttr, l_Lean_isExtern,
    runtime_initialize_Lean_Compiler_ExternAttr,
};
use crate::r#gen::Lean::Compiler::ImplementedByAttr::{
    initialize_Lean_Compiler_ImplementedByAttr, l_Lean_Compiler_getImplementedBy_x3f,
    runtime_initialize_Lean_Compiler_ImplementedByAttr,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_liftTermElabM___redArg,
    runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::SyntheticMVars::l_Lean_Elab_Term_elabTermAndSynthesize;
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Exception::{initialize_Lean_Exception, runtime_initialize_Lean_Exception};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_Expr_getAppFn,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_MessageData_ofSyntax, l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{l_Lean_Meta_mkDecide, l_Lean_Meta_mkEq};
use crate::r#gen::Lean::Meta::Eval::{
    initialize_Lean_Meta_Eval, l_Lean_Meta_evalExpr___redArg, runtime_initialize_Lean_Meta_Eval,
};
use crate::r#gen::Lean::Meta::Tactic::Unfold::{
    initialize_Lean_Meta_Tactic_Unfold, l_Lean_Meta_unfold,
    runtime_initialize_Lean_Meta_Tactic_Unfold,
};
use crate::ffi::lean_st_ref_get;
pub static l_testExternCmd___closed__0_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
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
            116, 101, 115, 116, 69, 120, 116, 101, 114, 110, 67, 109, 100, 0,
        ],
    };
static mut l_testExternCmd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_testExternCmd___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_testExternCmd___closed__0_value) as *mut crate::leanh::LeanObject,
            15638152521579042923 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_testExternCmd___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_testExternCmd___closed__2_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_testExternCmd___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_testExternCmd___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_testExternCmd___closed__2_value) as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_testExternCmd___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_testExternCmd___closed__4_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [116, 101, 115, 116, 95, 101, 120, 116, 101, 114, 110, 32, 0],
    };
static mut l_testExternCmd___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_testExternCmd___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_testExternCmd___closed__4_value) as *mut crate::leanh::LeanObject
        ],
    };
static mut l_testExternCmd___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_testExternCmd___closed__6_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_testExternCmd___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_testExternCmd___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_testExternCmd___closed__6_value) as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_testExternCmd___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_testExternCmd___closed__8_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_testExternCmd___closed__7_value) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_testExternCmd___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_testExternCmd___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_testExternCmd___closed__3_value) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_testExternCmd___closed__5_value) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_testExternCmd___closed__8_value) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_testExternCmd___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_testExternCmd___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_testExternCmd___closed__1_value) as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_testExternCmd___closed__9_value) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_testExternCmd___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__10_value) as *mut crate::leanh::LeanObject;
pub static mut l_testExternCmd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_elabTestExtern___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_elabTestExtern___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_elabTestExtern___lam__0___closed__1_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [114, 101, 100, 117, 99, 101, 66, 111, 111, 108, 0],
    };
static mut l_elabTestExtern___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_elabTestExtern___lam__0___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_elabTestExtern___lam__0___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__1_value)
                as *mut crate::leanh::LeanObject,
            2227249244235744626 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_elabTestExtern___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_elabTestExtern___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_elabTestExtern___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_elabTestExtern___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [66, 111, 111, 108, 0],
    };
static mut l_elabTestExtern___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_elabTestExtern___lam__0___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__4_value)
                as *mut crate::leanh::LeanObject,
            12882480457794858234 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_elabTestExtern___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_elabTestExtern___lam__0___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_elabTestExtern___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_elabTestExtern___lam__0___closed__7_value: crate::leanh::LeanStringObject<68> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 68,
        m_capacity: 68,
        m_length: 67,
        m_data: [
            110, 97, 116, 105, 118, 101, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 97, 116,
            105, 111, 110, 32, 100, 105, 100, 32, 110, 111, 116, 32, 97, 103, 114, 101, 101, 32,
            119, 105, 116, 104, 32, 114, 101, 102, 101, 114, 101, 110, 99, 101, 32, 105, 109, 112,
            108, 101, 109, 101, 110, 116, 97, 116, 105, 111, 110, 33, 10, 0,
        ],
    };
static mut l_elabTestExtern___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_elabTestExtern___lam__0___closed__8_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_elabTestExtern___lam__0___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_elabTestExtern___lam__0___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_elabTestExtern___lam__0___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_elabTestExtern___lam__0___closed__10_value: crate::leanh::LeanStringObject<31> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            67, 111, 109, 112, 97, 114, 101, 32, 116, 104, 101, 32, 111, 117, 116, 112, 117, 116,
            115, 32, 111, 102, 58, 10, 35, 101, 118, 97, 108, 32, 0,
        ],
    };
static mut l_elabTestExtern___lam__0___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_elabTestExtern___lam__0___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_elabTestExtern___lam__0___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_elabTestExtern___lam__0___closed__12_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [10, 32, 97, 110, 100, 10, 35, 101, 118, 97, 108, 32, 0],
    };
static mut l_elabTestExtern___lam__0___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_elabTestExtern___lam__0___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_elabTestExtern___lam__0___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_elabTestExtern___lam__0___closed__14_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
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
            116, 101, 115, 116, 95, 101, 120, 116, 101, 114, 110, 58, 32, 0,
        ],
    };
static mut l_elabTestExtern___lam__0___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_elabTestExtern___lam__0___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_elabTestExtern___lam__0___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_elabTestExtern___lam__0___closed__16_value: crate::leanh::LeanStringObject<69> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 69,
        m_capacity: 69,
        m_length: 68,
        m_data: [
            32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 97, 110, 32, 64,
            91, 101, 120, 116, 101, 114, 110, 93, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101,
            32, 111, 114, 32, 64, 91, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 95,
            98, 121, 93, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0,
        ],
    };
static mut l_elabTestExtern___lam__0___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_elabTestExtern___lam__0___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_elabTestExtern___lam__0___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_elabTestExtern___lam__0___closed__18_value: crate::leanh::LeanStringObject<44> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 44,
        m_capacity: 44,
        m_length: 43,
        m_data: [
            116, 101, 115, 116, 95, 101, 120, 116, 101, 114, 110, 58, 32, 101, 120, 112, 101, 99,
            116, 115, 32, 97, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 97, 112, 112, 108,
            105, 99, 97, 116, 105, 111, 110, 0,
        ],
    };
static mut l_elabTestExtern___lam__0___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_elabTestExtern___lam__0___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_elabTestExtern___lam__0___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_410_ = crate::leanh::lean_box(0);
    v___x_411_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_412_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_412_, 0, v___x_411_);
    crate::leanh::lean_ctor_set(v___x_412_, 1, v___x_410_);
    return v___x_412_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_414_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0);
    v___x_415_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_415_, 0, v___x_414_);
    return v___x_415_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___boxed(
    mut v___y_416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_417_ = l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg();
    return v_res_417_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0(
    mut v_00_u03b1_418_: *mut crate::leanh::LeanObject,
    mut v___y_419_: *mut crate::leanh::LeanObject,
    mut v___y_420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_422_ = l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg();
    return v___x_422_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___boxed(
    mut v_00_u03b1_423_: *mut crate::leanh::LeanObject,
    mut v___y_424_: *mut crate::leanh::LeanObject,
    mut v___y_425_: *mut crate::leanh::LeanObject,
    mut v___y_426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_427_ = l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0(
        v_00_u03b1_423_,
        v___y_424_,
        v___y_425_,
    );
    crate::leanh::lean_dec(v___y_425_);
    crate::leanh::lean_dec_ref(v___y_424_);
    return v_res_427_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1(
    mut v_msgData_428_: *mut crate::leanh::LeanObject,
    mut v___y_429_: *mut crate::leanh::LeanObject,
    mut v___y_430_: *mut crate::leanh::LeanObject,
    mut v___y_431_: *mut crate::leanh::LeanObject,
    mut v___y_432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_434_ = lean_st_ref_get(v___y_432_);
    v_env_435_ = crate::leanh::lean_ctor_get(v___x_434_, 0);
    crate::leanh::lean_inc_ref(v_env_435_);
    crate::leanh::lean_dec(v___x_434_);
    v___x_436_ = lean_st_ref_get(v___y_430_);
    v_mctx_437_ = crate::leanh::lean_ctor_get(v___x_436_, 0);
    crate::leanh::lean_inc_ref(v_mctx_437_);
    crate::leanh::lean_dec(v___x_436_);
    v_lctx_438_ = crate::leanh::lean_ctor_get(v___y_429_, 2);
    v_options_439_ = crate::leanh::lean_ctor_get(v___y_431_, 2);
    crate::leanh::lean_inc_ref(v_options_439_);
    crate::leanh::lean_inc_ref(v_lctx_438_);
    v___x_440_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_440_, 0, v_env_435_);
    crate::leanh::lean_ctor_set(v___x_440_, 1, v_mctx_437_);
    crate::leanh::lean_ctor_set(v___x_440_, 2, v_lctx_438_);
    crate::leanh::lean_ctor_set(v___x_440_, 3, v_options_439_);
    v___x_441_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_441_, 0, v___x_440_);
    crate::leanh::lean_ctor_set(v___x_441_, 1, v_msgData_428_);
    v___x_442_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_442_, 0, v___x_441_);
    return v___x_442_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1___boxed(
    mut v_msgData_443_: *mut crate::leanh::LeanObject,
    mut v___y_444_: *mut crate::leanh::LeanObject,
    mut v___y_445_: *mut crate::leanh::LeanObject,
    mut v___y_446_: *mut crate::leanh::LeanObject,
    mut v___y_447_: *mut crate::leanh::LeanObject,
    mut v___y_448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_449_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1(v_msgData_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
    crate::leanh::lean_dec(v___y_447_);
    crate::leanh::lean_dec_ref(v___y_446_);
    crate::leanh::lean_dec(v___y_445_);
    crate::leanh::lean_dec_ref(v___y_444_);
    return v_res_449_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3(
    mut v_opts_450_: *mut crate::leanh::LeanObject,
    mut v_opt_451_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_452_ = crate::leanh::lean_ctor_get(v_opt_451_, 0);
    v_defValue_453_ = crate::leanh::lean_ctor_get(v_opt_451_, 1);
    v_map_454_ = crate::leanh::lean_ctor_get(v_opts_450_, 0);
    v___x_455_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_454_,
            v_name_452_,
        );
    if crate::leanh::lean_obj_tag(v___x_455_) == 0 {
        let mut v___x_456_: u8 = 0;
        v___x_456_ = (crate::leanh::lean_unbox(v_defValue_453_) as u8);
        return v___x_456_;
    } else {
        let mut v_val_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_457_ = crate::leanh::lean_ctor_get(v___x_455_, 0);
        crate::leanh::lean_inc(v_val_457_);
        crate::leanh::lean_dec_ref_known(v___x_455_, 1);
        if crate::leanh::lean_obj_tag(v_val_457_) == 1 {
            let mut v_v_458_: u8 = 0;
            v_v_458_ = crate::leanh::lean_ctor_get_uint8(v_val_457_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_457_, 0);
            return v_v_458_;
        } else {
            let mut v___x_459_: u8 = 0;
            crate::leanh::lean_dec(v_val_457_);
            v___x_459_ = (crate::leanh::lean_unbox(v_defValue_453_) as u8);
            return v___x_459_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3___boxed(
    mut v_opts_460_: *mut crate::leanh::LeanObject,
    mut v_opt_461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_462_: u8 = 0;
    let mut v_r_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_462_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3(v_opts_460_, v_opt_461_);
    crate::leanh::lean_dec_ref(v_opt_461_);
    crate::leanh::lean_dec_ref(v_opts_460_);
    v_r_463_ = crate::leanh::lean_box((v_res_462_) as usize);
    return v_r_463_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_464_ = crate::leanh::lean_box(1);
    v___x_465_ = l_Lean_MessageData_ofFormat(v___x_464_);
    return v___x_465_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_469_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__2;
    v___x_470_ = l_Lean_MessageData_ofFormat(v___x_469_);
    return v___x_470_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4(
    mut v_x_471_: *mut crate::leanh::LeanObject,
    mut v_x_472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_477_: u8 = 0;
    let mut v_before_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_481_: u8 = 0;
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_494_: u8 = 0;
    let mut v_unused_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_472_) == 0 {
                    return v_x_471_;
                } else {
                    v_head_473_ = crate::leanh::lean_ctor_get(v_x_472_, 0);
                    v_tail_474_ = crate::leanh::lean_ctor_get(v_x_472_, 1);
                    v_isSharedCheck_496_ = (!crate::leanh::lean_is_exclusive(v_x_472_)) as u8;
                    if v_isSharedCheck_496_ == 0 {
                        v___x_476_ = v_x_472_;
                        v_isShared_477_ = v_isSharedCheck_496_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_474_);
                        crate::leanh::lean_inc(v_head_473_);
                        crate::leanh::lean_dec(v_x_472_);
                        v___x_476_ = crate::leanh::lean_box(0);
                        v_isShared_477_ = v_isSharedCheck_496_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_478_ = crate::leanh::lean_ctor_get(v_head_473_, 0);
                v_isSharedCheck_494_ = (!crate::leanh::lean_is_exclusive(v_head_473_)) as u8;
                if v_isSharedCheck_494_ == 0 {
                    v_unused_495_ = crate::leanh::lean_ctor_get(v_head_473_, 1);
                    crate::leanh::lean_dec(v_unused_495_);
                    v___x_480_ = v_head_473_;
                    v_isShared_481_ = v_isSharedCheck_494_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_478_);
                    crate::leanh::lean_dec(v_head_473_);
                    v___x_480_ = crate::leanh::lean_box(0);
                    v_isShared_481_ = v_isSharedCheck_494_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_482_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0);
                if v_isShared_481_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_480_, 7);
                    crate::leanh::lean_ctor_set(v___x_480_, 1, v___x_482_);
                    crate::leanh::lean_ctor_set(v___x_480_, 0, v_x_471_);
                    v___x_484_ = v___x_480_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_493_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_493_, 0, v_x_471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_493_, 1, v___x_482_);
                    v___x_484_ = v_reuseFailAlloc_493_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_485_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3);
                if v_isShared_477_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_476_, 7);
                    crate::leanh::lean_ctor_set(v___x_476_, 1, v___x_485_);
                    crate::leanh::lean_ctor_set(v___x_476_, 0, v___x_484_);
                    v___x_487_ = v___x_476_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_492_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_492_, 1, v___x_485_);
                    v___x_487_ = v_reuseFailAlloc_492_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_488_ = l_Lean_MessageData_ofSyntax(v_before_478_);
                v___x_489_ = l_Lean_indentD(v___x_488_);
                v___x_490_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_490_, 0, v___x_487_);
                crate::leanh::lean_ctor_set(v___x_490_, 1, v___x_489_);
                v_x_471_ = v___x_490_;
                v_x_472_ = v_tail_474_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_500_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__1;
    v___x_501_ = l_Lean_MessageData_ofFormat(v___x_500_);
    return v___x_501_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(
    mut v_msgData_502_: *mut crate::leanh::LeanObject,
    mut v_macroStack_503_: *mut crate::leanh::LeanObject,
    mut v___y_504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: u8 = 0;
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_515_: u8 = 0;
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_527_: u8 = 0;
    let mut v_unused_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_506_ = crate::leanh::lean_ctor_get(v___y_504_, 2);
                v___x_507_ = l_Lean_Elab_pp_macroStack;
                v___x_508_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3(v_options_506_, v___x_507_);
                if v___x_508_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_503_);
                    v___x_509_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_509_, 0, v_msgData_502_);
                    return v___x_509_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_503_) == 0 {
                        v___x_510_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_510_, 0, v_msgData_502_);
                        return v___x_510_;
                    } else {
                        v_head_511_ = crate::leanh::lean_ctor_get(v_macroStack_503_, 0);
                        crate::leanh::lean_inc(v_head_511_);
                        v_after_512_ = crate::leanh::lean_ctor_get(v_head_511_, 1);
                        v_isSharedCheck_527_ =
                            (!crate::leanh::lean_is_exclusive(v_head_511_)) as u8;
                        if v_isSharedCheck_527_ == 0 {
                            v_unused_528_ = crate::leanh::lean_ctor_get(v_head_511_, 0);
                            crate::leanh::lean_dec(v_unused_528_);
                            v___x_514_ = v_head_511_;
                            v_isShared_515_ = v_isSharedCheck_527_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_512_);
                            crate::leanh::lean_dec(v_head_511_);
                            v___x_514_ = crate::leanh::lean_box(0);
                            v_isShared_515_ = v_isSharedCheck_527_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_516_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0);
                if v_isShared_515_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_514_, 7);
                    crate::leanh::lean_ctor_set(v___x_514_, 1, v___x_516_);
                    crate::leanh::lean_ctor_set(v___x_514_, 0, v_msgData_502_);
                    v___x_518_ = v___x_514_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_526_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_526_, 0, v_msgData_502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_526_, 1, v___x_516_);
                    v___x_518_ = v_reuseFailAlloc_526_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_519_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2);
                v___x_520_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_520_, 0, v___x_518_);
                crate::leanh::lean_ctor_set(v___x_520_, 1, v___x_519_);
                v___x_521_ = l_Lean_MessageData_ofSyntax(v_after_512_);
                v___x_522_ = l_Lean_indentD(v___x_521_);
                v_msgData_523_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_523_, 0, v___x_520_);
                crate::leanh::lean_ctor_set(v_msgData_523_, 1, v___x_522_);
                v___x_524_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4(v_msgData_523_, v_macroStack_503_);
                v___x_525_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_525_, 0, v___x_524_);
                return v___x_525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___boxed(
    mut v_msgData_529_: *mut crate::leanh::LeanObject,
    mut v_macroStack_530_: *mut crate::leanh::LeanObject,
    mut v___y_531_: *mut crate::leanh::LeanObject,
    mut v___y_532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_533_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(v_msgData_529_, v_macroStack_530_, v___y_531_);
    crate::leanh::lean_dec_ref(v___y_531_);
    return v_res_533_;
}
pub unsafe fn l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(
    mut v_msg_534_: *mut crate::leanh::LeanObject,
    mut v___y_535_: *mut crate::leanh::LeanObject,
    mut v___y_536_: *mut crate::leanh::LeanObject,
    mut v___y_537_: *mut crate::leanh::LeanObject,
    mut v___y_538_: *mut crate::leanh::LeanObject,
    mut v___y_539_: *mut crate::leanh::LeanObject,
    mut v___y_540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_551_: u8 = 0;
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_556_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_542_ = crate::leanh::lean_ctor_get(v___y_539_, 5);
                v___x_543_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1(v_msg_534_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
                v_a_544_ = crate::leanh::lean_ctor_get(v___x_543_, 0);
                crate::leanh::lean_inc(v_a_544_);
                crate::leanh::lean_dec_ref(v___x_543_);
                v_macroStack_545_ = crate::leanh::lean_ctor_get(v___y_535_, 1);
                v___x_546_ = l_Lean_Elab_getBetterRef(v_ref_542_, v_macroStack_545_);
                crate::leanh::lean_inc(v_macroStack_545_);
                v___x_547_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(v_a_544_, v_macroStack_545_, v___y_539_);
                v_a_548_ = crate::leanh::lean_ctor_get(v___x_547_, 0);
                v_isSharedCheck_556_ = (!crate::leanh::lean_is_exclusive(v___x_547_)) as u8;
                if v_isSharedCheck_556_ == 0 {
                    v___x_550_ = v___x_547_;
                    v_isShared_551_ = v_isSharedCheck_556_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_548_);
                    crate::leanh::lean_dec(v___x_547_);
                    v___x_550_ = crate::leanh::lean_box(0);
                    v_isShared_551_ = v_isSharedCheck_556_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_552_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_552_, 0, v___x_546_);
                crate::leanh::lean_ctor_set(v___x_552_, 1, v_a_548_);
                if v_isShared_551_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_550_, 1);
                    crate::leanh::lean_ctor_set(v___x_550_, 0, v___x_552_);
                    v___x_554_ = v___x_550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_555_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
                    v___x_554_ = v_reuseFailAlloc_555_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_554_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00elabTestExtern_spec__1___redArg___boxed(
    mut v_msg_557_: *mut crate::leanh::LeanObject,
    mut v___y_558_: *mut crate::leanh::LeanObject,
    mut v___y_559_: *mut crate::leanh::LeanObject,
    mut v___y_560_: *mut crate::leanh::LeanObject,
    mut v___y_561_: *mut crate::leanh::LeanObject,
    mut v___y_562_: *mut crate::leanh::LeanObject,
    mut v___y_563_: *mut crate::leanh::LeanObject,
    mut v___y_564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_565_ = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(
        v_msg_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_,
    );
    crate::leanh::lean_dec(v___y_563_);
    crate::leanh::lean_dec_ref(v___y_562_);
    crate::leanh::lean_dec(v___y_561_);
    crate::leanh::lean_dec_ref(v___y_560_);
    crate::leanh::lean_dec(v___y_559_);
    crate::leanh::lean_dec_ref(v___y_558_);
    return v_res_565_;
}
pub unsafe fn _init_l_elabTestExtern___lam__0___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_571_ = crate::leanh::lean_box(0);
    v___x_572_ = l_elabTestExtern___lam__0___closed__2;
    v___x_573_ = l_Lean_Expr_const___override(v___x_572_, v___x_571_);
    return v___x_573_;
}
pub unsafe fn _init_l_elabTestExtern___lam__0___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_577_ = crate::leanh::lean_box(0);
    v___x_578_ = l_elabTestExtern___lam__0___closed__5;
    v___x_579_ = l_Lean_Expr_const___override(v___x_578_, v___x_577_);
    return v___x_579_;
}
pub unsafe fn _init_l_elabTestExtern___lam__0___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_583_ = l_elabTestExtern___lam__0___closed__8;
    v___x_584_ = l_Lean_MessageData_ofFormat(v___x_583_);
    return v___x_584_;
}
pub unsafe fn _init_l_elabTestExtern___lam__0___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_586_ = l_elabTestExtern___lam__0___closed__10;
    v___x_587_ = l_Lean_stringToMessageData(v___x_586_);
    return v___x_587_;
}
pub unsafe fn _init_l_elabTestExtern___lam__0___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_589_ = l_elabTestExtern___lam__0___closed__12;
    v___x_590_ = l_Lean_stringToMessageData(v___x_589_);
    return v___x_590_;
}
pub unsafe fn _init_l_elabTestExtern___lam__0___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_592_ = l_elabTestExtern___lam__0___closed__14;
    v___x_593_ = l_Lean_stringToMessageData(v___x_592_);
    return v___x_593_;
}
pub unsafe fn _init_l_elabTestExtern___lam__0___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_595_ = l_elabTestExtern___lam__0___closed__16;
    v___x_596_ = l_Lean_stringToMessageData(v___x_595_);
    return v___x_596_;
}
pub unsafe fn _init_l_elabTestExtern___lam__0___closed__19() -> *mut crate::leanh::LeanObject {
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_598_ = l_elabTestExtern___lam__0___closed__18;
    v___x_599_ = l_Lean_stringToMessageData(v___x_598_);
    return v___x_599_;
}
pub unsafe fn l_elabTestExtern___lam__0(
    mut v___x_600_: *mut crate::leanh::LeanObject,
    mut v___x_601_: *mut crate::leanh::LeanObject,
    mut v___x_602_: u8,
    mut v___y_603_: *mut crate::leanh::LeanObject,
    mut v___y_604_: *mut crate::leanh::LeanObject,
    mut v___y_605_: *mut crate::leanh::LeanObject,
    mut v___y_606_: *mut crate::leanh::LeanObject,
    mut v___y_607_: *mut crate::leanh::LeanObject,
    mut v___y_608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: u8 = 0;
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_631_: u8 = 0;
    let mut v___x_632_: u8 = 0;
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_647_: u8 = 0;
    let mut v_a_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_651_: u8 = 0;
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_655_: u8 = 0;
    let mut v_a_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_659_: u8 = 0;
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_663_: u8 = 0;
    let mut v_a_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_667_: u8 = 0;
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_671_: u8 = 0;
    let mut v_a_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_675_: u8 = 0;
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_679_: u8 = 0;
    let mut v___y_681_: u8 = 0;
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: u8 = 0;
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_696_: u8 = 0;
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_610_ = l_Lean_Elab_Term_elabTermAndSynthesize(
                    v___x_600_, v___x_601_, v___y_603_, v___y_604_, v___y_605_, v___y_606_,
                    v___y_607_, v___y_608_,
                );
                if crate::leanh::lean_obj_tag(v___x_610_) == 0 {
                    v_a_611_ = crate::leanh::lean_ctor_get(v___x_610_, 0);
                    crate::leanh::lean_inc(v_a_611_);
                    crate::leanh::lean_dec_ref_known(v___x_610_, 1);
                    v___x_612_ = l_Lean_Expr_getAppFn(v_a_611_);
                    if crate::leanh::lean_obj_tag(v___x_612_) == 4 {
                        v_declName_613_ = crate::leanh::lean_ctor_get(v___x_612_, 0);
                        crate::leanh::lean_inc_n(v_declName_613_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_612_, 2);
                        v___x_614_ = lean_st_ref_get(v___y_608_);
                        v_env_688_ = crate::leanh::lean_ctor_get(v___x_614_, 0);
                        crate::leanh::lean_inc_ref_n(v_env_688_, 2);
                        crate::leanh::lean_dec(v___x_614_);
                        v___x_689_ = l_Lean_isExtern(v_env_688_, v_declName_613_);
                        if v___x_689_ == 0 {
                            crate::leanh::lean_inc(v_declName_613_);
                            v___x_690_ =
                                l_Lean_Compiler_getImplementedBy_x3f(v_env_688_, v_declName_613_);
                            if crate::leanh::lean_obj_tag(v___x_690_) == 0 {
                                v___y_681_ = v___x_689_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_690_, 1);
                                v___y_681_ = v___x_602_;
                                state = 12;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_env_688_);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_612_);
                        crate::leanh::lean_dec(v_a_611_);
                        v___x_691_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__19),
                            core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__19_once),
                            _init_l_elabTestExtern___lam__0___closed__19,
                        );
                        v___x_692_ = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(
                            v___x_691_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_,
                            v___y_608_,
                        );
                        return v___x_692_;
                    }
                } else {
                    v_a_693_ = crate::leanh::lean_ctor_get(v___x_610_, 0);
                    v_isSharedCheck_700_ = (!crate::leanh::lean_is_exclusive(v___x_610_)) as u8;
                    if v_isSharedCheck_700_ == 0 {
                        v___x_695_ = v___x_610_;
                        v_isShared_696_ = v_isSharedCheck_700_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_693_);
                        crate::leanh::lean_dec(v___x_610_);
                        v___x_695_ = crate::leanh::lean_box(0);
                        v_isShared_696_ = v_isSharedCheck_700_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_611_);
                v___x_616_ = l_Lean_Meta_unfold(
                    v_a_611_,
                    v_declName_613_,
                    v___y_605_,
                    v___y_606_,
                    v___y_607_,
                    v___y_608_,
                );
                if crate::leanh::lean_obj_tag(v___x_616_) == 0 {
                    v_a_617_ = crate::leanh::lean_ctor_get(v___x_616_, 0);
                    crate::leanh::lean_inc(v_a_617_);
                    crate::leanh::lean_dec_ref_known(v___x_616_, 1);
                    v_expr_618_ = crate::leanh::lean_ctor_get(v_a_617_, 0);
                    crate::leanh::lean_inc_ref_n(v_expr_618_, 2);
                    crate::leanh::lean_dec(v_a_617_);
                    crate::leanh::lean_inc(v_a_611_);
                    v___x_619_ = l_Lean_Meta_mkEq(
                        v_a_611_,
                        v_expr_618_,
                        v___y_605_,
                        v___y_606_,
                        v___y_607_,
                        v___y_608_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_619_) == 0 {
                        v_a_620_ = crate::leanh::lean_ctor_get(v___x_619_, 0);
                        crate::leanh::lean_inc(v_a_620_);
                        crate::leanh::lean_dec_ref_known(v___x_619_, 1);
                        v___x_621_ = l_Lean_Meta_mkDecide(
                            v_a_620_, v___y_605_, v___y_606_, v___y_607_, v___y_608_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_621_) == 0 {
                            v_a_622_ = crate::leanh::lean_ctor_get(v___x_621_, 0);
                            crate::leanh::lean_inc(v_a_622_);
                            crate::leanh::lean_dec_ref_known(v___x_621_, 1);
                            v___x_623_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__3),
                                core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__3_once),
                                _init_l_elabTestExtern___lam__0___closed__3,
                            );
                            v___x_624_ = l_Lean_Expr_app___override(v___x_623_, v_a_622_);
                            v___x_625_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__6),
                                core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__6_once),
                                _init_l_elabTestExtern___lam__0___closed__6,
                            );
                            v___x_626_ = 1;
                            v___x_627_ = l_Lean_Meta_evalExpr___redArg(
                                v___x_625_, v___x_624_, v___x_626_, v___x_602_, v___y_605_,
                                v___y_606_, v___y_607_, v___y_608_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_627_) == 0 {
                                v_a_628_ = crate::leanh::lean_ctor_get(v___x_627_, 0);
                                v_isSharedCheck_647_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_627_)) as u8;
                                if v_isSharedCheck_647_ == 0 {
                                    v___x_630_ = v___x_627_;
                                    v_isShared_631_ = v_isSharedCheck_647_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_628_);
                                    crate::leanh::lean_dec(v___x_627_);
                                    v___x_630_ = crate::leanh::lean_box(0);
                                    v_isShared_631_ = v_isSharedCheck_647_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_expr_618_);
                                crate::leanh::lean_dec(v_a_611_);
                                v_a_648_ = crate::leanh::lean_ctor_get(v___x_627_, 0);
                                v_isSharedCheck_655_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_627_)) as u8;
                                if v_isSharedCheck_655_ == 0 {
                                    v___x_650_ = v___x_627_;
                                    v_isShared_651_ = v_isSharedCheck_655_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_648_);
                                    crate::leanh::lean_dec(v___x_627_);
                                    v___x_650_ = crate::leanh::lean_box(0);
                                    v_isShared_651_ = v_isSharedCheck_655_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_expr_618_);
                            crate::leanh::lean_dec(v_a_611_);
                            v_a_656_ = crate::leanh::lean_ctor_get(v___x_621_, 0);
                            v_isSharedCheck_663_ =
                                (!crate::leanh::lean_is_exclusive(v___x_621_)) as u8;
                            if v_isSharedCheck_663_ == 0 {
                                v___x_658_ = v___x_621_;
                                v_isShared_659_ = v_isSharedCheck_663_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_656_);
                                crate::leanh::lean_dec(v___x_621_);
                                v___x_658_ = crate::leanh::lean_box(0);
                                v_isShared_659_ = v_isSharedCheck_663_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_expr_618_);
                        crate::leanh::lean_dec(v_a_611_);
                        v_a_664_ = crate::leanh::lean_ctor_get(v___x_619_, 0);
                        v_isSharedCheck_671_ = (!crate::leanh::lean_is_exclusive(v___x_619_)) as u8;
                        if v_isSharedCheck_671_ == 0 {
                            v___x_666_ = v___x_619_;
                            v_isShared_667_ = v_isSharedCheck_671_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_664_);
                            crate::leanh::lean_dec(v___x_619_);
                            v___x_666_ = crate::leanh::lean_box(0);
                            v_isShared_667_ = v_isSharedCheck_671_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_611_);
                    v_a_672_ = crate::leanh::lean_ctor_get(v___x_616_, 0);
                    v_isSharedCheck_679_ = (!crate::leanh::lean_is_exclusive(v___x_616_)) as u8;
                    if v_isSharedCheck_679_ == 0 {
                        v___x_674_ = v___x_616_;
                        v_isShared_675_ = v_isSharedCheck_679_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_672_);
                        crate::leanh::lean_dec(v___x_616_);
                        v___x_674_ = crate::leanh::lean_box(0);
                        v_isShared_675_ = v_isSharedCheck_679_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_632_ = (crate::leanh::lean_unbox(v_a_628_) as u8);
                crate::leanh::lean_dec(v_a_628_);
                if v___x_632_ == 0 {
                    crate::leanh::lean_del_object(v___x_630_);
                    v___x_633_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__9),
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__9_once),
                        _init_l_elabTestExtern___lam__0___closed__9,
                    );
                    v___x_634_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__11),
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__11_once),
                        _init_l_elabTestExtern___lam__0___closed__11,
                    );
                    v___x_635_ = l_Lean_MessageData_ofExpr(v_a_611_);
                    v___x_636_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_636_, 0, v___x_634_);
                    crate::leanh::lean_ctor_set(v___x_636_, 1, v___x_635_);
                    v___x_637_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__13),
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__13_once),
                        _init_l_elabTestExtern___lam__0___closed__13,
                    );
                    v___x_638_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_638_, 0, v___x_636_);
                    crate::leanh::lean_ctor_set(v___x_638_, 1, v___x_637_);
                    v___x_639_ = l_Lean_MessageData_ofExpr(v_expr_618_);
                    v___x_640_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_640_, 0, v___x_638_);
                    crate::leanh::lean_ctor_set(v___x_640_, 1, v___x_639_);
                    v___x_641_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_641_, 0, v___x_633_);
                    crate::leanh::lean_ctor_set(v___x_641_, 1, v___x_640_);
                    v___x_642_ = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(
                        v___x_641_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_,
                        v___y_608_,
                    );
                    return v___x_642_;
                } else {
                    crate::leanh::lean_dec_ref(v_expr_618_);
                    crate::leanh::lean_dec(v_a_611_);
                    v___x_643_ = crate::leanh::lean_box(0);
                    if v_isShared_631_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_630_, 0, v___x_643_);
                        v___x_645_ = v___x_630_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_646_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
                        v___x_645_ = v_reuseFailAlloc_646_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_645_;
            }
            4 => {
                if v_isShared_651_ == 0 {
                    v___x_653_ = v___x_650_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_654_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
                    v___x_653_ = v_reuseFailAlloc_654_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_653_;
            }
            6 => {
                if v_isShared_659_ == 0 {
                    v___x_661_ = v___x_658_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_662_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
                    v___x_661_ = v_reuseFailAlloc_662_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_661_;
            }
            8 => {
                if v_isShared_667_ == 0 {
                    v___x_669_ = v___x_666_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_670_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
                    v___x_669_ = v_reuseFailAlloc_670_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_669_;
            }
            10 => {
                if v_isShared_675_ == 0 {
                    v___x_677_ = v___x_674_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_678_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
                    v___x_677_ = v_reuseFailAlloc_678_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_677_;
            }
            12 => {
                if v___y_681_ == 0 {
                    crate::leanh::lean_dec(v_a_611_);
                    v___x_682_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__15),
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__15_once),
                        _init_l_elabTestExtern___lam__0___closed__15,
                    );
                    v___x_683_ = l_Lean_MessageData_ofName(v_declName_613_);
                    v___x_684_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_684_, 0, v___x_682_);
                    crate::leanh::lean_ctor_set(v___x_684_, 1, v___x_683_);
                    v___x_685_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__17),
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__17_once),
                        _init_l_elabTestExtern___lam__0___closed__17,
                    );
                    v___x_686_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_686_, 0, v___x_684_);
                    crate::leanh::lean_ctor_set(v___x_686_, 1, v___x_685_);
                    v___x_687_ = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(
                        v___x_686_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_,
                        v___y_608_,
                    );
                    return v___x_687_;
                } else {
                    state = 1;
                    continue;
                }
            }
            13 => {
                if v_isShared_696_ == 0 {
                    v___x_698_ = v___x_695_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_699_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
                    v___x_698_ = v_reuseFailAlloc_699_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_698_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_elabTestExtern___lam__0___boxed(
    mut v___x_701_: *mut crate::leanh::LeanObject,
    mut v___x_702_: *mut crate::leanh::LeanObject,
    mut v___x_703_: *mut crate::leanh::LeanObject,
    mut v___y_704_: *mut crate::leanh::LeanObject,
    mut v___y_705_: *mut crate::leanh::LeanObject,
    mut v___y_706_: *mut crate::leanh::LeanObject,
    mut v___y_707_: *mut crate::leanh::LeanObject,
    mut v___y_708_: *mut crate::leanh::LeanObject,
    mut v___y_709_: *mut crate::leanh::LeanObject,
    mut v___y_710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5035__boxed_711_: u8 = 0;
    let mut v_res_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5035__boxed_711_ = (crate::leanh::lean_unbox(v___x_703_) as u8);
    v_res_712_ = l_elabTestExtern___lam__0(
        v___x_701_,
        v___x_702_,
        v___x_5035__boxed_711_,
        v___y_704_,
        v___y_705_,
        v___y_706_,
        v___y_707_,
        v___y_708_,
        v___y_709_,
    );
    crate::leanh::lean_dec(v___y_709_);
    crate::leanh::lean_dec_ref(v___y_708_);
    crate::leanh::lean_dec(v___y_707_);
    crate::leanh::lean_dec_ref(v___y_706_);
    crate::leanh::lean_dec(v___y_705_);
    crate::leanh::lean_dec_ref(v___y_704_);
    return v_res_712_;
}
pub unsafe fn l_elabTestExtern(
    mut v_x_713_: *mut crate::leanh::LeanObject,
    mut v_a_714_: *mut crate::leanh::LeanObject,
    mut v_a_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: u8 = 0;
    v___x_717_ = l_testExternCmd___closed__1;
    crate::leanh::lean_inc(v_x_713_);
    v___x_718_ = l_Lean_Syntax_isOfKind(v_x_713_, v___x_717_);
    if v___x_718_ == 0 {
        let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_713_);
        v___x_719_ = l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg();
        return v___x_719_;
    } else {
        let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_720_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_721_ = l_Lean_Syntax_getArg(v_x_713_, v___x_720_);
        crate::leanh::lean_dec(v_x_713_);
        v___x_722_ = crate::leanh::lean_box(0);
        v___x_723_ = crate::leanh::lean_box((v___x_718_) as usize);
        v___f_724_ = crate::leanh::lean_alloc_closure(
            l_elabTestExtern___lam__0___boxed as *mut core::ffi::c_void,
            10,
            3,
        );
        crate::leanh::lean_closure_set(v___f_724_, 0, v___x_721_);
        crate::leanh::lean_closure_set(v___f_724_, 1, v___x_722_);
        crate::leanh::lean_closure_set(v___f_724_, 2, v___x_723_);
        v___x_725_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_724_, v_a_714_, v_a_715_);
        return v___x_725_;
    }
}
pub unsafe fn l_elabTestExtern___boxed(
    mut v_x_726_: *mut crate::leanh::LeanObject,
    mut v_a_727_: *mut crate::leanh::LeanObject,
    mut v_a_728_: *mut crate::leanh::LeanObject,
    mut v_a_729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_730_ = l_elabTestExtern(v_x_726_, v_a_727_, v_a_728_);
    crate::leanh::lean_dec(v_a_728_);
    crate::leanh::lean_dec_ref(v_a_727_);
    return v_res_730_;
}
pub unsafe fn l_Lean_throwError___at___00elabTestExtern_spec__1(
    mut v_00_u03b1_731_: *mut crate::leanh::LeanObject,
    mut v_msg_732_: *mut crate::leanh::LeanObject,
    mut v___y_733_: *mut crate::leanh::LeanObject,
    mut v___y_734_: *mut crate::leanh::LeanObject,
    mut v___y_735_: *mut crate::leanh::LeanObject,
    mut v___y_736_: *mut crate::leanh::LeanObject,
    mut v___y_737_: *mut crate::leanh::LeanObject,
    mut v___y_738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_740_ = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(
        v_msg_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_,
    );
    return v___x_740_;
}
pub unsafe fn l_Lean_throwError___at___00elabTestExtern_spec__1___boxed(
    mut v_00_u03b1_741_: *mut crate::leanh::LeanObject,
    mut v_msg_742_: *mut crate::leanh::LeanObject,
    mut v___y_743_: *mut crate::leanh::LeanObject,
    mut v___y_744_: *mut crate::leanh::LeanObject,
    mut v___y_745_: *mut crate::leanh::LeanObject,
    mut v___y_746_: *mut crate::leanh::LeanObject,
    mut v___y_747_: *mut crate::leanh::LeanObject,
    mut v___y_748_: *mut crate::leanh::LeanObject,
    mut v___y_749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_750_ = l_Lean_throwError___at___00elabTestExtern_spec__1(
        v_00_u03b1_741_,
        v_msg_742_,
        v___y_743_,
        v___y_744_,
        v___y_745_,
        v___y_746_,
        v___y_747_,
        v___y_748_,
    );
    crate::leanh::lean_dec(v___y_748_);
    crate::leanh::lean_dec_ref(v___y_747_);
    crate::leanh::lean_dec(v___y_746_);
    crate::leanh::lean_dec_ref(v___y_745_);
    crate::leanh::lean_dec(v___y_744_);
    crate::leanh::lean_dec_ref(v___y_743_);
    return v_res_750_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2(
    mut v_msgData_751_: *mut crate::leanh::LeanObject,
    mut v_macroStack_752_: *mut crate::leanh::LeanObject,
    mut v___y_753_: *mut crate::leanh::LeanObject,
    mut v___y_754_: *mut crate::leanh::LeanObject,
    mut v___y_755_: *mut crate::leanh::LeanObject,
    mut v___y_756_: *mut crate::leanh::LeanObject,
    mut v___y_757_: *mut crate::leanh::LeanObject,
    mut v___y_758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_760_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(v_msgData_751_, v_macroStack_752_, v___y_757_);
    return v___x_760_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___boxed(
    mut v_msgData_761_: *mut crate::leanh::LeanObject,
    mut v_macroStack_762_: *mut crate::leanh::LeanObject,
    mut v___y_763_: *mut crate::leanh::LeanObject,
    mut v___y_764_: *mut crate::leanh::LeanObject,
    mut v___y_765_: *mut crate::leanh::LeanObject,
    mut v___y_766_: *mut crate::leanh::LeanObject,
    mut v___y_767_: *mut crate::leanh::LeanObject,
    mut v___y_768_: *mut crate::leanh::LeanObject,
    mut v___y_769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_770_ =
        l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2(
            v_msgData_761_,
            v_macroStack_762_,
            v___y_763_,
            v___y_764_,
            v___y_765_,
            v___y_766_,
            v___y_767_,
            v___y_768_,
        );
    crate::leanh::lean_dec(v___y_768_);
    crate::leanh::lean_dec_ref(v___y_767_);
    crate::leanh::lean_dec(v___y_766_);
    crate::leanh::lean_dec_ref(v___y_765_);
    crate::leanh::lean_dec(v___y_764_);
    crate::leanh::lean_dec_ref(v___y_763_);
    return v_res_770_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_TestExtern(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Exception(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_TestExtern(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Unfold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Eval(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_ImplementedByAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_ExternAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_TestExtern(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Unfold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Eval(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_ImplementedByAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Exception(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_ExternAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_TestExtern(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_TestExtern(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_TestExtern(builtin);
}
