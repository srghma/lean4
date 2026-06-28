// Lean compiler output
// Module: Lean.Util.TestExtern
// Imports: Lean.Meta.Tactic.Unfold Lean.Meta.Eval Lean.Compiler.ImplementedByAttr Lean.Elab.Command Init.Notation Lean.Exception Lean.Compiler.ExternAttr
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
};
use crate::r#gen::Lean::Compiler::ExternAttr::{
    initialize_Lean_Compiler_ExternAttr, l_Lean_isExtern, meta_initialize_Lean_Compiler_ExternAttr,
};
use crate::r#gen::Lean::Compiler::ImplementedByAttr::{
    initialize_Lean_Compiler_ImplementedByAttr, l_Lean_Compiler_getImplementedBy_x3f,
    meta_initialize_Lean_Compiler_ImplementedByAttr,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_liftTermElabM___redArg,
    meta_initialize_Lean_Elab_Command,
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
    initialize_Lean_Meta_Eval, l_Lean_Meta_evalExpr___redArg, meta_initialize_Lean_Meta_Eval,
};
use crate::r#gen::Lean::Meta::Tactic::Unfold::{
    initialize_Lean_Meta_Tactic_Unfold, l_Lean_Meta_unfold, meta_initialize_Lean_Meta_Tactic_Unfold,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_testExternCmd___closed__0_value: LeanStringObject<14> = LeanStringObject {
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
        116, 101, 115, 116, 69, 120, 116, 101, 114, 110, 67, 109, 100, 0,
    ],
};
static mut l_testExternCmd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__0_value) as *mut LeanObject;
pub static l_testExternCmd___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_testExternCmd___closed__0_value) as *mut LeanObject,
        15638152521579042923 as *mut LeanObject,
    ],
};
static mut l_testExternCmd___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__1_value) as *mut LeanObject;
pub static l_testExternCmd___closed__2_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_testExternCmd___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__2_value) as *mut LeanObject;
pub static l_testExternCmd___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_testExternCmd___closed__2_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_testExternCmd___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__3_value) as *mut LeanObject;
pub static l_testExternCmd___closed__4_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_testExternCmd___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__4_value) as *mut LeanObject;
pub static l_testExternCmd___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_testExternCmd___closed__4_value) as *mut LeanObject],
};
static mut l_testExternCmd___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__5_value) as *mut LeanObject;
pub static l_testExternCmd___closed__6_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_testExternCmd___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__6_value) as *mut LeanObject;
pub static l_testExternCmd___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_testExternCmd___closed__6_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_testExternCmd___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__7_value) as *mut LeanObject;
pub static l_testExternCmd___closed__8_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_testExternCmd___closed__7_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_testExternCmd___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__8_value) as *mut LeanObject;
pub static l_testExternCmd___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_testExternCmd___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_testExternCmd___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_testExternCmd___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_testExternCmd___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__9_value) as *mut LeanObject;
pub static l_testExternCmd___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_testExternCmd___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_testExternCmd___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_testExternCmd___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__10_value) as *mut LeanObject;
pub static mut l_testExternCmd: *mut LeanObject =
    core::ptr::addr_of!(l_testExternCmd___closed__10_value) as *mut LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_elabTestExtern___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_elabTestExtern___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__0_value) as *mut LeanObject;
pub static l_elabTestExtern___lam__0___closed__1_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_elabTestExtern___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__1_value) as *mut LeanObject;
static l_elabTestExtern___lam__0___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
pub static l_elabTestExtern___lam__0___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__1_value) as *mut LeanObject,
        2227249244235744626 as *mut LeanObject,
    ],
};
static mut l_elabTestExtern___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__2_value) as *mut LeanObject;
static mut l_elabTestExtern___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_elabTestExtern___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_elabTestExtern___lam__0___closed__4_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_elabTestExtern___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__4_value) as *mut LeanObject;
pub static l_elabTestExtern___lam__0___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__4_value) as *mut LeanObject,
        12882480457794858234 as *mut LeanObject,
    ],
};
static mut l_elabTestExtern___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__5_value) as *mut LeanObject;
static mut l_elabTestExtern___lam__0___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_elabTestExtern___lam__0___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_elabTestExtern___lam__0___closed__7_value: LeanStringObject<68> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 68,
    m_capacity: 68,
    m_length: 67,
    m_data: [
        110, 97, 116, 105, 118, 101, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 97, 116, 105,
        111, 110, 32, 100, 105, 100, 32, 110, 111, 116, 32, 97, 103, 114, 101, 101, 32, 119, 105,
        116, 104, 32, 114, 101, 102, 101, 114, 101, 110, 99, 101, 32, 105, 109, 112, 108, 101, 109,
        101, 110, 116, 97, 116, 105, 111, 110, 33, 10, 0,
    ],
};
static mut l_elabTestExtern___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__7_value) as *mut LeanObject;
pub static l_elabTestExtern___lam__0___closed__8_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__7_value) as *mut LeanObject],
};
static mut l_elabTestExtern___lam__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__8_value) as *mut LeanObject;
static mut l_elabTestExtern___lam__0___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_elabTestExtern___lam__0___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_elabTestExtern___lam__0___closed__10_value: LeanStringObject<31> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        67, 111, 109, 112, 97, 114, 101, 32, 116, 104, 101, 32, 111, 117, 116, 112, 117, 116, 115,
        32, 111, 102, 58, 10, 35, 101, 118, 97, 108, 32, 0,
    ],
};
static mut l_elabTestExtern___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__10_value) as *mut LeanObject;
static mut l_elabTestExtern___lam__0___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_elabTestExtern___lam__0___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_elabTestExtern___lam__0___closed__12_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_elabTestExtern___lam__0___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__12_value) as *mut LeanObject;
static mut l_elabTestExtern___lam__0___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_elabTestExtern___lam__0___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_elabTestExtern___lam__0___closed__14_value: LeanStringObject<14> = LeanStringObject {
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
        116, 101, 115, 116, 95, 101, 120, 116, 101, 114, 110, 58, 32, 0,
    ],
};
static mut l_elabTestExtern___lam__0___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__14_value) as *mut LeanObject;
static mut l_elabTestExtern___lam__0___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_elabTestExtern___lam__0___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_elabTestExtern___lam__0___closed__16_value: LeanStringObject<69> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 69,
    m_capacity: 69,
    m_length: 68,
    m_data: [
        32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 97, 110, 32, 64, 91,
        101, 120, 116, 101, 114, 110, 93, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 111,
        114, 32, 64, 91, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 95, 98, 121, 93,
        32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0,
    ],
};
static mut l_elabTestExtern___lam__0___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__16_value) as *mut LeanObject;
static mut l_elabTestExtern___lam__0___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_elabTestExtern___lam__0___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_elabTestExtern___lam__0___closed__18_value: LeanStringObject<44> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        116, 101, 115, 116, 95, 101, 120, 116, 101, 114, 110, 58, 32, 101, 120, 112, 101, 99, 116,
        115, 32, 97, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 97, 112, 112, 108, 105, 99, 97,
        116, 105, 111, 110, 0,
    ],
};
static mut l_elabTestExtern___lam__0___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_elabTestExtern___lam__0___closed__18_value) as *mut LeanObject;
static mut l_elabTestExtern___lam__0___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_elabTestExtern___lam__0___closed__19: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
    v___x_410_ = lean_box(0);
    v___x_411_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_412_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_412_, 0, v___x_411_);
    lean_ctor_set(v___x_412_, 1, v___x_410_);
    return v___x_412_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    v___x_414_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0);
    v___x_415_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_415_, 0, v___x_414_);
    return v___x_415_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___boxed(
    mut v___y_416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_417_: *mut LeanObject = core::ptr::null_mut();
    v_res_417_ = l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg();
    return v_res_417_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0(
    mut v_00_u03b1_418_: *mut LeanObject,
    mut v___y_419_: *mut LeanObject,
    mut v___y_420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    v___x_422_ = l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg();
    return v___x_422_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___boxed(
    mut v_00_u03b1_423_: *mut LeanObject,
    mut v___y_424_: *mut LeanObject,
    mut v___y_425_: *mut LeanObject,
    mut v___y_426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_427_: *mut LeanObject = core::ptr::null_mut();
    v_res_427_ = l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0(
        v_00_u03b1_423_,
        v___y_424_,
        v___y_425_,
    );
    lean_dec(v___y_425_);
    lean_dec_ref(v___y_424_);
    return v_res_427_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1(
    mut v_msgData_428_: *mut LeanObject,
    mut v___y_429_: *mut LeanObject,
    mut v___y_430_: *mut LeanObject,
    mut v___y_431_: *mut LeanObject,
    mut v___y_432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    v___x_434_ = lean_st_ref_get(v___y_432_);
    v_env_435_ = lean_ctor_get(v___x_434_, 0);
    lean_inc_ref(v_env_435_);
    lean_dec(v___x_434_);
    v___x_436_ = lean_st_ref_get(v___y_430_);
    v_mctx_437_ = lean_ctor_get(v___x_436_, 0);
    lean_inc_ref(v_mctx_437_);
    lean_dec(v___x_436_);
    v_lctx_438_ = lean_ctor_get(v___y_429_, 2);
    v_options_439_ = lean_ctor_get(v___y_431_, 2);
    lean_inc_ref(v_options_439_);
    lean_inc_ref(v_lctx_438_);
    v___x_440_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_440_, 0, v_env_435_);
    lean_ctor_set(v___x_440_, 1, v_mctx_437_);
    lean_ctor_set(v___x_440_, 2, v_lctx_438_);
    lean_ctor_set(v___x_440_, 3, v_options_439_);
    v___x_441_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_441_, 0, v___x_440_);
    lean_ctor_set(v___x_441_, 1, v_msgData_428_);
    v___x_442_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_442_, 0, v___x_441_);
    return v___x_442_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1___boxed(
    mut v_msgData_443_: *mut LeanObject,
    mut v___y_444_: *mut LeanObject,
    mut v___y_445_: *mut LeanObject,
    mut v___y_446_: *mut LeanObject,
    mut v___y_447_: *mut LeanObject,
    mut v___y_448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_449_: *mut LeanObject = core::ptr::null_mut();
    v_res_449_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1(v_msgData_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
    lean_dec(v___y_447_);
    lean_dec_ref(v___y_446_);
    lean_dec(v___y_445_);
    lean_dec_ref(v___y_444_);
    return v_res_449_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3(
    mut v_opts_450_: *mut LeanObject,
    mut v_opt_451_: *mut LeanObject,
) -> u8 {
    let mut v_name_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    v_name_452_ = lean_ctor_get(v_opt_451_, 0);
    v_defValue_453_ = lean_ctor_get(v_opt_451_, 1);
    v_map_454_ = lean_ctor_get(v_opts_450_, 0);
    v___x_455_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_454_,
            v_name_452_,
        );
    if lean_obj_tag(v___x_455_) == 0 {
        let mut v___x_456_: u8 = 0;
        v___x_456_ = (lean_unbox(v_defValue_453_) as u8);
        return v___x_456_;
    } else {
        let mut v_val_457_: *mut LeanObject = core::ptr::null_mut();
        v_val_457_ = lean_ctor_get(v___x_455_, 0);
        lean_inc(v_val_457_);
        lean_dec_ref_known(v___x_455_, 1);
        if lean_obj_tag(v_val_457_) == 1 {
            let mut v_v_458_: u8 = 0;
            v_v_458_ = lean_ctor_get_uint8(v_val_457_, 0 as u32);
            lean_dec_ref_known(v_val_457_, 0);
            return v_v_458_;
        } else {
            let mut v___x_459_: u8 = 0;
            lean_dec(v_val_457_);
            v___x_459_ = (lean_unbox(v_defValue_453_) as u8);
            return v___x_459_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3___boxed(
    mut v_opts_460_: *mut LeanObject,
    mut v_opt_461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_462_: u8 = 0;
    let mut v_r_463_: *mut LeanObject = core::ptr::null_mut();
    v_res_462_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3(v_opts_460_, v_opt_461_);
    lean_dec_ref(v_opt_461_);
    lean_dec_ref(v_opts_460_);
    v_r_463_ = lean_box((v_res_462_) as usize);
    return v_r_463_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0()
-> *mut LeanObject {
    let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    v___x_464_ = lean_box(1);
    v___x_465_ = l_Lean_MessageData_ofFormat(v___x_464_);
    return v___x_465_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3()
-> *mut LeanObject {
    let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    v___x_469_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__2;
    v___x_470_ = l_Lean_MessageData_ofFormat(v___x_469_);
    return v___x_470_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4(
    mut v_x_471_: *mut LeanObject,
    mut v_x_472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_477_: u8 = 0;
    let mut v_before_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_481_: u8 = 0;
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_494_: u8 = 0;
    let mut v_unused_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_472_) == 0 {
                    return v_x_471_;
                } else {
                    v_head_473_ = lean_ctor_get(v_x_472_, 0);
                    v_tail_474_ = lean_ctor_get(v_x_472_, 1);
                    v_isSharedCheck_496_ = (!lean_is_exclusive(v_x_472_)) as u8;
                    if v_isSharedCheck_496_ == 0 {
                        v___x_476_ = v_x_472_;
                        v_isShared_477_ = v_isSharedCheck_496_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_474_);
                        lean_inc(v_head_473_);
                        lean_dec(v_x_472_);
                        v___x_476_ = lean_box(0);
                        v_isShared_477_ = v_isSharedCheck_496_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_478_ = lean_ctor_get(v_head_473_, 0);
                v_isSharedCheck_494_ = (!lean_is_exclusive(v_head_473_)) as u8;
                if v_isSharedCheck_494_ == 0 {
                    v_unused_495_ = lean_ctor_get(v_head_473_, 1);
                    lean_dec(v_unused_495_);
                    v___x_480_ = v_head_473_;
                    v_isShared_481_ = v_isSharedCheck_494_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_478_);
                    lean_dec(v_head_473_);
                    v___x_480_ = lean_box(0);
                    v_isShared_481_ = v_isSharedCheck_494_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_482_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0);
                if v_isShared_481_ == 0 {
                    lean_ctor_set_tag(v___x_480_, 7);
                    lean_ctor_set(v___x_480_, 1, v___x_482_);
                    lean_ctor_set(v___x_480_, 0, v_x_471_);
                    v___x_484_ = v___x_480_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_493_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_493_, 0, v_x_471_);
                    lean_ctor_set(v_reuseFailAlloc_493_, 1, v___x_482_);
                    v___x_484_ = v_reuseFailAlloc_493_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_485_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3);
                if v_isShared_477_ == 0 {
                    lean_ctor_set_tag(v___x_476_, 7);
                    lean_ctor_set(v___x_476_, 1, v___x_485_);
                    lean_ctor_set(v___x_476_, 0, v___x_484_);
                    v___x_487_ = v___x_476_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_492_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_484_);
                    lean_ctor_set(v_reuseFailAlloc_492_, 1, v___x_485_);
                    v___x_487_ = v_reuseFailAlloc_492_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_488_ = l_Lean_MessageData_ofSyntax(v_before_478_);
                v___x_489_ = l_Lean_indentD(v___x_488_);
                v___x_490_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_490_, 0, v___x_487_);
                lean_ctor_set(v___x_490_, 1, v___x_489_);
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
-> *mut LeanObject {
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    v___x_500_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__1;
    v___x_501_ = l_Lean_MessageData_ofFormat(v___x_500_);
    return v___x_501_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(
    mut v_msgData_502_: *mut LeanObject,
    mut v_macroStack_503_: *mut LeanObject,
    mut v___y_504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: u8 = 0;
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_515_: u8 = 0;
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_527_: u8 = 0;
    let mut v_unused_528_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_506_ = lean_ctor_get(v___y_504_, 2);
                v___x_507_ = l_Lean_Elab_pp_macroStack;
                v___x_508_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3(v_options_506_, v___x_507_);
                if v___x_508_ == 0 {
                    lean_dec(v_macroStack_503_);
                    v___x_509_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_509_, 0, v_msgData_502_);
                    return v___x_509_;
                } else {
                    if lean_obj_tag(v_macroStack_503_) == 0 {
                        v___x_510_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_510_, 0, v_msgData_502_);
                        return v___x_510_;
                    } else {
                        v_head_511_ = lean_ctor_get(v_macroStack_503_, 0);
                        lean_inc(v_head_511_);
                        v_after_512_ = lean_ctor_get(v_head_511_, 1);
                        v_isSharedCheck_527_ = (!lean_is_exclusive(v_head_511_)) as u8;
                        if v_isSharedCheck_527_ == 0 {
                            v_unused_528_ = lean_ctor_get(v_head_511_, 0);
                            lean_dec(v_unused_528_);
                            v___x_514_ = v_head_511_;
                            v_isShared_515_ = v_isSharedCheck_527_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_512_);
                            lean_dec(v_head_511_);
                            v___x_514_ = lean_box(0);
                            v_isShared_515_ = v_isSharedCheck_527_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_516_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0);
                if v_isShared_515_ == 0 {
                    lean_ctor_set_tag(v___x_514_, 7);
                    lean_ctor_set(v___x_514_, 1, v___x_516_);
                    lean_ctor_set(v___x_514_, 0, v_msgData_502_);
                    v___x_518_ = v___x_514_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_526_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_526_, 0, v_msgData_502_);
                    lean_ctor_set(v_reuseFailAlloc_526_, 1, v___x_516_);
                    v___x_518_ = v_reuseFailAlloc_526_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_519_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2);
                v___x_520_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_520_, 0, v___x_518_);
                lean_ctor_set(v___x_520_, 1, v___x_519_);
                v___x_521_ = l_Lean_MessageData_ofSyntax(v_after_512_);
                v___x_522_ = l_Lean_indentD(v___x_521_);
                v_msgData_523_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_523_, 0, v___x_520_);
                lean_ctor_set(v_msgData_523_, 1, v___x_522_);
                v___x_524_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4(v_msgData_523_, v_macroStack_503_);
                v___x_525_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_525_, 0, v___x_524_);
                return v___x_525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___boxed(
    mut v_msgData_529_: *mut LeanObject,
    mut v_macroStack_530_: *mut LeanObject,
    mut v___y_531_: *mut LeanObject,
    mut v___y_532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_533_: *mut LeanObject = core::ptr::null_mut();
    v_res_533_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(v_msgData_529_, v_macroStack_530_, v___y_531_);
    lean_dec_ref(v___y_531_);
    return v_res_533_;
}
pub unsafe fn l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(
    mut v_msg_534_: *mut LeanObject,
    mut v___y_535_: *mut LeanObject,
    mut v___y_536_: *mut LeanObject,
    mut v___y_537_: *mut LeanObject,
    mut v___y_538_: *mut LeanObject,
    mut v___y_539_: *mut LeanObject,
    mut v___y_540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_551_: u8 = 0;
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_556_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_542_ = lean_ctor_get(v___y_539_, 5);
                v___x_543_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1(v_msg_534_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
                v_a_544_ = lean_ctor_get(v___x_543_, 0);
                lean_inc(v_a_544_);
                lean_dec_ref(v___x_543_);
                v_macroStack_545_ = lean_ctor_get(v___y_535_, 1);
                v___x_546_ = l_Lean_Elab_getBetterRef(v_ref_542_, v_macroStack_545_);
                lean_inc(v_macroStack_545_);
                v___x_547_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(v_a_544_, v_macroStack_545_, v___y_539_);
                v_a_548_ = lean_ctor_get(v___x_547_, 0);
                v_isSharedCheck_556_ = (!lean_is_exclusive(v___x_547_)) as u8;
                if v_isSharedCheck_556_ == 0 {
                    v___x_550_ = v___x_547_;
                    v_isShared_551_ = v_isSharedCheck_556_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_548_);
                    lean_dec(v___x_547_);
                    v___x_550_ = lean_box(0);
                    v_isShared_551_ = v_isSharedCheck_556_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_552_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_552_, 0, v___x_546_);
                lean_ctor_set(v___x_552_, 1, v_a_548_);
                if v_isShared_551_ == 0 {
                    lean_ctor_set_tag(v___x_550_, 1);
                    lean_ctor_set(v___x_550_, 0, v___x_552_);
                    v___x_554_ = v___x_550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
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
    mut v_msg_557_: *mut LeanObject,
    mut v___y_558_: *mut LeanObject,
    mut v___y_559_: *mut LeanObject,
    mut v___y_560_: *mut LeanObject,
    mut v___y_561_: *mut LeanObject,
    mut v___y_562_: *mut LeanObject,
    mut v___y_563_: *mut LeanObject,
    mut v___y_564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_565_: *mut LeanObject = core::ptr::null_mut();
    v_res_565_ = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(
        v_msg_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_,
    );
    lean_dec(v___y_563_);
    lean_dec_ref(v___y_562_);
    lean_dec(v___y_561_);
    lean_dec_ref(v___y_560_);
    lean_dec(v___y_559_);
    lean_dec_ref(v___y_558_);
    return v_res_565_;
}
pub unsafe fn _init_l_elabTestExtern___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    v___x_571_ = lean_box(0);
    v___x_572_ = l_elabTestExtern___lam__0___closed__2;
    v___x_573_ = l_Lean_Expr_const___override(v___x_572_, v___x_571_);
    return v___x_573_;
}
pub unsafe fn _init_l_elabTestExtern___lam__0___closed__6() -> *mut LeanObject {
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    v___x_577_ = lean_box(0);
    v___x_578_ = l_elabTestExtern___lam__0___closed__5;
    v___x_579_ = l_Lean_Expr_const___override(v___x_578_, v___x_577_);
    return v___x_579_;
}
pub unsafe fn _init_l_elabTestExtern___lam__0___closed__9() -> *mut LeanObject {
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    v___x_583_ = l_elabTestExtern___lam__0___closed__8;
    v___x_584_ = l_Lean_MessageData_ofFormat(v___x_583_);
    return v___x_584_;
}
pub unsafe fn _init_l_elabTestExtern___lam__0___closed__11() -> *mut LeanObject {
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    v___x_586_ = l_elabTestExtern___lam__0___closed__10;
    v___x_587_ = l_Lean_stringToMessageData(v___x_586_);
    return v___x_587_;
}
pub unsafe fn _init_l_elabTestExtern___lam__0___closed__13() -> *mut LeanObject {
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    v___x_589_ = l_elabTestExtern___lam__0___closed__12;
    v___x_590_ = l_Lean_stringToMessageData(v___x_589_);
    return v___x_590_;
}
pub unsafe fn _init_l_elabTestExtern___lam__0___closed__15() -> *mut LeanObject {
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    v___x_592_ = l_elabTestExtern___lam__0___closed__14;
    v___x_593_ = l_Lean_stringToMessageData(v___x_592_);
    return v___x_593_;
}
pub unsafe fn _init_l_elabTestExtern___lam__0___closed__17() -> *mut LeanObject {
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    v___x_595_ = l_elabTestExtern___lam__0___closed__16;
    v___x_596_ = l_Lean_stringToMessageData(v___x_595_);
    return v___x_596_;
}
pub unsafe fn _init_l_elabTestExtern___lam__0___closed__19() -> *mut LeanObject {
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    v___x_598_ = l_elabTestExtern___lam__0___closed__18;
    v___x_599_ = l_Lean_stringToMessageData(v___x_598_);
    return v___x_599_;
}
pub unsafe fn l_elabTestExtern___lam__0(
    mut v___x_600_: *mut LeanObject,
    mut v___x_601_: *mut LeanObject,
    mut v___x_602_: u8,
    mut v___y_603_: *mut LeanObject,
    mut v___y_604_: *mut LeanObject,
    mut v___y_605_: *mut LeanObject,
    mut v___y_606_: *mut LeanObject,
    mut v___y_607_: *mut LeanObject,
    mut v___y_608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: u8 = 0;
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_631_: u8 = 0;
    let mut v___x_632_: u8 = 0;
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_647_: u8 = 0;
    let mut v_a_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_651_: u8 = 0;
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_655_: u8 = 0;
    let mut v_a_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_659_: u8 = 0;
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_663_: u8 = 0;
    let mut v_a_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_667_: u8 = 0;
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_671_: u8 = 0;
    let mut v_a_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_675_: u8 = 0;
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_679_: u8 = 0;
    let mut v___y_681_: u8 = 0;
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: u8 = 0;
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_696_: u8 = 0;
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_610_ = l_Lean_Elab_Term_elabTermAndSynthesize(
                    v___x_600_, v___x_601_, v___y_603_, v___y_604_, v___y_605_, v___y_606_,
                    v___y_607_, v___y_608_,
                );
                if lean_obj_tag(v___x_610_) == 0 {
                    v_a_611_ = lean_ctor_get(v___x_610_, 0);
                    lean_inc(v_a_611_);
                    lean_dec_ref_known(v___x_610_, 1);
                    v___x_612_ = l_Lean_Expr_getAppFn(v_a_611_);
                    if lean_obj_tag(v___x_612_) == 4 {
                        v_declName_613_ = lean_ctor_get(v___x_612_, 0);
                        lean_inc_n(v_declName_613_, 2);
                        lean_dec_ref_known(v___x_612_, 2);
                        v___x_614_ = lean_st_ref_get(v___y_608_);
                        v_env_688_ = lean_ctor_get(v___x_614_, 0);
                        lean_inc_ref_n(v_env_688_, 2);
                        lean_dec(v___x_614_);
                        v___x_689_ = l_Lean_isExtern(v_env_688_, v_declName_613_);
                        if v___x_689_ == 0 {
                            lean_inc(v_declName_613_);
                            v___x_690_ =
                                l_Lean_Compiler_getImplementedBy_x3f(v_env_688_, v_declName_613_);
                            if lean_obj_tag(v___x_690_) == 0 {
                                v___y_681_ = v___x_689_;
                                state = 12;
                                continue;
                            } else {
                                lean_dec_ref_known(v___x_690_, 1);
                                v___y_681_ = v___x_602_;
                                state = 12;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_env_688_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_612_);
                        lean_dec(v_a_611_);
                        v___x_691_ = lean_obj_once(
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
                    v_a_693_ = lean_ctor_get(v___x_610_, 0);
                    v_isSharedCheck_700_ = (!lean_is_exclusive(v___x_610_)) as u8;
                    if v_isSharedCheck_700_ == 0 {
                        v___x_695_ = v___x_610_;
                        v_isShared_696_ = v_isSharedCheck_700_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_693_);
                        lean_dec(v___x_610_);
                        v___x_695_ = lean_box(0);
                        v_isShared_696_ = v_isSharedCheck_700_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_a_611_);
                v___x_616_ = l_Lean_Meta_unfold(
                    v_a_611_,
                    v_declName_613_,
                    v___y_605_,
                    v___y_606_,
                    v___y_607_,
                    v___y_608_,
                );
                if lean_obj_tag(v___x_616_) == 0 {
                    v_a_617_ = lean_ctor_get(v___x_616_, 0);
                    lean_inc(v_a_617_);
                    lean_dec_ref_known(v___x_616_, 1);
                    v_expr_618_ = lean_ctor_get(v_a_617_, 0);
                    lean_inc_ref_n(v_expr_618_, 2);
                    lean_dec(v_a_617_);
                    lean_inc(v_a_611_);
                    v___x_619_ = l_Lean_Meta_mkEq(
                        v_a_611_,
                        v_expr_618_,
                        v___y_605_,
                        v___y_606_,
                        v___y_607_,
                        v___y_608_,
                    );
                    if lean_obj_tag(v___x_619_) == 0 {
                        v_a_620_ = lean_ctor_get(v___x_619_, 0);
                        lean_inc(v_a_620_);
                        lean_dec_ref_known(v___x_619_, 1);
                        v___x_621_ = l_Lean_Meta_mkDecide(
                            v_a_620_, v___y_605_, v___y_606_, v___y_607_, v___y_608_,
                        );
                        if lean_obj_tag(v___x_621_) == 0 {
                            v_a_622_ = lean_ctor_get(v___x_621_, 0);
                            lean_inc(v_a_622_);
                            lean_dec_ref_known(v___x_621_, 1);
                            v___x_623_ = lean_obj_once(
                                core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__3),
                                core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__3_once),
                                _init_l_elabTestExtern___lam__0___closed__3,
                            );
                            v___x_624_ = l_Lean_Expr_app___override(v___x_623_, v_a_622_);
                            v___x_625_ = lean_obj_once(
                                core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__6),
                                core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__6_once),
                                _init_l_elabTestExtern___lam__0___closed__6,
                            );
                            v___x_626_ = 1;
                            v___x_627_ = l_Lean_Meta_evalExpr___redArg(
                                v___x_625_, v___x_624_, v___x_626_, v___x_602_, v___y_605_,
                                v___y_606_, v___y_607_, v___y_608_,
                            );
                            if lean_obj_tag(v___x_627_) == 0 {
                                v_a_628_ = lean_ctor_get(v___x_627_, 0);
                                v_isSharedCheck_647_ = (!lean_is_exclusive(v___x_627_)) as u8;
                                if v_isSharedCheck_647_ == 0 {
                                    v___x_630_ = v___x_627_;
                                    v_isShared_631_ = v_isSharedCheck_647_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_628_);
                                    lean_dec(v___x_627_);
                                    v___x_630_ = lean_box(0);
                                    v_isShared_631_ = v_isSharedCheck_647_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_expr_618_);
                                lean_dec(v_a_611_);
                                v_a_648_ = lean_ctor_get(v___x_627_, 0);
                                v_isSharedCheck_655_ = (!lean_is_exclusive(v___x_627_)) as u8;
                                if v_isSharedCheck_655_ == 0 {
                                    v___x_650_ = v___x_627_;
                                    v_isShared_651_ = v_isSharedCheck_655_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_648_);
                                    lean_dec(v___x_627_);
                                    v___x_650_ = lean_box(0);
                                    v_isShared_651_ = v_isSharedCheck_655_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_expr_618_);
                            lean_dec(v_a_611_);
                            v_a_656_ = lean_ctor_get(v___x_621_, 0);
                            v_isSharedCheck_663_ = (!lean_is_exclusive(v___x_621_)) as u8;
                            if v_isSharedCheck_663_ == 0 {
                                v___x_658_ = v___x_621_;
                                v_isShared_659_ = v_isSharedCheck_663_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_656_);
                                lean_dec(v___x_621_);
                                v___x_658_ = lean_box(0);
                                v_isShared_659_ = v_isSharedCheck_663_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_expr_618_);
                        lean_dec(v_a_611_);
                        v_a_664_ = lean_ctor_get(v___x_619_, 0);
                        v_isSharedCheck_671_ = (!lean_is_exclusive(v___x_619_)) as u8;
                        if v_isSharedCheck_671_ == 0 {
                            v___x_666_ = v___x_619_;
                            v_isShared_667_ = v_isSharedCheck_671_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_664_);
                            lean_dec(v___x_619_);
                            v___x_666_ = lean_box(0);
                            v_isShared_667_ = v_isSharedCheck_671_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_611_);
                    v_a_672_ = lean_ctor_get(v___x_616_, 0);
                    v_isSharedCheck_679_ = (!lean_is_exclusive(v___x_616_)) as u8;
                    if v_isSharedCheck_679_ == 0 {
                        v___x_674_ = v___x_616_;
                        v_isShared_675_ = v_isSharedCheck_679_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_672_);
                        lean_dec(v___x_616_);
                        v___x_674_ = lean_box(0);
                        v_isShared_675_ = v_isSharedCheck_679_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_632_ = (lean_unbox(v_a_628_) as u8);
                lean_dec(v_a_628_);
                if v___x_632_ == 0 {
                    lean_del_object(v___x_630_);
                    v___x_633_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__9),
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__9_once),
                        _init_l_elabTestExtern___lam__0___closed__9,
                    );
                    v___x_634_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__11),
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__11_once),
                        _init_l_elabTestExtern___lam__0___closed__11,
                    );
                    v___x_635_ = l_Lean_MessageData_ofExpr(v_a_611_);
                    v___x_636_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_636_, 0, v___x_634_);
                    lean_ctor_set(v___x_636_, 1, v___x_635_);
                    v___x_637_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__13),
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__13_once),
                        _init_l_elabTestExtern___lam__0___closed__13,
                    );
                    v___x_638_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_638_, 0, v___x_636_);
                    lean_ctor_set(v___x_638_, 1, v___x_637_);
                    v___x_639_ = l_Lean_MessageData_ofExpr(v_expr_618_);
                    v___x_640_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_640_, 0, v___x_638_);
                    lean_ctor_set(v___x_640_, 1, v___x_639_);
                    v___x_641_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_641_, 0, v___x_633_);
                    lean_ctor_set(v___x_641_, 1, v___x_640_);
                    v___x_642_ = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(
                        v___x_641_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_,
                        v___y_608_,
                    );
                    return v___x_642_;
                } else {
                    lean_dec_ref(v_expr_618_);
                    lean_dec(v_a_611_);
                    v___x_643_ = lean_box(0);
                    if v_isShared_631_ == 0 {
                        lean_ctor_set(v___x_630_, 0, v___x_643_);
                        v___x_645_ = v___x_630_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
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
                    v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
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
                    v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
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
                    v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
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
                    v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
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
                    lean_dec(v_a_611_);
                    v___x_682_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__15),
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__15_once),
                        _init_l_elabTestExtern___lam__0___closed__15,
                    );
                    v___x_683_ = l_Lean_MessageData_ofName(v_declName_613_);
                    v___x_684_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_684_, 0, v___x_682_);
                    lean_ctor_set(v___x_684_, 1, v___x_683_);
                    v___x_685_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__17),
                        core::ptr::addr_of_mut!(l_elabTestExtern___lam__0___closed__17_once),
                        _init_l_elabTestExtern___lam__0___closed__17,
                    );
                    v___x_686_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_686_, 0, v___x_684_);
                    lean_ctor_set(v___x_686_, 1, v___x_685_);
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
                    v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
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
    mut v___x_701_: *mut LeanObject,
    mut v___x_702_: *mut LeanObject,
    mut v___x_703_: *mut LeanObject,
    mut v___y_704_: *mut LeanObject,
    mut v___y_705_: *mut LeanObject,
    mut v___y_706_: *mut LeanObject,
    mut v___y_707_: *mut LeanObject,
    mut v___y_708_: *mut LeanObject,
    mut v___y_709_: *mut LeanObject,
    mut v___y_710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5035__boxed_711_: u8 = 0;
    let mut v_res_712_: *mut LeanObject = core::ptr::null_mut();
    v___x_5035__boxed_711_ = (lean_unbox(v___x_703_) as u8);
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
    lean_dec(v___y_709_);
    lean_dec_ref(v___y_708_);
    lean_dec(v___y_707_);
    lean_dec_ref(v___y_706_);
    lean_dec(v___y_705_);
    lean_dec_ref(v___y_704_);
    return v_res_712_;
}
pub unsafe fn l_elabTestExtern(
    mut v_x_713_: *mut LeanObject,
    mut v_a_714_: *mut LeanObject,
    mut v_a_715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: u8 = 0;
    v___x_717_ = l_testExternCmd___closed__1;
    lean_inc(v_x_713_);
    v___x_718_ = l_Lean_Syntax_isOfKind(v_x_713_, v___x_717_);
    if v___x_718_ == 0 {
        let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_713_);
        v___x_719_ = l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg();
        return v___x_719_;
    } else {
        let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_724_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
        v___x_720_ = lean_unsigned_to_nat(1);
        v___x_721_ = l_Lean_Syntax_getArg(v_x_713_, v___x_720_);
        lean_dec(v_x_713_);
        v___x_722_ = lean_box(0);
        v___x_723_ = lean_box((v___x_718_) as usize);
        v___f_724_ = lean_alloc_closure(
            l_elabTestExtern___lam__0___boxed as *mut core::ffi::c_void,
            10,
            3,
        );
        lean_closure_set(v___f_724_, 0, v___x_721_);
        lean_closure_set(v___f_724_, 1, v___x_722_);
        lean_closure_set(v___f_724_, 2, v___x_723_);
        v___x_725_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_724_, v_a_714_, v_a_715_);
        return v___x_725_;
    }
}
pub unsafe fn l_elabTestExtern___boxed(
    mut v_x_726_: *mut LeanObject,
    mut v_a_727_: *mut LeanObject,
    mut v_a_728_: *mut LeanObject,
    mut v_a_729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_730_: *mut LeanObject = core::ptr::null_mut();
    v_res_730_ = l_elabTestExtern(v_x_726_, v_a_727_, v_a_728_);
    lean_dec(v_a_728_);
    lean_dec_ref(v_a_727_);
    return v_res_730_;
}
pub unsafe fn l_Lean_throwError___at___00elabTestExtern_spec__1(
    mut v_00_u03b1_731_: *mut LeanObject,
    mut v_msg_732_: *mut LeanObject,
    mut v___y_733_: *mut LeanObject,
    mut v___y_734_: *mut LeanObject,
    mut v___y_735_: *mut LeanObject,
    mut v___y_736_: *mut LeanObject,
    mut v___y_737_: *mut LeanObject,
    mut v___y_738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    v___x_740_ = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(
        v_msg_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_,
    );
    return v___x_740_;
}
pub unsafe fn l_Lean_throwError___at___00elabTestExtern_spec__1___boxed(
    mut v_00_u03b1_741_: *mut LeanObject,
    mut v_msg_742_: *mut LeanObject,
    mut v___y_743_: *mut LeanObject,
    mut v___y_744_: *mut LeanObject,
    mut v___y_745_: *mut LeanObject,
    mut v___y_746_: *mut LeanObject,
    mut v___y_747_: *mut LeanObject,
    mut v___y_748_: *mut LeanObject,
    mut v___y_749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_750_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_748_);
    lean_dec_ref(v___y_747_);
    lean_dec(v___y_746_);
    lean_dec_ref(v___y_745_);
    lean_dec(v___y_744_);
    lean_dec_ref(v___y_743_);
    return v_res_750_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2(
    mut v_msgData_751_: *mut LeanObject,
    mut v_macroStack_752_: *mut LeanObject,
    mut v___y_753_: *mut LeanObject,
    mut v___y_754_: *mut LeanObject,
    mut v___y_755_: *mut LeanObject,
    mut v___y_756_: *mut LeanObject,
    mut v___y_757_: *mut LeanObject,
    mut v___y_758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    v___x_760_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(v_msgData_751_, v_macroStack_752_, v___y_757_);
    return v___x_760_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___boxed(
    mut v_msgData_761_: *mut LeanObject,
    mut v_macroStack_762_: *mut LeanObject,
    mut v___y_763_: *mut LeanObject,
    mut v___y_764_: *mut LeanObject,
    mut v___y_765_: *mut LeanObject,
    mut v___y_766_: *mut LeanObject,
    mut v___y_767_: *mut LeanObject,
    mut v___y_768_: *mut LeanObject,
    mut v___y_769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_770_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_768_);
    lean_dec_ref(v___y_767_);
    lean_dec(v___y_766_);
    lean_dec_ref(v___y_765_);
    lean_dec(v___y_764_);
    lean_dec_ref(v___y_763_);
    return v_res_770_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_TestExtern(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Notation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Exception(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_TestExtern(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Unfold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Eval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_ImplementedByAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_ExternAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_TestExtern(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Unfold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Eval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_ImplementedByAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Notation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Exception(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_ExternAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_TestExtern(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Util_TestExtern(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Util_TestExtern(builtin);
}
