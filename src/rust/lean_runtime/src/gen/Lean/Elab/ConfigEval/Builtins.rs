// Lean compiler output
// Module: Lean.Elab.ConfigEval.Builtins
// Imports: Lean.Elab.ConfigEval.Commands Lean.Elab.ConfigEval.DeriveEvalConfigItem Lean.Linter.MissingDocs
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_isNone, l_Lean_TSyntax_getId, l_Lean_mkCIdent, l_Lean_mkHole, l_Lean_mkIdentFrom,
    lean_mk_syntax_ident,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Macro_throwErrorAt___redArg,
    l_Lean_Macro_throwUnsupported___redArg, l_Lean_Name_append, l_Lean_Name_mkStr1,
    l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_Syntax_node7,
    l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27, lean_erase_macro_scopes,
};
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_commandElabAttribute, l_Lean_Elab_Command_liftTermElabM___redArg,
};
use crate::r#gen::Lean::Elab::ConfigEval::Commands::{
    initialize_Lean_Elab_ConfigEval_Commands, runtime_initialize_Lean_Elab_ConfigEval_Commands,
};
use crate::r#gen::Lean::Elab::ConfigEval::DeriveEvalConfigItem::{
    initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem, l_Lean_Elab_ConfigEval_defEvalConfigItem,
    runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem,
};
use crate::r#gen::Lean::Elab::ConfigEval::DeriveEvalExpr::{
    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval, l_Lean_Elab_ConfigEval_ensureEvalExpr,
};
use crate::r#gen::Lean::Elab::ConfigEval::DeriveEvalTerm::l_Lean_Elab_ConfigEval_ensureEvalTerm;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::SyntheticMVars::l_Lean_Elab_Term_elabTermAndSynthesize___boxed;
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_withoutErrToSorryImp___redArg;
use crate::r#gen::Lean::Elab::Util::l_Lean_Elab_macroAttribute;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Linter::MissingDocs::{
    initialize_Lean_Linter_MissingDocs, l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed,
    l_Lean_Linter_MissingDocs_addBuiltinHandler, l_Lean_Linter_MissingDocs_mkSimpleHandler,
    runtime_initialize_Lean_Linter_MissingDocs,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_3, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value: LeanStringObject<
    5,
> = LeanStringObject {
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
static mut l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__3_value: LeanStringObject<
    9,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0],
};
static mut l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__3_value)
                as *mut LeanObject,
            7983999284776576032 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [69, 108, 97, 98, 0],
};
static mut l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value: LeanStringObject<
    11,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [67, 111, 110, 102, 105, 103, 69, 118, 97, 108, 0],
};
static mut l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__7_value: LeanStringObject<
    23,
> = LeanStringObject {
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
        101, 110, 115, 117, 114, 101, 69, 118, 97, 108, 84, 101, 114, 109, 73, 110, 115, 116, 97,
        110, 99, 101, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__7_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value)
            as *mut LeanObject,
        11510100434945111860 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value)
            as *mut LeanObject,
        11364794674035624021 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__7_value)
                as *mut LeanObject,
            15782017376166539708 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__0_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 108, 97, 98, 69, 110, 115, 117, 114, 101, 69, 118, 97, 108, 84, 101, 114, 109, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__0_value) as *mut LeanObject,3774683980042126024 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__0_value: LeanStringObject<
    23,
> = LeanStringObject {
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
        101, 110, 115, 117, 114, 101, 69, 118, 97, 108, 69, 120, 112, 114, 73, 110, 115, 116, 97,
        110, 99, 101, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value)
            as *mut LeanObject,
        11510100434945111860 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value)
            as *mut LeanObject,
        11364794674035624021 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__0_value)
                as *mut LeanObject,
            242734749837126826 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__0_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 108, 97, 98, 69, 110, 115, 117, 114, 101, 69, 118, 97, 108, 69, 120, 112, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__0_value) as *mut LeanObject,6638561281264851003 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__0_value:
    LeanStringObject<28> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        101, 110, 115, 117, 114, 101, 69, 118, 97, 108, 84, 101, 114, 109, 69, 120, 112, 114, 73,
        110, 115, 116, 97, 110, 99, 101, 115, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value)
            as *mut LeanObject,
        11510100434945111860 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value)
            as *mut LeanObject,
        11364794674035624021 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__0_value
        ) as *mut LeanObject,
        13281077697210892810 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__2_value:
    LeanStringObject<26> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        101, 110, 115, 117, 114, 101, 95, 101, 118, 97, 108, 95, 116, 101, 114, 109, 95, 105, 110,
        115, 116, 97, 110, 99, 101, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__3_value:
    LeanStringObject<26> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        101, 110, 115, 117, 114, 101, 95, 101, 118, 97, 108, 95, 101, 120, 112, 114, 95, 105, 110,
        115, 116, 97, 110, 99, 101, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__4_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__4_value
        ) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__0_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [101, 120, 112, 97, 110, 100, 69, 110, 115, 117, 114, 101, 69, 118, 97, 108, 84, 101, 114, 109, 69, 120, 112, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__0_value) as *mut LeanObject,3184057547004315090 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__0_value: LeanStringObject<
    24,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        100, 101, 114, 105, 118, 101, 69, 118, 97, 108, 69, 120, 112, 114, 85, 115, 105, 110, 103,
        77, 101, 116, 97, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value)
            as *mut LeanObject,
        11510100434945111860 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value)
            as *mut LeanObject,
        11364794674035624021 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__0_value
            ) as *mut LeanObject,
            5814452243651064866 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__0_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [101, 108, 97, 98, 68, 101, 114, 105, 118, 101, 69, 118, 97, 108, 69, 120, 112, 114, 85, 115, 105, 110, 103, 77, 101, 116, 97, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__0_value) as *mut LeanObject,11327550639422987008 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [99, 111, 110, 102, 105, 103, 69, 110, 116, 114, 121, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__0_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__0_value) as *mut LeanObject,9645242084791194988 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__2_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [99, 111, 110, 102, 105, 103, 69, 110, 116, 114, 121, 79, 109, 105, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__2_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__2_value) as *mut LeanObject,5452356098271972433 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__4_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [99, 111, 110, 102, 105, 103, 69, 110, 116, 114, 121, 72, 97, 110, 100, 108, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__4_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__4_value) as *mut LeanObject,3045336378954125646 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__6_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [99, 111, 110, 102, 105, 103, 69, 110, 116, 114, 121, 72, 97, 110, 100, 108, 101, 114, 75, 101, 121, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__6_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__6_value) as *mut LeanObject,15143275316288011801 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__8_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [99, 111, 110, 102, 105, 103, 69, 110, 116, 114, 121, 72, 97, 110, 100, 108, 101, 114, 75, 101, 121, 80, 114, 101, 102, 105, 120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__8_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__8_value) as *mut LeanObject,5170656903224962469 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__10_value: LeanStringObject<30> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [99, 111, 110, 102, 105, 103, 69, 110, 116, 114, 121, 72, 97, 110, 100, 108, 101, 114, 75, 101, 121, 87, 105, 108, 100, 99, 97, 114, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__10_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__10_value) as *mut LeanObject,6766706904888361041 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__12_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__12_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__12_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__1_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__2_value: LeanStringObject<14> =
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
            99, 111, 110, 102, 105, 103, 69, 110, 116, 114, 105, 101, 115, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__2_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__2_value)
                as *mut LeanObject,
            2209778251590303698 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__0_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            100, 101, 102, 69, 118, 97, 108, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 67,
            109, 100, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__0_value)
                as *mut LeanObject,
            15774958811162948289 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [67, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__3_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
    };
static mut l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__3_value)
                as *mut LeanObject,
            9063780239635860524 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [101, 108, 97, 98, 68, 101, 102, 69, 118, 97, 108, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 67, 109, 100, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__0_value) as *mut LeanObject,9194023677756017578 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [99, 111, 110, 102, 105, 103, 32, 101, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value) as *mut LeanObject,17201320286889277233 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__2_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 109, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__2_value) as *mut LeanObject,6962862263136859431 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__4_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [115, 116, 114, 105, 99, 116, 73, 109, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__4_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__4_value) as *mut LeanObject,13687021865847480189 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__6_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 115, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__6_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__6_value) as *mut LeanObject,16363371701764479942 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 98, 105, 110, 100, 101, 114, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__1_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 101, 102, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__4_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__5_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__6_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [76, 101, 97, 110, 46, 83, 121, 110, 116, 97, 120, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__6_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__8_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 121, 110, 116, 97, 120, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__8_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__8_value) as *mut LeanObject,5337926038336999469 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__10_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__11_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [98, 105, 110, 100, 101, 114, 68, 101, 102, 97, 117, 108, 116, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__11_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__11_value) as *mut LeanObject,2302148402677708579 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__13_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 104, 111, 105, 99, 101, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__13_value) as *mut LeanObject,11985596712582660667 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__15_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 101, 114, 109, 123, 125, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__15_value) as *mut LeanObject,5126085667538439468 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__17_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [123, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__18_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [125, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__19_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__19_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__19_value) as *mut LeanObject,2026475204632980274 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__21_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 115, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__21_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__21_value) as *mut LeanObject,5018042693327868416 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__23_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [111, 112, 116, 69, 108, 108, 105, 112, 115, 105, 115, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__23_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__23_value) as *mut LeanObject,11580369617518985485 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__27_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__27: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__27_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__28_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__27_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__28: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__28_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__29_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__29: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__29_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__29_value) as *mut LeanObject,4498178684837002829 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__32_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [100, 111, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__32: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__32_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__32_value) as *mut LeanObject,5817315006727311029 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 111, 83, 101, 113, 73, 110, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34_value) as *mut LeanObject,3326968124746134365 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 83, 101, 113, 73, 116, 101, 109, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36_value) as *mut LeanObject,940684074193935882 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 111, 76, 101, 116, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38_value) as *mut LeanObject,14774476768116910908 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 101, 116, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__41_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__41: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__41_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__41_value) as *mut LeanObject,17404204824591055365 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [108, 101, 116, 68, 101, 99, 108, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43_value) as *mut LeanObject,8036185514257755965 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 73, 100, 68, 101, 99, 108, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45_value) as *mut LeanObject,17116161260408496210 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 101, 116, 73, 100, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47_value) as *mut LeanObject,13708106407786339395 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49_value) as *mut LeanObject,13290931718435096973 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [64, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__52_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [69, 118, 97, 108, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 46, 100, 101, 102, 97, 117, 108, 116, 79, 110, 69, 114, 114, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__52: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__52_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__53_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__53: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [100, 101, 102, 97, 117, 108, 116, 79, 110, 69, 114, 114, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__55_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 102, 103, 84, 121, 112, 101, 63, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__55: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__55_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__55_value) as *mut LeanObject,7348416525232862522 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__58_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 107, 67, 111, 110, 115, 116, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__58: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__58_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__58_value) as *mut LeanObject,17968679829667083557 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__61_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__61_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__61_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__58_value) as *mut LeanObject,8577186464599713308 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__61: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__61_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__62_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [100, 111, 117, 98, 108, 101, 81, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__62: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__62_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__62_value) as *mut LeanObject,11323065835382012354 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__65_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 111, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__65: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__65_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__65_value) as *mut LeanObject,5573444893818005634 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__68_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__68: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__68_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67_value) as *mut LeanObject,7625897890118033792 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__68_value) as *mut LeanObject,8715860392475343861 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__71_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__71: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__71_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__72_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [108, 111, 103, 69, 120, 99, 101, 112, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__72: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__72_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__73_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__72_value) as *mut LeanObject,16773238528744707702 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__73: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__73_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [99, 102, 103, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__76_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75_value) as *mut LeanObject,1529402619103148481 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__76: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__76_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__77_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__77: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [105, 110, 105, 116, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__79_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78_value) as *mut LeanObject,15209775132330820936 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__79: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__79_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__80_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__80: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [69, 118, 97, 108, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 46, 115, 101, 116, 67, 111, 110, 102, 105, 103, 39, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__84_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__84: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [69, 118, 97, 108, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__86_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 101, 116, 67, 111, 110, 102, 105, 103, 39, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__86: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__86_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__87_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85_value) as *mut LeanObject,13650387811874371350 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__87_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__87_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__86_value) as *mut LeanObject,3429309849189070656 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__87: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__87_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85_value) as *mut LeanObject,12464536414584198160 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__86_value) as *mut LeanObject,9040428619303664574 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__90_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__90: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__90_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__91_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 118, 97, 108, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__91: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__91_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__91_value) as *mut LeanObject,9571650749804680972 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__94_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [110, 97, 109, 101, 100, 65, 114, 103, 117, 109, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__94: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__94_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__94_value) as *mut LeanObject,13594530736035158498 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 110, 69, 114, 114, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97_value) as *mut LeanObject,3731565283734990564 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__100_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__100: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__100_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__101_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__101: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__101_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 118, 97, 108, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__104_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103_value) as *mut LeanObject,15572110113139446196 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__104: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__104_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105_value) as *mut LeanObject,10324751846086867157 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 111, 99, 97, 108, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value) as *mut LeanObject,312453245906544776 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [100, 101, 102, 95, 101, 118, 97, 108, 95, 99, 111, 110, 102, 105, 103, 95, 105, 116, 101, 109, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 111, 114, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__0_value: LeanStringObject<
    22,
> = LeanStringObject {
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
        100, 101, 99, 108, 97, 114, 101, 67, 111, 114, 101, 67, 111, 110, 102, 105, 103, 69, 108,
        97, 98, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__0_value)
                as *mut LeanObject,
            10628568370346925746 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__2_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__4_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [67, 111, 114, 101, 0],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__5_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [67, 111, 114, 101, 77, 0],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__5_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__4_value)
                as *mut LeanObject,
            14660883194614152898 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__5_value)
                as *mut LeanObject,
            10194387235483120243 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__8_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__8_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__9_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__8_value)
                as *mut LeanObject,
            15761733860085307253 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__9_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [101, 108, 97, 98, 68, 101, 99, 108, 97, 114, 101, 67, 111, 114, 101, 67, 111, 110, 102, 105, 103, 69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__0_value) as *mut LeanObject,13630717974556420429 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__0_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [116, 101, 114, 109, 95, 38, 38, 95, 0],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__0_value
        ) as *mut LeanObject,
        1601449343645893382 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__2_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [38, 38, 0],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__3_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [112, 114, 111, 106, 0],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__4_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [112, 97, 114, 101, 110, 0],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__5_value:
    LeanStringObject<15> = LeanStringObject {
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
        104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__6_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__7_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__6_value
        ) as *mut LeanObject,
        9871775667037945883 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__8_value:
    LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__10_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [77, 101, 116, 97, 0],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__10: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__10_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__11_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [110, 101, 115, 116, 101, 100, 65, 99, 116, 105, 111, 110, 0],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__11: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__11_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__12_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 134, 144, 0],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__12: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__12_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__13_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [114, 101, 97, 100, 0],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__13: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__13_value
)
    as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__15_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__13_value
        ) as *mut LeanObject,
        16705565168081637566 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__15: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__15_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__16_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [77, 111, 110, 97, 100, 82, 101, 97, 100, 101, 114, 0],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__16: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__16_value
)
    as *mut LeanObject;
static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__17_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__16_value
        ) as *mut LeanObject,
        12145732180193422603 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__17_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__17_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__13_value
        ) as *mut LeanObject,
        5126750173635103278 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__17: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__17_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__18_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__17_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__18: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__18_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__19_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__18_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__19: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__19_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__20_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [46, 0],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__20: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__20_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__21_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [101, 114, 114, 84, 111, 83, 111, 114, 114, 121, 0],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__21: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__21_value
)
    as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__23_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__21_value
        ) as *mut LeanObject,
        7867977222459139751 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__23: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__23_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__0_value: LeanStringObject<
    22,
> = LeanStringObject {
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
        100, 101, 99, 108, 97, 114, 101, 84, 101, 114, 109, 67, 111, 110, 102, 105, 103, 69, 108,
        97, 98, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__0_value)
                as *mut LeanObject,
            8913075533519350929 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__2_value: LeanClosureObject<
    5,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 5) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 5,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__3_value: LeanStringObject<
    10,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [84, 101, 114, 109, 69, 108, 97, 98, 77, 0],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value)
                as *mut LeanObject,
            7892421401833366012 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__3_value)
                as *mut LeanObject,
            11926526118880761173 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__6_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__6_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__7_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__6_value)
                as *mut LeanObject,
            9255189395584251158 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [101, 108, 97, 98, 68, 101, 99, 108, 97, 114, 101, 84, 101, 114, 109, 67, 111, 110, 102, 105, 103, 69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__0_value) as *mut LeanObject,8296220008007696692 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__0_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [114, 101, 99, 111, 118, 101, 114, 0],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__2_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__0_value
        ) as *mut LeanObject,
        11451883528579887567 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__0_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            100, 101, 99, 108, 97, 114, 101, 84, 97, 99, 116, 105, 99, 67, 111, 110, 102, 105, 103,
            0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__0_value)
                as *mut LeanObject,
            14052075957971063135 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__2_value: LeanClosureObject<5> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 5) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 5,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__3_value: LeanStringObject<7> =
    LeanStringObject {
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
static mut l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__4_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [84, 97, 99, 116, 105, 99, 77, 0],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__4_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__3_value)
                as *mut LeanObject,
            12733524109236233889 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__4_value)
                as *mut LeanObject,
            15473897845548334991 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [101, 108, 97, 98, 68, 101, 99, 108, 97, 114, 101, 84, 97, 99, 116, 105, 99, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__0_value) as *mut LeanObject,3375831771971807160 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__0_value:
    LeanStringObject<22> = LeanStringObject {
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
        67, 111, 109, 109, 97, 110, 100, 46, 108, 105, 102, 116, 84, 101, 114, 109, 69, 108, 97,
        98, 77, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__2_value:
    LeanStringObject<14> = LeanStringObject {
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
        108, 105, 102, 116, 84, 101, 114, 109, 69, 108, 97, 98, 77, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__0_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            100, 101, 99, 108, 97, 114, 101, 67, 111, 109, 109, 97, 110, 100, 67, 111, 110, 102,
            105, 103, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__0_value)
                as *mut LeanObject,
            7457840639043711308 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__2_value: LeanClosureObject<5> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 5) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 5,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__3_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [67, 111, 109, 109, 97, 110, 100, 69, 108, 97, 98, 77, 0],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2_value)
                as *mut LeanObject,
            16981400742628996529 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__3_value)
                as *mut LeanObject,
            15711078226730137352 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [101, 108, 97, 98, 68, 101, 99, 108, 97, 114, 101, 67, 111, 109, 109, 97, 110, 100, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__0_value) as *mut LeanObject,3930665142417705911 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    v___x_2711_ = lean_box(0);
    v___x_2712_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_2713_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2713_, 0, v___x_2712_);
    lean_ctor_set(v___x_2713_, 1, v___x_2711_);
    return v___x_2713_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    v___x_2715_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___closed__0);
    v___x_2716_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2716_, 0, v___x_2715_);
    return v___x_2716_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___boxed(
    mut v___y_2717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2718_: *mut LeanObject = core::ptr::null_mut();
    v_res_2718_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
    return v_res_2718_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0(
    mut v_00_u03b1_2719_: *mut LeanObject,
    mut v___y_2720_: *mut LeanObject,
    mut v___y_2721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    v___x_2723_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
    return v___x_2723_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___boxed(
    mut v_00_u03b1_2724_: *mut LeanObject,
    mut v___y_2725_: *mut LeanObject,
    mut v___y_2726_: *mut LeanObject,
    mut v___y_2727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2728_: *mut LeanObject = core::ptr::null_mut();
    v_res_2728_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0(v_00_u03b1_2724_, v___y_2725_, v___y_2726_);
    lean_dec(v___y_2726_);
    lean_dec_ref(v___y_2725_);
    return v_res_2728_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___redArg(
    mut v_a_2729_: *mut LeanObject,
    mut v___y_2730_: *mut LeanObject,
    mut v___y_2731_: *mut LeanObject,
    mut v___y_2732_: *mut LeanObject,
    mut v___y_2733_: *mut LeanObject,
    mut v___y_2734_: *mut LeanObject,
    mut v___y_2735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    v___x_2737_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v_a_2729_,
        v___y_2730_,
        v___y_2731_,
        v___y_2732_,
        v___y_2733_,
        v___y_2734_,
        v___y_2735_,
    );
    return v___x_2737_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___redArg___boxed(
    mut v_a_2738_: *mut LeanObject,
    mut v___y_2739_: *mut LeanObject,
    mut v___y_2740_: *mut LeanObject,
    mut v___y_2741_: *mut LeanObject,
    mut v___y_2742_: *mut LeanObject,
    mut v___y_2743_: *mut LeanObject,
    mut v___y_2744_: *mut LeanObject,
    mut v___y_2745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2746_: *mut LeanObject = core::ptr::null_mut();
    v_res_2746_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___redArg(v_a_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
    lean_dec(v___y_2744_);
    lean_dec_ref(v___y_2743_);
    lean_dec(v___y_2742_);
    lean_dec_ref(v___y_2741_);
    lean_dec(v___y_2740_);
    lean_dec_ref(v___y_2739_);
    return v_res_2746_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1(
    mut v_00_u03b1_2747_: *mut LeanObject,
    mut v_a_2748_: *mut LeanObject,
    mut v___y_2749_: *mut LeanObject,
    mut v___y_2750_: *mut LeanObject,
    mut v___y_2751_: *mut LeanObject,
    mut v___y_2752_: *mut LeanObject,
    mut v___y_2753_: *mut LeanObject,
    mut v___y_2754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    v___x_2756_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v_a_2748_,
        v___y_2749_,
        v___y_2750_,
        v___y_2751_,
        v___y_2752_,
        v___y_2753_,
        v___y_2754_,
    );
    return v___x_2756_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___boxed(
    mut v_00_u03b1_2757_: *mut LeanObject,
    mut v_a_2758_: *mut LeanObject,
    mut v___y_2759_: *mut LeanObject,
    mut v___y_2760_: *mut LeanObject,
    mut v___y_2761_: *mut LeanObject,
    mut v___y_2762_: *mut LeanObject,
    mut v___y_2763_: *mut LeanObject,
    mut v___y_2764_: *mut LeanObject,
    mut v___y_2765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2766_: *mut LeanObject = core::ptr::null_mut();
    v_res_2766_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1(v_00_u03b1_2757_, v_a_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
    lean_dec(v___y_2764_);
    lean_dec_ref(v___y_2763_);
    lean_dec(v___y_2762_);
    lean_dec_ref(v___y_2761_);
    lean_dec(v___y_2760_);
    lean_dec_ref(v___y_2759_);
    return v_res_2766_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance(
    mut v_x_2784_: *mut LeanObject,
    mut v_a_2785_: *mut LeanObject,
    mut v_a_2786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vis_x3f_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: u8 = 0;
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2810_: u8 = 0;
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2814_: u8 = 0;
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: u8 = 0;
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: u8 = 0;
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: u8 = 0;
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vis_x3f_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2815_ = l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8;
                lean_inc(v_x_2784_);
                v___x_2816_ = l_Lean_Syntax_isOfKind(v_x_2784_, v___x_2815_);
                if v___x_2816_ == 0 {
                    lean_dec(v_x_2784_);
                    v___x_2817_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                    return v___x_2817_;
                } else {
                    v___x_2818_ = lean_unsigned_to_nat(0);
                    v___x_2819_ = l_Lean_Syntax_getArg(v_x_2784_, v___x_2818_);
                    v___x_2820_ = l_Lean_Syntax_isNone(v___x_2819_);
                    if v___x_2820_ == 0 {
                        v___x_2821_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_2819_);
                        v___x_2822_ = l_Lean_Syntax_matchesNull(v___x_2819_, v___x_2821_);
                        if v___x_2822_ == 0 {
                            lean_dec(v___x_2819_);
                            lean_dec(v_x_2784_);
                            v___x_2823_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                            return v___x_2823_;
                        } else {
                            v_vis_x3f_2824_ = l_Lean_Syntax_getArg(v___x_2819_, v___x_2818_);
                            lean_dec(v___x_2819_);
                            v___x_2825_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2825_, 0, v_vis_x3f_2824_);
                            v_vis_x3f_2789_ = v___x_2825_;
                            v___y_2790_ = v_a_2785_;
                            v___y_2791_ = v_a_2786_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2819_);
                        v___x_2826_ = lean_box(0);
                        v_vis_x3f_2789_ = v___x_2826_;
                        v___y_2790_ = v_a_2785_;
                        v___y_2791_ = v_a_2786_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2792_ = lean_unsigned_to_nat(1);
                v_kind_2793_ = l_Lean_Syntax_getArg(v_x_2784_, v___x_2792_);
                v___x_2794_ = l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4;
                lean_inc(v_kind_2793_);
                v___x_2795_ = l_Lean_Syntax_isOfKind(v_kind_2793_, v___x_2794_);
                if v___x_2795_ == 0 {
                    lean_dec(v_kind_2793_);
                    lean_dec(v_vis_x3f_2789_);
                    lean_dec(v_x_2784_);
                    v___x_2796_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                    return v___x_2796_;
                } else {
                    v___x_2797_ = lean_unsigned_to_nat(3);
                    v___x_2798_ = l_Lean_Syntax_getArg(v_x_2784_, v___x_2797_);
                    v___x_2799_ = lean_box(0);
                    lean_inc(v___x_2798_);
                    v___x_2800_ = lean_alloc_closure(
                        l_Lean_Elab_Term_elabTermAndSynthesize___boxed as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    lean_closure_set(v___x_2800_, 0, v___x_2798_);
                    lean_closure_set(v___x_2800_, 1, v___x_2799_);
                    v___x_2801_ = lean_alloc_closure(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___boxed as *mut core::ffi::c_void, 9, 2);
                    lean_closure_set(v___x_2801_, 0, lean_box(0));
                    lean_closure_set(v___x_2801_, 1, v___x_2800_);
                    v___x_2802_ = l_Lean_Elab_Command_liftTermElabM___redArg(
                        v___x_2801_,
                        v___y_2790_,
                        v___y_2791_,
                    );
                    if lean_obj_tag(v___x_2802_) == 0 {
                        v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
                        lean_inc(v_a_2803_);
                        lean_dec_ref_known(v___x_2802_, 1);
                        v___x_2804_ = lean_unsigned_to_nat(2);
                        v_tk_2805_ = l_Lean_Syntax_getArg(v_x_2784_, v___x_2804_);
                        lean_dec(v_x_2784_);
                        v___x_2806_ = l_Lean_Elab_ConfigEval_ensureEvalTerm(
                            v_vis_x3f_2789_,
                            v_kind_2793_,
                            v_tk_2805_,
                            v___x_2798_,
                            v_a_2803_,
                            v___y_2790_,
                            v___y_2791_,
                        );
                        return v___x_2806_;
                    } else {
                        lean_dec(v___x_2798_);
                        lean_dec(v_kind_2793_);
                        lean_dec(v_vis_x3f_2789_);
                        lean_dec(v_x_2784_);
                        v_a_2807_ = lean_ctor_get(v___x_2802_, 0);
                        v_isSharedCheck_2814_ = (!lean_is_exclusive(v___x_2802_)) as u8;
                        if v_isSharedCheck_2814_ == 0 {
                            v___x_2809_ = v___x_2802_;
                            v_isShared_2810_ = v_isSharedCheck_2814_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2807_);
                            lean_dec(v___x_2802_);
                            v___x_2809_ = lean_box(0);
                            v_isShared_2810_ = v_isSharedCheck_2814_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2810_ == 0 {
                    v___x_2812_ = v___x_2809_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
                    v___x_2812_ = v_reuseFailAlloc_2813_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2812_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___boxed(
    mut v_x_2827_: *mut LeanObject,
    mut v_a_2828_: *mut LeanObject,
    mut v_a_2829_: *mut LeanObject,
    mut v_a_2830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2831_: *mut LeanObject = core::ptr::null_mut();
    v_res_2831_ =
        l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance(v_x_2827_, v_a_2828_, v_a_2829_);
    lean_dec(v_a_2829_);
    lean_dec_ref(v_a_2828_);
    return v_res_2831_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1()
-> *mut LeanObject {
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    v___x_2839_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_2840_ = l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8;
    v___x_2841_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1;
    v___x_2842_ = lean_alloc_closure(
        l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_2843_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2839_,
        v___x_2840_,
        v___x_2841_,
        v___x_2842_,
    );
    return v___x_2843_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___boxed(
    mut v_a_2844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2845_: *mut LeanObject = core::ptr::null_mut();
    v_res_2845_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1();
    return v_res_2845_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance(
    mut v_x_2852_: *mut LeanObject,
    mut v_a_2853_: *mut LeanObject,
    mut v_a_2854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vis_x3f_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: u8 = 0;
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2878_: u8 = 0;
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2882_: u8 = 0;
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: u8 = 0;
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: u8 = 0;
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: u8 = 0;
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vis_x3f_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2883_ = l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1;
                lean_inc(v_x_2852_);
                v___x_2884_ = l_Lean_Syntax_isOfKind(v_x_2852_, v___x_2883_);
                if v___x_2884_ == 0 {
                    lean_dec(v_x_2852_);
                    v___x_2885_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                    return v___x_2885_;
                } else {
                    v___x_2886_ = lean_unsigned_to_nat(0);
                    v___x_2887_ = l_Lean_Syntax_getArg(v_x_2852_, v___x_2886_);
                    v___x_2888_ = l_Lean_Syntax_isNone(v___x_2887_);
                    if v___x_2888_ == 0 {
                        v___x_2889_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_2887_);
                        v___x_2890_ = l_Lean_Syntax_matchesNull(v___x_2887_, v___x_2889_);
                        if v___x_2890_ == 0 {
                            lean_dec(v___x_2887_);
                            lean_dec(v_x_2852_);
                            v___x_2891_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                            return v___x_2891_;
                        } else {
                            v_vis_x3f_2892_ = l_Lean_Syntax_getArg(v___x_2887_, v___x_2886_);
                            lean_dec(v___x_2887_);
                            v___x_2893_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2893_, 0, v_vis_x3f_2892_);
                            v_vis_x3f_2857_ = v___x_2893_;
                            v___y_2858_ = v_a_2853_;
                            v___y_2859_ = v_a_2854_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2887_);
                        v___x_2894_ = lean_box(0);
                        v_vis_x3f_2857_ = v___x_2894_;
                        v___y_2858_ = v_a_2853_;
                        v___y_2859_ = v_a_2854_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2860_ = lean_unsigned_to_nat(1);
                v_kind_2861_ = l_Lean_Syntax_getArg(v_x_2852_, v___x_2860_);
                v___x_2862_ = l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4;
                lean_inc(v_kind_2861_);
                v___x_2863_ = l_Lean_Syntax_isOfKind(v_kind_2861_, v___x_2862_);
                if v___x_2863_ == 0 {
                    lean_dec(v_kind_2861_);
                    lean_dec(v_vis_x3f_2857_);
                    lean_dec(v_x_2852_);
                    v___x_2864_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                    return v___x_2864_;
                } else {
                    v___x_2865_ = lean_unsigned_to_nat(3);
                    v___x_2866_ = l_Lean_Syntax_getArg(v_x_2852_, v___x_2865_);
                    v___x_2867_ = lean_box(0);
                    lean_inc(v___x_2866_);
                    v___x_2868_ = lean_alloc_closure(
                        l_Lean_Elab_Term_elabTermAndSynthesize___boxed as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    lean_closure_set(v___x_2868_, 0, v___x_2866_);
                    lean_closure_set(v___x_2868_, 1, v___x_2867_);
                    v___x_2869_ = lean_alloc_closure(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___boxed as *mut core::ffi::c_void, 9, 2);
                    lean_closure_set(v___x_2869_, 0, lean_box(0));
                    lean_closure_set(v___x_2869_, 1, v___x_2868_);
                    v___x_2870_ = l_Lean_Elab_Command_liftTermElabM___redArg(
                        v___x_2869_,
                        v___y_2858_,
                        v___y_2859_,
                    );
                    if lean_obj_tag(v___x_2870_) == 0 {
                        v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
                        lean_inc(v_a_2871_);
                        lean_dec_ref_known(v___x_2870_, 1);
                        v___x_2872_ = lean_unsigned_to_nat(2);
                        v_tk_2873_ = l_Lean_Syntax_getArg(v_x_2852_, v___x_2872_);
                        lean_dec(v_x_2852_);
                        v___x_2874_ = l_Lean_Elab_ConfigEval_ensureEvalExpr(
                            v_vis_x3f_2857_,
                            v_kind_2861_,
                            v_tk_2873_,
                            v___x_2866_,
                            v_a_2871_,
                            v___y_2858_,
                            v___y_2859_,
                        );
                        return v___x_2874_;
                    } else {
                        lean_dec(v___x_2866_);
                        lean_dec(v_kind_2861_);
                        lean_dec(v_vis_x3f_2857_);
                        lean_dec(v_x_2852_);
                        v_a_2875_ = lean_ctor_get(v___x_2870_, 0);
                        v_isSharedCheck_2882_ = (!lean_is_exclusive(v___x_2870_)) as u8;
                        if v_isSharedCheck_2882_ == 0 {
                            v___x_2877_ = v___x_2870_;
                            v_isShared_2878_ = v_isSharedCheck_2882_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2875_);
                            lean_dec(v___x_2870_);
                            v___x_2877_ = lean_box(0);
                            v_isShared_2878_ = v_isSharedCheck_2882_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2878_ == 0 {
                    v___x_2880_ = v___x_2877_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
                    v___x_2880_ = v_reuseFailAlloc_2881_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2880_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___boxed(
    mut v_x_2895_: *mut LeanObject,
    mut v_a_2896_: *mut LeanObject,
    mut v_a_2897_: *mut LeanObject,
    mut v_a_2898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2899_: *mut LeanObject = core::ptr::null_mut();
    v_res_2899_ =
        l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance(v_x_2895_, v_a_2896_, v_a_2897_);
    lean_dec(v_a_2897_);
    lean_dec_ref(v_a_2896_);
    return v_res_2899_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1()
-> *mut LeanObject {
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    v___x_2907_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_2908_ = l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1;
    v___x_2909_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1;
    v___x_2910_ = lean_alloc_closure(
        l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_2911_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2907_,
        v___x_2908_,
        v___x_2909_,
        v___x_2910_,
    );
    return v___x_2911_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___boxed(
    mut v_a_2912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2913_: *mut LeanObject = core::ptr::null_mut();
    v_res_2913_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1();
    return v_res_2913_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6()
-> *mut LeanObject {
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    v___x_2925_ = l_Array_mkArray0(lean_box(0));
    return v___x_2925_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance(
    mut v_x_2928_: *mut LeanObject,
    mut v_a_2929_: *mut LeanObject,
    mut v_a_2930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: u8 = 0;
    let mut v___y_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vis_x3f_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: u8 = 0;
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: u8 = 0;
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: u8 = 0;
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: u8 = 0;
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vis_x3f_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2931_ = l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1;
                lean_inc(v_x_2928_);
                v___x_2932_ = l_Lean_Syntax_isOfKind(v_x_2928_, v___x_2931_);
                if v___x_2932_ == 0 {
                    lean_dec(v_x_2928_);
                    v___x_2977_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2930_);
                    return v___x_2977_;
                } else {
                    v___x_2978_ = lean_unsigned_to_nat(0);
                    v___x_2979_ = l_Lean_Syntax_getArg(v_x_2928_, v___x_2978_);
                    v___x_2980_ = l_Lean_Syntax_isNone(v___x_2979_);
                    if v___x_2980_ == 0 {
                        v___x_2981_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_2979_);
                        v___x_2982_ = l_Lean_Syntax_matchesNull(v___x_2979_, v___x_2981_);
                        if v___x_2982_ == 0 {
                            lean_dec(v___x_2979_);
                            lean_dec(v_x_2928_);
                            v___x_2983_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2930_);
                            return v___x_2983_;
                        } else {
                            v_vis_x3f_2984_ = l_Lean_Syntax_getArg(v___x_2979_, v___x_2978_);
                            lean_dec(v___x_2979_);
                            v___x_2985_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2985_, 0, v_vis_x3f_2984_);
                            v_vis_x3f_2956_ = v___x_2985_;
                            v___y_2957_ = v_a_2929_;
                            v___y_2958_ = v_a_2930_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2979_);
                        v___x_2986_ = lean_box(0);
                        v_vis_x3f_2956_ = v___x_2986_;
                        v___y_2957_ = v_a_2929_;
                        v___y_2958_ = v_a_2930_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_2937_);
                v___x_2943_ = l_Array_append___redArg(v___y_2937_, v___y_2942_);
                lean_dec_ref(v___y_2942_);
                lean_inc_n(v___y_2940_, 2);
                lean_inc_n(v___y_2941_, 3);
                v___x_2944_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2944_, 0, v___y_2941_);
                lean_ctor_set(v___x_2944_, 1, v___y_2940_);
                lean_ctor_set(v___x_2944_, 2, v___x_2943_);
                v___x_2945_ = l_Lean_SourceInfo_fromRef(v___y_2934_, v___x_2932_);
                lean_dec(v___y_2934_);
                v___x_2946_ = l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__2;
                lean_inc(v___x_2945_);
                v___x_2947_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2947_, 0, v___x_2945_);
                lean_ctor_set(v___x_2947_, 1, v___x_2946_);
                lean_inc(v___y_2938_);
                lean_inc(v___y_2936_);
                lean_inc_ref(v___x_2944_);
                lean_inc(v___y_2939_);
                v___x_2948_ = l_Lean_Syntax_node4(
                    v___y_2941_,
                    v___y_2939_,
                    v___x_2944_,
                    v___y_2936_,
                    v___x_2947_,
                    v___y_2938_,
                );
                v___x_2949_ = l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1;
                v___x_2950_ = l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__3;
                v___x_2951_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2951_, 0, v___x_2945_);
                lean_ctor_set(v___x_2951_, 1, v___x_2950_);
                v___x_2952_ = l_Lean_Syntax_node4(
                    v___y_2941_,
                    v___x_2949_,
                    v___x_2944_,
                    v___y_2936_,
                    v___x_2951_,
                    v___y_2938_,
                );
                v___x_2953_ =
                    l_Lean_Syntax_node2(v___y_2941_, v___y_2940_, v___x_2948_, v___x_2952_);
                v___x_2954_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2954_, 0, v___x_2953_);
                lean_ctor_set(v___x_2954_, 1, v___y_2935_);
                return v___x_2954_;
            }
            2 => {
                v___x_2959_ = lean_unsigned_to_nat(1);
                v___x_2960_ = l_Lean_Syntax_getArg(v_x_2928_, v___x_2959_);
                v___x_2961_ = l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4;
                lean_inc(v___x_2960_);
                v___x_2962_ = l_Lean_Syntax_isOfKind(v___x_2960_, v___x_2961_);
                if v___x_2962_ == 0 {
                    lean_dec(v___x_2960_);
                    lean_dec(v_vis_x3f_2956_);
                    lean_dec(v_x_2928_);
                    v___x_2963_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2958_);
                    return v___x_2963_;
                } else {
                    v_ref_2964_ = lean_ctor_get(v___y_2957_, 5);
                    v___x_2965_ = lean_unsigned_to_nat(2);
                    v_tk_2966_ = l_Lean_Syntax_getArg(v_x_2928_, v___x_2965_);
                    v___x_2967_ = lean_unsigned_to_nat(3);
                    v___x_2968_ = l_Lean_Syntax_getArg(v_x_2928_, v___x_2967_);
                    lean_dec(v_x_2928_);
                    v___x_2969_ = 0;
                    v___x_2970_ = l_Lean_SourceInfo_fromRef(v_ref_2964_, v___x_2969_);
                    v___x_2971_ =
                        l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__5;
                    v___x_2972_ = l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8;
                    v___x_2973_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6_once), _init_l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6);
                    if lean_obj_tag(v_vis_x3f_2956_) == 1 {
                        v_val_2974_ = lean_ctor_get(v_vis_x3f_2956_, 0);
                        lean_inc(v_val_2974_);
                        lean_dec_ref_known(v_vis_x3f_2956_, 1);
                        v___x_2975_ = l_Array_mkArray1___redArg(v_val_2974_);
                        v___y_2934_ = v_tk_2966_;
                        v___y_2935_ = v___y_2958_;
                        v___y_2936_ = v___x_2960_;
                        v___y_2937_ = v___x_2973_;
                        v___y_2938_ = v___x_2968_;
                        v___y_2939_ = v___x_2972_;
                        v___y_2940_ = v___x_2971_;
                        v___y_2941_ = v___x_2970_;
                        v___y_2942_ = v___x_2975_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_vis_x3f_2956_);
                        v___x_2976_ =
                            l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7;
                        v___y_2934_ = v_tk_2966_;
                        v___y_2935_ = v___y_2958_;
                        v___y_2936_ = v___x_2960_;
                        v___y_2937_ = v___x_2973_;
                        v___y_2938_ = v___x_2968_;
                        v___y_2939_ = v___x_2972_;
                        v___y_2940_ = v___x_2971_;
                        v___y_2941_ = v___x_2970_;
                        v___y_2942_ = v___x_2976_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___boxed(
    mut v_x_2987_: *mut LeanObject,
    mut v_a_2988_: *mut LeanObject,
    mut v_a_2989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2990_: *mut LeanObject = core::ptr::null_mut();
    v_res_2990_ =
        l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance(v_x_2987_, v_a_2988_, v_a_2989_);
    lean_dec_ref(v_a_2988_);
    return v_res_2990_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1()
-> *mut LeanObject {
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    v___x_2998_ = l_Lean_Elab_macroAttribute;
    v___x_2999_ = l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1;
    v___x_3000_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1;
    v___x_3001_ = lean_alloc_closure(
        l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_3002_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2998_,
        v___x_2999_,
        v___x_3000_,
        v___x_3001_,
    );
    return v___x_3002_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___boxed(
    mut v_a_3003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3004_: *mut LeanObject = core::ptr::null_mut();
    v_res_3004_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1();
    return v_res_3004_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta(
    mut v_x_3011_: *mut LeanObject,
    mut v_a_3012_: *mut LeanObject,
    mut v_a_3013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vis_x3f_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: u8 = 0;
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3037_: u8 = 0;
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3041_: u8 = 0;
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: u8 = 0;
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: u8 = 0;
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: u8 = 0;
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vis_x3f_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3042_ = l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1;
                lean_inc(v_x_3011_);
                v___x_3043_ = l_Lean_Syntax_isOfKind(v_x_3011_, v___x_3042_);
                if v___x_3043_ == 0 {
                    lean_dec(v_x_3011_);
                    v___x_3044_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                    return v___x_3044_;
                } else {
                    v___x_3045_ = lean_unsigned_to_nat(0);
                    v___x_3046_ = l_Lean_Syntax_getArg(v_x_3011_, v___x_3045_);
                    v___x_3047_ = l_Lean_Syntax_isNone(v___x_3046_);
                    if v___x_3047_ == 0 {
                        v___x_3048_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_3046_);
                        v___x_3049_ = l_Lean_Syntax_matchesNull(v___x_3046_, v___x_3048_);
                        if v___x_3049_ == 0 {
                            lean_dec(v___x_3046_);
                            lean_dec(v_x_3011_);
                            v___x_3050_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                            return v___x_3050_;
                        } else {
                            v_vis_x3f_3051_ = l_Lean_Syntax_getArg(v___x_3046_, v___x_3045_);
                            lean_dec(v___x_3046_);
                            v___x_3052_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_3052_, 0, v_vis_x3f_3051_);
                            v_vis_x3f_3016_ = v___x_3052_;
                            v___y_3017_ = v_a_3012_;
                            v___y_3018_ = v_a_3013_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3046_);
                        v___x_3053_ = lean_box(0);
                        v_vis_x3f_3016_ = v___x_3053_;
                        v___y_3017_ = v_a_3012_;
                        v___y_3018_ = v_a_3013_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3019_ = lean_unsigned_to_nat(1);
                v_kind_3020_ = l_Lean_Syntax_getArg(v_x_3011_, v___x_3019_);
                v___x_3021_ = l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4;
                lean_inc(v_kind_3020_);
                v___x_3022_ = l_Lean_Syntax_isOfKind(v_kind_3020_, v___x_3021_);
                if v___x_3022_ == 0 {
                    lean_dec(v_kind_3020_);
                    lean_dec(v_vis_x3f_3016_);
                    lean_dec(v_x_3011_);
                    v___x_3023_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                    return v___x_3023_;
                } else {
                    v___x_3024_ = lean_unsigned_to_nat(3);
                    v___x_3025_ = l_Lean_Syntax_getArg(v_x_3011_, v___x_3024_);
                    v___x_3026_ = lean_box(0);
                    lean_inc(v___x_3025_);
                    v___x_3027_ = lean_alloc_closure(
                        l_Lean_Elab_Term_elabTermAndSynthesize___boxed as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    lean_closure_set(v___x_3027_, 0, v___x_3025_);
                    lean_closure_set(v___x_3027_, 1, v___x_3026_);
                    v___x_3028_ = lean_alloc_closure(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___boxed as *mut core::ffi::c_void, 9, 2);
                    lean_closure_set(v___x_3028_, 0, lean_box(0));
                    lean_closure_set(v___x_3028_, 1, v___x_3027_);
                    v___x_3029_ = l_Lean_Elab_Command_liftTermElabM___redArg(
                        v___x_3028_,
                        v___y_3017_,
                        v___y_3018_,
                    );
                    if lean_obj_tag(v___x_3029_) == 0 {
                        v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
                        lean_inc(v_a_3030_);
                        lean_dec_ref_known(v___x_3029_, 1);
                        v___x_3031_ = lean_unsigned_to_nat(2);
                        v_tk_3032_ = l_Lean_Syntax_getArg(v_x_3011_, v___x_3031_);
                        lean_dec(v_x_3011_);
                        v___x_3033_ = l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval(
                            v_vis_x3f_3016_,
                            v_kind_3020_,
                            v_tk_3032_,
                            v___x_3025_,
                            v_a_3030_,
                            v___y_3017_,
                            v___y_3018_,
                        );
                        return v___x_3033_;
                    } else {
                        lean_dec(v___x_3025_);
                        lean_dec(v_kind_3020_);
                        lean_dec(v_vis_x3f_3016_);
                        lean_dec(v_x_3011_);
                        v_a_3034_ = lean_ctor_get(v___x_3029_, 0);
                        v_isSharedCheck_3041_ = (!lean_is_exclusive(v___x_3029_)) as u8;
                        if v_isSharedCheck_3041_ == 0 {
                            v___x_3036_ = v___x_3029_;
                            v_isShared_3037_ = v_isSharedCheck_3041_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3034_);
                            lean_dec(v___x_3029_);
                            v___x_3036_ = lean_box(0);
                            v_isShared_3037_ = v_isSharedCheck_3041_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_3037_ == 0 {
                    v___x_3039_ = v___x_3036_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
                    v___x_3039_ = v_reuseFailAlloc_3040_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3039_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___boxed(
    mut v_x_3054_: *mut LeanObject,
    mut v_a_3055_: *mut LeanObject,
    mut v_a_3056_: *mut LeanObject,
    mut v_a_3057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3058_: *mut LeanObject = core::ptr::null_mut();
    v_res_3058_ =
        l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta(v_x_3054_, v_a_3055_, v_a_3056_);
    lean_dec(v_a_3056_);
    lean_dec_ref(v_a_3055_);
    return v_res_3058_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1()
-> *mut LeanObject {
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    v___x_3066_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_3067_ = l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1;
    v___x_3068_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1;
    v___x_3069_ = lean_alloc_closure(
        l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_3070_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3066_,
        v___x_3067_,
        v___x_3068_,
        v___x_3069_,
    );
    return v___x_3070_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___boxed(
    mut v_a_3071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3072_: *mut LeanObject = core::ptr::null_mut();
    v_res_3072_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1();
    return v_res_3072_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0(
    mut v_sz_3073_: usize,
    mut v_i_3074_: usize,
    mut v_bs_3075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3076_: u8 = 0;
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: usize = 0;
    let mut v___x_3082_: usize = 0;
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3076_ = lean_usize_dec_lt(v_i_3074_, v_sz_3073_);
                if v___x_3076_ == 0 {
                    v___x_3077_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3077_, 0, v_bs_3075_);
                    return v___x_3077_;
                } else {
                    v_v_3078_ = lean_array_uget(v_bs_3075_, v_i_3074_);
                    v___x_3079_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3080_ = lean_array_uset(v_bs_3075_, v_i_3074_, v___x_3079_);
                    v___x_3081_ = 1usize;
                    v___x_3082_ = lean_usize_add(v_i_3074_, v___x_3081_);
                    v___x_3083_ = lean_array_uset(v_bs_x27_3080_, v_i_3074_, v_v_3078_);
                    v_i_3074_ = v___x_3082_;
                    v_bs_3075_ = v___x_3083_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0___boxed(
    mut v_sz_3085_: *mut LeanObject,
    mut v_i_3086_: *mut LeanObject,
    mut v_bs_3087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3088_: usize = 0;
    let mut v_i_boxed_3089_: usize = 0;
    let mut v_res_3090_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3088_ = lean_unbox_usize(v_sz_3085_);
    lean_dec(v_sz_3085_);
    v_i_boxed_3089_ = lean_unbox_usize(v_i_3086_);
    lean_dec(v_i_3086_);
    v_res_3090_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0(v_sz_boxed_3088_, v_i_boxed_3089_, v_bs_3087_);
    return v_res_3090_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1(
    mut v_sz_3091_: usize,
    mut v_i_3092_: usize,
    mut v_bs_3093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3094_: u8 = 0;
    let mut v_v_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: usize = 0;
    let mut v___x_3102_: usize = 0;
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3094_ = lean_usize_dec_lt(v_i_3092_, v_sz_3091_);
                if v___x_3094_ == 0 {
                    return v_bs_3093_;
                } else {
                    v_v_3095_ = lean_array_uget(v_bs_3093_, v_i_3092_);
                    v___x_3096_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3097_ = lean_array_uset(v_bs_3093_, v_i_3092_, v___x_3096_);
                    v___x_3098_ = l_Lean_TSyntax_getId(v_v_3095_);
                    v___x_3099_ = lean_erase_macro_scopes(v___x_3098_);
                    v___x_3100_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3100_, 0, v_v_3095_);
                    lean_ctor_set(v___x_3100_, 1, v___x_3099_);
                    v___x_3101_ = 1usize;
                    v___x_3102_ = lean_usize_add(v_i_3092_, v___x_3101_);
                    v___x_3103_ = lean_array_uset(v_bs_x27_3097_, v_i_3092_, v___x_3100_);
                    v_i_3092_ = v___x_3102_;
                    v_bs_3093_ = v___x_3103_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1___boxed(
    mut v_sz_3105_: *mut LeanObject,
    mut v_i_3106_: *mut LeanObject,
    mut v_bs_3107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3108_: usize = 0;
    let mut v_i_boxed_3109_: usize = 0;
    let mut v_res_3110_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3108_ = lean_unbox_usize(v_sz_3105_);
    lean_dec(v_sz_3105_);
    v_i_boxed_3109_ = lean_unbox_usize(v_i_3106_);
    lean_dec(v_i_3106_);
    v_res_3110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1(v_sz_boxed_3108_, v_i_boxed_3109_, v_bs_3107_);
    return v_res_3110_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(
    mut v___x_3111_: u8,
    mut v_as_3112_: *mut LeanObject,
    mut v_i_3113_: usize,
    mut v_stop_3114_: usize,
    mut v_b_3115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: usize = 0;
    let mut v___x_3119_: usize = 0;
    let mut v___x_3121_: u8 = 0;
    let mut v_fst_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: u8 = 0;
    let mut v_snd_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3127_: u8 = 0;
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3132_: u8 = 0;
    let mut v_unused_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3137_: u8 = 0;
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3144_: u8 = 0;
    let mut v_unused_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3121_ = lean_usize_dec_eq(v_i_3113_, v_stop_3114_);
                if v___x_3121_ == 0 {
                    v_fst_3122_ = lean_ctor_get(v_b_3115_, 0);
                    v___x_3123_ = (lean_unbox(v_fst_3122_) as u8);
                    if v___x_3123_ == 0 {
                        v_snd_3124_ = lean_ctor_get(v_b_3115_, 1);
                        v_isSharedCheck_3132_ = (!lean_is_exclusive(v_b_3115_)) as u8;
                        if v_isSharedCheck_3132_ == 0 {
                            v_unused_3133_ = lean_ctor_get(v_b_3115_, 0);
                            lean_dec(v_unused_3133_);
                            v___x_3126_ = v_b_3115_;
                            v_isShared_3127_ = v_isSharedCheck_3132_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_snd_3124_);
                            lean_dec(v_b_3115_);
                            v___x_3126_ = lean_box(0);
                            v_isShared_3127_ = v_isSharedCheck_3132_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_3134_ = lean_ctor_get(v_b_3115_, 1);
                        v_isSharedCheck_3144_ = (!lean_is_exclusive(v_b_3115_)) as u8;
                        if v_isSharedCheck_3144_ == 0 {
                            v_unused_3145_ = lean_ctor_get(v_b_3115_, 0);
                            lean_dec(v_unused_3145_);
                            v___x_3136_ = v_b_3115_;
                            v_isShared_3137_ = v_isSharedCheck_3144_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_snd_3134_);
                            lean_dec(v_b_3115_);
                            v___x_3136_ = lean_box(0);
                            v_isShared_3137_ = v_isSharedCheck_3144_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    return v_b_3115_;
                }
            }
            1 => {
                v___x_3118_ = 1usize;
                v___x_3119_ = lean_usize_add(v_i_3113_, v___x_3118_);
                v_i_3113_ = v___x_3119_;
                v_b_3115_ = v___y_3117_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3128_ = lean_box((v___x_3111_) as usize);
                if v_isShared_3127_ == 0 {
                    lean_ctor_set(v___x_3126_, 0, v___x_3128_);
                    v___x_3130_ = v___x_3126_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3128_);
                    lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_snd_3124_);
                    v___x_3130_ = v_reuseFailAlloc_3131_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_3117_ = v___x_3130_;
                state = 1;
                continue;
            }
            4 => {
                v___x_3138_ = lean_array_uget_borrowed(v_as_3112_, v_i_3113_);
                lean_inc(v___x_3138_);
                v___x_3139_ = lean_array_push(v_snd_3134_, v___x_3138_);
                v___x_3140_ = lean_box((v___x_3121_) as usize);
                if v_isShared_3137_ == 0 {
                    lean_ctor_set(v___x_3136_, 1, v___x_3139_);
                    lean_ctor_set(v___x_3136_, 0, v___x_3140_);
                    v___x_3142_ = v___x_3136_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3140_);
                    lean_ctor_set(v_reuseFailAlloc_3143_, 1, v___x_3139_);
                    v___x_3142_ = v_reuseFailAlloc_3143_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_3117_ = v___x_3142_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2___boxed(
    mut v___x_3146_: *mut LeanObject,
    mut v_as_3147_: *mut LeanObject,
    mut v_i_3148_: *mut LeanObject,
    mut v_stop_3149_: *mut LeanObject,
    mut v_b_3150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8515__boxed_3151_: u8 = 0;
    let mut v_i_boxed_3152_: usize = 0;
    let mut v_stop_boxed_3153_: usize = 0;
    let mut v_res_3154_: *mut LeanObject = core::ptr::null_mut();
    v___x_8515__boxed_3151_ = (lean_unbox(v___x_3146_) as u8);
    v_i_boxed_3152_ = lean_unbox_usize(v_i_3148_);
    lean_dec(v_i_3148_);
    v_stop_boxed_3153_ = lean_unbox_usize(v_stop_3149_);
    lean_dec(v_stop_3149_);
    v_res_3154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_8515__boxed_3151_, v_as_3147_, v_i_boxed_3152_, v_stop_boxed_3153_, v_b_3150_);
    lean_dec_ref(v_as_3147_);
    return v_res_3154_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(
    mut v_as_3194_: *mut LeanObject,
    mut v_sz_3195_: usize,
    mut v_i_3196_: usize,
    mut v_b_3197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: usize = 0;
    let mut v___x_3202_: usize = 0;
    let mut v___x_3204_: u8 = 0;
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3210_: u8 = 0;
    let mut v___y_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3213_: usize = 0;
    let mut v___x_3214_: usize = 0;
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3223_: u8 = 0;
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3227_: u8 = 0;
    let mut v_val_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3229_: usize = 0;
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: u8 = 0;
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3243_: u8 = 0;
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3247_: u8 = 0;
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: u8 = 0;
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: u8 = 0;
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3264_: u8 = 0;
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: u8 = 0;
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3273_: u8 = 0;
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3277_: u8 = 0;
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3282_: u8 = 0;
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_____x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: u8 = 0;
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3297_: u8 = 0;
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3301_: u8 = 0;
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: u8 = 0;
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: u8 = 0;
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3312_: u8 = 0;
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3316_: u8 = 0;
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: u8 = 0;
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: u8 = 0;
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3327_: u8 = 0;
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3331_: u8 = 0;
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: u8 = 0;
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: u8 = 0;
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3341_: u8 = 0;
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3345_: u8 = 0;
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: u8 = 0;
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: u8 = 0;
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: u8 = 0;
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: u8 = 0;
    let mut v___x_3360_: usize = 0;
    let mut v___x_3361_: usize = 0;
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: usize = 0;
    let mut v___x_3365_: usize = 0;
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3368_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3204_ = lean_usize_dec_lt(v_i_3196_, v_sz_3195_);
                if v___x_3204_ == 0 {
                    v___x_3205_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3205_, 0, v_b_3197_);
                    return v___x_3205_;
                } else {
                    v_fst_3206_ = lean_ctor_get(v_b_3197_, 0);
                    v_snd_3207_ = lean_ctor_get(v_b_3197_, 1);
                    v_isSharedCheck_3368_ = (!lean_is_exclusive(v_b_3197_)) as u8;
                    if v_isSharedCheck_3368_ == 0 {
                        v___x_3209_ = v_b_3197_;
                        v_isShared_3210_ = v_isSharedCheck_3368_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_3207_);
                        lean_inc(v_fst_3206_);
                        lean_dec(v_b_3197_);
                        v___x_3209_ = lean_box(0);
                        v_isShared_3210_ = v_isSharedCheck_3368_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3201_ = 1usize;
                v___x_3202_ = lean_usize_add(v_i_3196_, v___x_3201_);
                v_i_3196_ = v___x_3202_;
                v_b_3197_ = v_a_3200_;
                state = 0;
                continue;
            }
            2 => {
                v_a_3235_ = lean_array_uget_borrowed(v_as_3194_, v_i_3196_);
                v___x_3236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1;
                lean_inc(v_a_3235_);
                v___x_3237_ = l_Lean_Syntax_isOfKind(v_a_3235_, v___x_3236_);
                if v___x_3237_ == 0 {
                    lean_del_object(v___x_3209_);
                    v___x_3238_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                    if lean_obj_tag(v___x_3238_) == 0 {
                        lean_dec_ref_known(v___x_3238_, 1);
                        v___x_3239_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3239_, 0, v_fst_3206_);
                        lean_ctor_set(v___x_3239_, 1, v_snd_3207_);
                        v_a_3200_ = v___x_3239_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_snd_3207_);
                        lean_dec(v_fst_3206_);
                        v_a_3240_ = lean_ctor_get(v___x_3238_, 0);
                        v_isSharedCheck_3247_ = (!lean_is_exclusive(v___x_3238_)) as u8;
                        if v_isSharedCheck_3247_ == 0 {
                            v___x_3242_ = v___x_3238_;
                            v_isShared_3243_ = v_isSharedCheck_3247_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3240_);
                            lean_dec(v___x_3238_);
                            v___x_3242_ = lean_box(0);
                            v_isShared_3243_ = v_isSharedCheck_3247_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v___x_3248_ = lean_unsigned_to_nat(0);
                    v___x_3249_ = lean_unsigned_to_nat(1);
                    v___x_3250_ = l_Lean_Syntax_getArg(v_a_3235_, v___x_3248_);
                    v___x_3251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3;
                    lean_inc(v___x_3250_);
                    v___x_3252_ = l_Lean_Syntax_isOfKind(v___x_3250_, v___x_3251_);
                    if v___x_3252_ == 0 {
                        lean_del_object(v___x_3209_);
                        v___x_3253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5;
                        lean_inc(v___x_3250_);
                        v___x_3254_ = l_Lean_Syntax_isOfKind(v___x_3250_, v___x_3253_);
                        if v___x_3254_ == 0 {
                            lean_dec(v___x_3250_);
                            v___x_3255_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                            if lean_obj_tag(v___x_3255_) == 0 {
                                lean_dec_ref_known(v___x_3255_, 1);
                                v___x_3256_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_3256_, 0, v_fst_3206_);
                                lean_ctor_set(v___x_3256_, 1, v_snd_3207_);
                                v_a_3200_ = v___x_3256_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_snd_3207_);
                                lean_dec(v_fst_3206_);
                                v_a_3257_ = lean_ctor_get(v___x_3255_, 0);
                                v_isSharedCheck_3264_ = (!lean_is_exclusive(v___x_3255_)) as u8;
                                if v_isSharedCheck_3264_ == 0 {
                                    v___x_3259_ = v___x_3255_;
                                    v_isShared_3260_ = v_isSharedCheck_3264_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_a_3257_);
                                    lean_dec(v___x_3255_);
                                    v___x_3259_ = lean_box(0);
                                    v_isShared_3260_ = v_isSharedCheck_3264_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            v___x_3265_ = l_Lean_Syntax_getArg(v___x_3250_, v___x_3249_);
                            v___x_3266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7;
                            lean_inc(v___x_3265_);
                            v___x_3267_ = l_Lean_Syntax_isOfKind(v___x_3265_, v___x_3266_);
                            if v___x_3267_ == 0 {
                                lean_dec(v___x_3265_);
                                lean_dec(v___x_3250_);
                                v___x_3268_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                                if lean_obj_tag(v___x_3268_) == 0 {
                                    lean_dec_ref_known(v___x_3268_, 1);
                                    v___x_3269_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_3269_, 0, v_fst_3206_);
                                    lean_ctor_set(v___x_3269_, 1, v_snd_3207_);
                                    v_a_3200_ = v___x_3269_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_snd_3207_);
                                    lean_dec(v_fst_3206_);
                                    v_a_3270_ = lean_ctor_get(v___x_3268_, 0);
                                    v_isSharedCheck_3277_ = (!lean_is_exclusive(v___x_3268_)) as u8;
                                    if v_isSharedCheck_3277_ == 0 {
                                        v___x_3272_ = v___x_3268_;
                                        v_isShared_3273_ = v_isSharedCheck_3277_;
                                        state = 12;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3270_);
                                        lean_dec(v___x_3268_);
                                        v___x_3272_ = lean_box(0);
                                        v_isShared_3273_ = v_isSharedCheck_3277_;
                                        state = 12;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_3278_ = lean_unsigned_to_nat(3);
                                v___x_3279_ = l_Lean_Syntax_getArg(v___x_3250_, v___x_3278_);
                                lean_dec(v___x_3250_);
                                if v___x_3267_ == 0 {
                                    v___x_3292_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                                    if lean_obj_tag(v___x_3292_) == 0 {
                                        v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
                                        lean_inc(v_a_3293_);
                                        lean_dec_ref_known(v___x_3292_, 1);
                                        v_____x_3288_ = v_a_3293_;
                                        state = 15;
                                        continue;
                                    } else {
                                        lean_dec(v___x_3279_);
                                        lean_dec(v___x_3265_);
                                        lean_dec(v_snd_3207_);
                                        lean_dec(v_fst_3206_);
                                        v_a_3294_ = lean_ctor_get(v___x_3292_, 0);
                                        v_isSharedCheck_3301_ =
                                            (!lean_is_exclusive(v___x_3292_)) as u8;
                                        if v_isSharedCheck_3301_ == 0 {
                                            v___x_3296_ = v___x_3292_;
                                            v_isShared_3297_ = v_isSharedCheck_3301_;
                                            state = 16;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3294_);
                                            lean_dec(v___x_3292_);
                                            v___x_3296_ = lean_box(0);
                                            v_isShared_3297_ = v_isSharedCheck_3301_;
                                            state = 16;
                                            continue;
                                        }
                                    }
                                } else {
                                    v___x_3302_ = l_Lean_Syntax_getArg(v___x_3265_, v___x_3248_);
                                    v___x_3303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9;
                                    lean_inc(v___x_3302_);
                                    v___x_3304_ = l_Lean_Syntax_isOfKind(v___x_3302_, v___x_3303_);
                                    if v___x_3304_ == 0 {
                                        v___x_3305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11;
                                        v___x_3306_ =
                                            l_Lean_Syntax_isOfKind(v___x_3302_, v___x_3305_);
                                        if v___x_3306_ == 0 {
                                            v___x_3307_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                                            if lean_obj_tag(v___x_3307_) == 0 {
                                                v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
                                                lean_inc(v_a_3308_);
                                                lean_dec_ref_known(v___x_3307_, 1);
                                                v_____x_3288_ = v_a_3308_;
                                                state = 15;
                                                continue;
                                            } else {
                                                lean_dec(v___x_3279_);
                                                lean_dec(v___x_3265_);
                                                lean_dec(v_snd_3207_);
                                                lean_dec(v_fst_3206_);
                                                v_a_3309_ = lean_ctor_get(v___x_3307_, 0);
                                                v_isSharedCheck_3316_ =
                                                    (!lean_is_exclusive(v___x_3307_)) as u8;
                                                if v_isSharedCheck_3316_ == 0 {
                                                    v___x_3311_ = v___x_3307_;
                                                    v_isShared_3312_ = v_isSharedCheck_3316_;
                                                    state = 18;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3309_);
                                                    lean_dec(v___x_3307_);
                                                    v___x_3311_ = lean_box(0);
                                                    v_isShared_3312_ = v_isSharedCheck_3316_;
                                                    state = 18;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            v___x_3317_ = lean_box(0);
                                            v___x_3318_ = 1;
                                            v_fst_3281_ = v___x_3317_;
                                            v_snd_3282_ = v___x_3318_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v___x_3319_ =
                                            l_Lean_Syntax_getArg(v___x_3302_, v___x_3248_);
                                        v___x_3320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13;
                                        lean_inc(v___x_3319_);
                                        v___x_3321_ =
                                            l_Lean_Syntax_isOfKind(v___x_3319_, v___x_3320_);
                                        if v___x_3321_ == 0 {
                                            lean_dec(v___x_3319_);
                                            lean_dec(v___x_3302_);
                                            v___x_3322_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                                            if lean_obj_tag(v___x_3322_) == 0 {
                                                v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
                                                lean_inc(v_a_3323_);
                                                lean_dec_ref_known(v___x_3322_, 1);
                                                v_____x_3288_ = v_a_3323_;
                                                state = 15;
                                                continue;
                                            } else {
                                                lean_dec(v___x_3279_);
                                                lean_dec(v___x_3265_);
                                                lean_dec(v_snd_3207_);
                                                lean_dec(v_fst_3206_);
                                                v_a_3324_ = lean_ctor_get(v___x_3322_, 0);
                                                v_isSharedCheck_3331_ =
                                                    (!lean_is_exclusive(v___x_3322_)) as u8;
                                                if v_isSharedCheck_3331_ == 0 {
                                                    v___x_3326_ = v___x_3322_;
                                                    v_isShared_3327_ = v_isSharedCheck_3331_;
                                                    state = 20;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3324_);
                                                    lean_dec(v___x_3322_);
                                                    v___x_3326_ = lean_box(0);
                                                    v_isShared_3327_ = v_isSharedCheck_3331_;
                                                    state = 20;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            v___x_3332_ =
                                                l_Lean_Syntax_getArg(v___x_3302_, v___x_3249_);
                                            lean_dec(v___x_3302_);
                                            lean_inc(v___x_3332_);
                                            v___x_3333_ =
                                                l_Lean_Syntax_matchesNull(v___x_3332_, v___x_3248_);
                                            if v___x_3333_ == 0 {
                                                v___x_3334_ = lean_unsigned_to_nat(2);
                                                v___x_3335_ = l_Lean_Syntax_matchesNull(
                                                    v___x_3332_,
                                                    v___x_3334_,
                                                );
                                                if v___x_3335_ == 0 {
                                                    lean_dec(v___x_3319_);
                                                    v___x_3336_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                                                    if lean_obj_tag(v___x_3336_) == 0 {
                                                        v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
                                                        lean_inc(v_a_3337_);
                                                        lean_dec_ref_known(v___x_3336_, 1);
                                                        v_____x_3288_ = v_a_3337_;
                                                        state = 15;
                                                        continue;
                                                    } else {
                                                        lean_dec(v___x_3279_);
                                                        lean_dec(v___x_3265_);
                                                        lean_dec(v_snd_3207_);
                                                        lean_dec(v_fst_3206_);
                                                        v_a_3338_ = lean_ctor_get(v___x_3336_, 0);
                                                        v_isSharedCheck_3345_ =
                                                            (!lean_is_exclusive(v___x_3336_)) as u8;
                                                        if v_isSharedCheck_3345_ == 0 {
                                                            v___x_3340_ = v___x_3336_;
                                                            v_isShared_3341_ =
                                                                v_isSharedCheck_3345_;
                                                            state = 22;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_3338_);
                                                            lean_dec(v___x_3336_);
                                                            v___x_3340_ = lean_box(0);
                                                            v_isShared_3341_ =
                                                                v_isSharedCheck_3345_;
                                                            state = 22;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    v___x_3346_ = l_Lean_TSyntax_getId(v___x_3319_);
                                                    lean_dec(v___x_3319_);
                                                    v___x_3347_ =
                                                        lean_erase_macro_scopes(v___x_3346_);
                                                    v___x_3348_ = 1;
                                                    v_fst_3281_ = v___x_3347_;
                                                    v_snd_3282_ = v___x_3348_;
                                                    state = 14;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec(v___x_3332_);
                                                v___x_3349_ = l_Lean_TSyntax_getId(v___x_3319_);
                                                lean_dec(v___x_3319_);
                                                v___x_3350_ = lean_erase_macro_scopes(v___x_3349_);
                                                v___x_3351_ = 0;
                                                v_fst_3281_ = v___x_3350_;
                                                v_snd_3282_ = v___x_3351_;
                                                state = 14;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        v___x_3352_ = l_Lean_Syntax_getArg(v___x_3250_, v___x_3249_);
                        lean_dec(v___x_3250_);
                        v___x_3353_ = l_Lean_Syntax_getArgs(v___x_3352_);
                        lean_dec(v___x_3352_);
                        v___x_3354_ =
                            l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7;
                        v___x_3355_ = lean_array_get_size(v___x_3353_);
                        v___x_3356_ = lean_nat_dec_lt(v___x_3248_, v___x_3355_);
                        if v___x_3356_ == 0 {
                            lean_dec_ref(v___x_3353_);
                            v___y_3212_ = v___x_3354_;
                            state = 3;
                            continue;
                        } else {
                            v___x_3357_ = lean_box((v___x_3252_) as usize);
                            v___x_3358_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_3358_, 0, v___x_3357_);
                            lean_ctor_set(v___x_3358_, 1, v___x_3354_);
                            v___x_3359_ = lean_nat_dec_le(v___x_3355_, v___x_3355_);
                            if v___x_3359_ == 0 {
                                if v___x_3356_ == 0 {
                                    lean_dec_ref_known(v___x_3358_, 2);
                                    lean_dec_ref(v___x_3353_);
                                    v___y_3212_ = v___x_3354_;
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3360_ = 0usize;
                                    v___x_3361_ = lean_usize_of_nat(v___x_3355_);
                                    v___x_3362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_3252_, v___x_3353_, v___x_3360_, v___x_3361_, v___x_3358_);
                                    lean_dec_ref(v___x_3353_);
                                    v_snd_3363_ = lean_ctor_get(v___x_3362_, 1);
                                    lean_inc(v_snd_3363_);
                                    lean_dec_ref(v___x_3362_);
                                    v___y_3212_ = v_snd_3363_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v___x_3364_ = 0usize;
                                v___x_3365_ = lean_usize_of_nat(v___x_3355_);
                                v___x_3366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_3252_, v___x_3353_, v___x_3364_, v___x_3365_, v___x_3358_);
                                lean_dec_ref(v___x_3353_);
                                v_snd_3367_ = lean_ctor_get(v___x_3366_, 1);
                                lean_inc(v_snd_3367_);
                                lean_dec_ref(v___x_3366_);
                                v___y_3212_ = v_snd_3367_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v_sz_3213_ = lean_array_size(v___y_3212_);
                v___x_3214_ = 0usize;
                v___x_3215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0(v_sz_3213_, v___x_3214_, v___y_3212_);
                if lean_obj_tag(v___x_3215_) == 0 {
                    v___x_3216_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                    if lean_obj_tag(v___x_3216_) == 0 {
                        lean_dec_ref_known(v___x_3216_, 1);
                        if v_isShared_3210_ == 0 {
                            v___x_3218_ = v___x_3209_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_fst_3206_);
                            lean_ctor_set(v_reuseFailAlloc_3219_, 1, v_snd_3207_);
                            v___x_3218_ = v_reuseFailAlloc_3219_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3209_);
                        lean_dec(v_snd_3207_);
                        lean_dec(v_fst_3206_);
                        v_a_3220_ = lean_ctor_get(v___x_3216_, 0);
                        v_isSharedCheck_3227_ = (!lean_is_exclusive(v___x_3216_)) as u8;
                        if v_isSharedCheck_3227_ == 0 {
                            v___x_3222_ = v___x_3216_;
                            v_isShared_3223_ = v_isSharedCheck_3227_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3220_);
                            lean_dec(v___x_3216_);
                            v___x_3222_ = lean_box(0);
                            v_isShared_3223_ = v_isSharedCheck_3227_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_val_3228_ = lean_ctor_get(v___x_3215_, 0);
                    lean_inc(v_val_3228_);
                    lean_dec_ref_known(v___x_3215_, 1);
                    v_sz_3229_ = lean_array_size(v_val_3228_);
                    v___x_3230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1(v_sz_3229_, v___x_3214_, v_val_3228_);
                    v___x_3231_ = l_Array_append___redArg(v_fst_3206_, v___x_3230_);
                    lean_dec_ref(v___x_3230_);
                    if v_isShared_3210_ == 0 {
                        lean_ctor_set(v___x_3209_, 0, v___x_3231_);
                        v___x_3233_ = v___x_3209_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3231_);
                        lean_ctor_set(v_reuseFailAlloc_3234_, 1, v_snd_3207_);
                        v___x_3233_ = v_reuseFailAlloc_3234_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v_a_3200_ = v___x_3218_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_3223_ == 0 {
                    v___x_3225_ = v___x_3222_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3220_);
                    v___x_3225_ = v_reuseFailAlloc_3226_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3225_;
            }
            7 => {
                v_a_3200_ = v___x_3233_;
                state = 1;
                continue;
            }
            8 => {
                if v_isShared_3243_ == 0 {
                    v___x_3245_ = v___x_3242_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
                    v___x_3245_ = v_reuseFailAlloc_3246_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3245_;
            }
            10 => {
                if v_isShared_3260_ == 0 {
                    v___x_3262_ = v___x_3259_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
                    v___x_3262_ = v_reuseFailAlloc_3263_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3262_;
            }
            12 => {
                if v_isShared_3273_ == 0 {
                    v___x_3275_ = v___x_3272_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
                    v___x_3275_ = v_reuseFailAlloc_3276_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3275_;
            }
            14 => {
                v___x_3283_ = lean_box(0);
                v___x_3284_ = lean_alloc_ctor(0, 5, (1) as u32);
                lean_ctor_set(v___x_3284_, 0, v___x_3265_);
                lean_ctor_set(v___x_3284_, 1, v_fst_3281_);
                lean_ctor_set(v___x_3284_, 2, v___x_3279_);
                lean_ctor_set(v___x_3284_, 3, v___x_3283_);
                lean_ctor_set(v___x_3284_, 4, v___x_3283_);
                lean_ctor_set_uint8(
                    v___x_3284_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v_snd_3282_,
                );
                v___x_3285_ = lean_array_push(v_snd_3207_, v___x_3284_);
                v___x_3286_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3286_, 0, v_fst_3206_);
                lean_ctor_set(v___x_3286_, 1, v___x_3285_);
                v_a_3200_ = v___x_3286_;
                state = 1;
                continue;
            }
            15 => {
                v_fst_3289_ = lean_ctor_get(v_____x_3288_, 0);
                lean_inc(v_fst_3289_);
                v_snd_3290_ = lean_ctor_get(v_____x_3288_, 1);
                lean_inc(v_snd_3290_);
                lean_dec_ref(v_____x_3288_);
                v___x_3291_ = (lean_unbox(v_snd_3290_) as u8);
                lean_dec(v_snd_3290_);
                v_fst_3281_ = v_fst_3289_;
                v_snd_3282_ = v___x_3291_;
                state = 14;
                continue;
            }
            16 => {
                if v_isShared_3297_ == 0 {
                    v___x_3299_ = v___x_3296_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
                    v___x_3299_ = v_reuseFailAlloc_3300_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3299_;
            }
            18 => {
                if v_isShared_3312_ == 0 {
                    v___x_3314_ = v___x_3311_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
                    v___x_3314_ = v_reuseFailAlloc_3315_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3314_;
            }
            20 => {
                if v_isShared_3327_ == 0 {
                    v___x_3329_ = v___x_3326_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
                    v___x_3329_ = v_reuseFailAlloc_3330_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3329_;
            }
            22 => {
                if v_isShared_3341_ == 0 {
                    v___x_3343_ = v___x_3340_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
                    v___x_3343_ = v_reuseFailAlloc_3344_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___boxed(
    mut v_as_3369_: *mut LeanObject,
    mut v_sz_3370_: *mut LeanObject,
    mut v_i_3371_: *mut LeanObject,
    mut v_b_3372_: *mut LeanObject,
    mut v___y_3373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3374_: usize = 0;
    let mut v_i_boxed_3375_: usize = 0;
    let mut v_res_3376_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3374_ = lean_unbox_usize(v_sz_3370_);
    lean_dec(v_sz_3370_);
    v_i_boxed_3375_ = lean_unbox_usize(v_i_3371_);
    lean_dec(v_i_3371_);
    v_res_3376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(v_as_3369_, v_sz_boxed_3374_, v_i_boxed_3375_, v_b_3372_);
    lean_dec_ref(v_as_3369_);
    return v_res_3376_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3(
    mut v_sz_3377_: usize,
    mut v_i_3378_: usize,
    mut v_bs_3379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3380_: u8 = 0;
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: u8 = 0;
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: usize = 0;
    let mut v___x_3389_: usize = 0;
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3380_ = lean_usize_dec_lt(v_i_3378_, v_sz_3377_);
                if v___x_3380_ == 0 {
                    v___x_3381_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3381_, 0, v_bs_3379_);
                    return v___x_3381_;
                } else {
                    v_v_3382_ = lean_array_uget(v_bs_3379_, v_i_3378_);
                    v___x_3383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1;
                    lean_inc(v_v_3382_);
                    v___x_3384_ = l_Lean_Syntax_isOfKind(v_v_3382_, v___x_3383_);
                    if v___x_3384_ == 0 {
                        lean_dec(v_v_3382_);
                        lean_dec_ref(v_bs_3379_);
                        v___x_3385_ = lean_box(0);
                        return v___x_3385_;
                    } else {
                        v___x_3386_ = lean_unsigned_to_nat(0);
                        v_bs_x27_3387_ = lean_array_uset(v_bs_3379_, v_i_3378_, v___x_3386_);
                        v___x_3388_ = 1usize;
                        v___x_3389_ = lean_usize_add(v_i_3378_, v___x_3388_);
                        v___x_3390_ = lean_array_uset(v_bs_x27_3387_, v_i_3378_, v_v_3382_);
                        v_i_3378_ = v___x_3389_;
                        v_bs_3379_ = v___x_3390_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3___boxed(
    mut v_sz_3392_: *mut LeanObject,
    mut v_i_3393_: *mut LeanObject,
    mut v_bs_3394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3395_: usize = 0;
    let mut v_i_boxed_3396_: usize = 0;
    let mut v_res_3397_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3395_ = lean_unbox_usize(v_sz_3392_);
    lean_dec(v_sz_3392_);
    v_i_boxed_3396_ = lean_unbox_usize(v_i_3393_);
    lean_dec(v_i_3393_);
    v_res_3397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3(v_sz_boxed_3395_, v_i_boxed_3396_, v_bs_3394_);
    return v_res_3397_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_mkEvalConfigItemView(
    mut v_entries_x3f_3408_: *mut LeanObject,
    mut v_a_3409_: *mut LeanObject,
    mut v_a_3410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_omitFields_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_handlers_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_omitFields_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3421_: usize = 0;
    let mut v___x_3422_: usize = 0;
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3428_: u8 = 0;
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3432_: u8 = 0;
    let mut v_val_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3435_: usize = 0;
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3443_: u8 = 0;
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3447_: u8 = 0;
    let mut v_val_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: u8 = 0;
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3455_: u8 = 0;
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3459_: u8 = 0;
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: u8 = 0;
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: u8 = 0;
    let mut v___x_3469_: usize = 0;
    let mut v___x_3470_: usize = 0;
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: usize = 0;
    let mut v___x_3474_: usize = 0;
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3417_ = lean_unsigned_to_nat(0);
                v_omitFields_3418_ = l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0;
                if lean_obj_tag(v_entries_x3f_3408_) == 1 {
                    v_val_3448_ = lean_ctor_get(v_entries_x3f_3408_, 0);
                    lean_inc_n(v_val_3448_, 2);
                    lean_dec_ref_known(v_entries_x3f_3408_, 1);
                    v___x_3449_ = l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3;
                    v___x_3450_ = l_Lean_Syntax_isOfKind(v_val_3448_, v___x_3449_);
                    if v___x_3450_ == 0 {
                        lean_dec(v_val_3448_);
                        v___x_3451_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                        v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
                        v_isSharedCheck_3459_ = (!lean_is_exclusive(v___x_3451_)) as u8;
                        if v_isSharedCheck_3459_ == 0 {
                            v___x_3454_ = v___x_3451_;
                            v_isShared_3455_ = v_isSharedCheck_3459_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_3452_);
                            lean_dec(v___x_3451_);
                            v___x_3454_ = lean_box(0);
                            v_isShared_3455_ = v_isSharedCheck_3459_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v___x_3460_ = lean_unsigned_to_nat(1);
                        v___x_3461_ = l_Lean_Syntax_getArg(v_val_3448_, v___x_3460_);
                        lean_dec(v_val_3448_);
                        v___x_3462_ = l_Lean_Syntax_getArgs(v___x_3461_);
                        lean_dec(v___x_3461_);
                        v___x_3463_ =
                            l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7;
                        v___x_3464_ = lean_array_get_size(v___x_3462_);
                        v___x_3465_ = lean_nat_dec_lt(v___x_3417_, v___x_3464_);
                        if v___x_3465_ == 0 {
                            lean_dec_ref(v___x_3462_);
                            v___y_3420_ = v___x_3463_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3466_ = lean_box((v___x_3450_) as usize);
                            v___x_3467_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_3467_, 0, v___x_3466_);
                            lean_ctor_set(v___x_3467_, 1, v___x_3463_);
                            v___x_3468_ = lean_nat_dec_le(v___x_3464_, v___x_3464_);
                            if v___x_3468_ == 0 {
                                if v___x_3465_ == 0 {
                                    lean_dec_ref_known(v___x_3467_, 2);
                                    lean_dec_ref(v___x_3462_);
                                    v___y_3420_ = v___x_3463_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_3469_ = 0usize;
                                    v___x_3470_ = lean_usize_of_nat(v___x_3464_);
                                    v___x_3471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_3450_, v___x_3462_, v___x_3469_, v___x_3470_, v___x_3467_);
                                    lean_dec_ref(v___x_3462_);
                                    v_snd_3472_ = lean_ctor_get(v___x_3471_, 1);
                                    lean_inc(v_snd_3472_);
                                    lean_dec_ref(v___x_3471_);
                                    v___y_3420_ = v_snd_3472_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___x_3473_ = 0usize;
                                v___x_3474_ = lean_usize_of_nat(v___x_3464_);
                                v___x_3475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_3450_, v___x_3462_, v___x_3473_, v___x_3474_, v___x_3467_);
                                lean_dec_ref(v___x_3462_);
                                v_snd_3476_ = lean_ctor_get(v___x_3475_, 1);
                                lean_inc(v_snd_3476_);
                                lean_dec_ref(v___x_3475_);
                                v___y_3420_ = v_snd_3476_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_entries_x3f_3408_);
                    v_omitFields_3413_ = v_omitFields_3418_;
                    v_handlers_3414_ = v_omitFields_3418_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3415_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3415_, 0, v_omitFields_3413_);
                lean_ctor_set(v___x_3415_, 1, v_handlers_3414_);
                v___x_3416_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3416_, 0, v___x_3415_);
                return v___x_3416_;
            }
            2 => {
                v_sz_3421_ = lean_array_size(v___y_3420_);
                v___x_3422_ = 0usize;
                v___x_3423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3(v_sz_3421_, v___x_3422_, v___y_3420_);
                if lean_obj_tag(v___x_3423_) == 0 {
                    v___x_3424_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                    v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
                    v_isSharedCheck_3432_ = (!lean_is_exclusive(v___x_3424_)) as u8;
                    if v_isSharedCheck_3432_ == 0 {
                        v___x_3427_ = v___x_3424_;
                        v_isShared_3428_ = v_isSharedCheck_3432_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3425_);
                        lean_dec(v___x_3424_);
                        v___x_3427_ = lean_box(0);
                        v_isShared_3428_ = v_isSharedCheck_3432_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_3433_ = lean_ctor_get(v___x_3423_, 0);
                    lean_inc(v_val_3433_);
                    lean_dec_ref_known(v___x_3423_, 1);
                    v___x_3434_ = l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__1;
                    v_sz_3435_ = lean_array_size(v_val_3433_);
                    v___x_3436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(v_val_3433_, v_sz_3435_, v___x_3422_, v___x_3434_);
                    lean_dec(v_val_3433_);
                    if lean_obj_tag(v___x_3436_) == 0 {
                        v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
                        lean_inc(v_a_3437_);
                        lean_dec_ref_known(v___x_3436_, 1);
                        v_fst_3438_ = lean_ctor_get(v_a_3437_, 0);
                        lean_inc(v_fst_3438_);
                        v_snd_3439_ = lean_ctor_get(v_a_3437_, 1);
                        lean_inc(v_snd_3439_);
                        lean_dec(v_a_3437_);
                        v_omitFields_3413_ = v_fst_3438_;
                        v_handlers_3414_ = v_snd_3439_;
                        state = 1;
                        continue;
                    } else {
                        v_a_3440_ = lean_ctor_get(v___x_3436_, 0);
                        v_isSharedCheck_3447_ = (!lean_is_exclusive(v___x_3436_)) as u8;
                        if v_isSharedCheck_3447_ == 0 {
                            v___x_3442_ = v___x_3436_;
                            v_isShared_3443_ = v_isSharedCheck_3447_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3440_);
                            lean_dec(v___x_3436_);
                            v___x_3442_ = lean_box(0);
                            v_isShared_3443_ = v_isSharedCheck_3447_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_3428_ == 0 {
                    v___x_3430_ = v___x_3427_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
                    v___x_3430_ = v_reuseFailAlloc_3431_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3430_;
            }
            5 => {
                if v_isShared_3443_ == 0 {
                    v___x_3445_ = v___x_3442_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
                    v___x_3445_ = v_reuseFailAlloc_3446_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3445_;
            }
            7 => {
                if v_isShared_3455_ == 0 {
                    v___x_3457_ = v___x_3454_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
                    v___x_3457_ = v_reuseFailAlloc_3458_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3457_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_mkEvalConfigItemView___boxed(
    mut v_entries_x3f_3477_: *mut LeanObject,
    mut v_a_3478_: *mut LeanObject,
    mut v_a_3479_: *mut LeanObject,
    mut v_a_3480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3481_: *mut LeanObject = core::ptr::null_mut();
    v_res_3481_ =
        l_Lean_Elab_ConfigEval_mkEvalConfigItemView(v_entries_x3f_3477_, v_a_3478_, v_a_3479_);
    lean_dec(v_a_3479_);
    lean_dec_ref(v_a_3478_);
    return v_res_3481_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4(
    mut v_as_3482_: *mut LeanObject,
    mut v_sz_3483_: usize,
    mut v_i_3484_: usize,
    mut v_b_3485_: *mut LeanObject,
    mut v___y_3486_: *mut LeanObject,
    mut v___y_3487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    v___x_3489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(v_as_3482_, v_sz_3483_, v_i_3484_, v_b_3485_);
    return v___x_3489_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___boxed(
    mut v_as_3490_: *mut LeanObject,
    mut v_sz_3491_: *mut LeanObject,
    mut v_i_3492_: *mut LeanObject,
    mut v_b_3493_: *mut LeanObject,
    mut v___y_3494_: *mut LeanObject,
    mut v___y_3495_: *mut LeanObject,
    mut v___y_3496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3497_: usize = 0;
    let mut v_i_boxed_3498_: usize = 0;
    let mut v_res_3499_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3497_ = lean_unbox_usize(v_sz_3491_);
    lean_dec(v_sz_3491_);
    v_i_boxed_3498_ = lean_unbox_usize(v_i_3492_);
    lean_dec(v_i_3492_);
    v_res_3499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4(v_as_3490_, v_sz_boxed_3497_, v_i_boxed_3498_, v_b_3493_, v___y_3494_, v___y_3495_);
    lean_dec(v___y_3495_);
    lean_dec_ref(v___y_3494_);
    lean_dec_ref(v_as_3490_);
    return v_res_3499_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd(
    mut v_x_3513_: *mut LeanObject,
    mut v_a_3514_: *mut LeanObject,
    mut v_a_3515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_x3f_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binders_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3535_: u8 = 0;
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3539_: u8 = 0;
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: u8 = 0;
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vis_x3f_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: u8 = 0;
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: u8 = 0;
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: u8 = 0;
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: u8 = 0;
    let mut v___x_3571_: u8 = 0;
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_x3f_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: u8 = 0;
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: u8 = 0;
    let mut v___x_3586_: u8 = 0;
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vis_x3f_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: u8 = 0;
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: u8 = 0;
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: u8 = 0;
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3540_ = l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1;
                lean_inc(v_x_3513_);
                v___x_3541_ = l_Lean_Syntax_isOfKind(v_x_3513_, v___x_3540_);
                if v___x_3541_ == 0 {
                    lean_dec(v_x_3513_);
                    v___x_3542_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                    return v___x_3542_;
                } else {
                    v___x_3543_ = lean_unsigned_to_nat(0);
                    v___x_3591_ = l_Lean_Syntax_getArg(v_x_3513_, v___x_3543_);
                    v___x_3592_ = l_Lean_Syntax_isNone(v___x_3591_);
                    if v___x_3592_ == 0 {
                        v___x_3593_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_3591_);
                        v___x_3594_ = l_Lean_Syntax_matchesNull(v___x_3591_, v___x_3593_);
                        if v___x_3594_ == 0 {
                            lean_dec(v___x_3591_);
                            lean_dec(v_x_3513_);
                            v___x_3595_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                            return v___x_3595_;
                        } else {
                            v_doc_x3f_3596_ = l_Lean_Syntax_getArg(v___x_3591_, v___x_3543_);
                            lean_dec(v___x_3591_);
                            v___x_3597_ =
                                l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4;
                            lean_inc(v_doc_x3f_3596_);
                            v___x_3598_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3596_, v___x_3597_);
                            if v___x_3598_ == 0 {
                                lean_dec(v_doc_x3f_3596_);
                                lean_dec(v_x_3513_);
                                v___x_3599_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                                return v___x_3599_;
                            } else {
                                v___x_3600_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3600_, 0, v_doc_x3f_3596_);
                                v_doc_x3f_3580_ = v___x_3600_;
                                v___y_3581_ = v_a_3514_;
                                v___y_3582_ = v_a_3515_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_3591_);
                        v___x_3601_ = lean_box(0);
                        v_doc_x3f_3580_ = v___x_3601_;
                        v___y_3581_ = v_a_3514_;
                        v___y_3582_ = v_a_3515_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3528_ = l_Lean_Elab_ConfigEval_mkEvalConfigItemView(
                    v_entries_x3f_3525_,
                    v___y_3526_,
                    v___y_3527_,
                );
                if lean_obj_tag(v___x_3528_) == 0 {
                    v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
                    lean_inc(v_a_3529_);
                    lean_dec_ref_known(v___x_3528_, 1);
                    v_binders_3530_ = l_Lean_Syntax_getArgs(v___y_3521_);
                    lean_dec(v___y_3521_);
                    v___x_3531_ = l_Lean_Elab_ConfigEval_defEvalConfigItem(
                        v___y_3524_,
                        v___y_3518_,
                        v___y_3522_,
                        v___y_3520_,
                        v___y_3519_,
                        v___y_3523_,
                        v_binders_3530_,
                        v_a_3529_,
                        v___y_3526_,
                        v___y_3527_,
                    );
                    return v___x_3531_;
                } else {
                    lean_dec(v___y_3524_);
                    lean_dec(v___y_3523_);
                    lean_dec(v___y_3522_);
                    lean_dec(v___y_3521_);
                    lean_dec(v___y_3520_);
                    lean_dec(v___y_3519_);
                    lean_dec(v___y_3518_);
                    v_a_3532_ = lean_ctor_get(v___x_3528_, 0);
                    v_isSharedCheck_3539_ = (!lean_is_exclusive(v___x_3528_)) as u8;
                    if v_isSharedCheck_3539_ == 0 {
                        v___x_3534_ = v___x_3528_;
                        v_isShared_3535_ = v_isSharedCheck_3539_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3532_);
                        lean_dec(v___x_3528_);
                        v___x_3534_ = lean_box(0);
                        v_isShared_3535_ = v_isSharedCheck_3539_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3535_ == 0 {
                    v___x_3537_ = v___x_3534_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
                    v___x_3537_ = v_reuseFailAlloc_3538_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3537_;
            }
            4 => {
                v___x_3550_ = lean_unsigned_to_nat(2);
                v_kind_3551_ = l_Lean_Syntax_getArg(v_x_3513_, v___x_3550_);
                v___x_3552_ = l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4;
                lean_inc(v_kind_3551_);
                v___x_3553_ = l_Lean_Syntax_isOfKind(v_kind_3551_, v___x_3552_);
                if v___x_3553_ == 0 {
                    lean_dec(v_kind_3551_);
                    lean_dec(v_vis_x3f_3547_);
                    lean_dec(v___y_3546_);
                    lean_dec(v_x_3513_);
                    v___x_3554_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                    return v___x_3554_;
                } else {
                    v___x_3555_ = lean_unsigned_to_nat(4);
                    v_fn_3556_ = l_Lean_Syntax_getArg(v_x_3513_, v___x_3555_);
                    v___x_3557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13;
                    lean_inc(v_fn_3556_);
                    v___x_3558_ = l_Lean_Syntax_isOfKind(v_fn_3556_, v___x_3557_);
                    if v___x_3558_ == 0 {
                        lean_dec(v_fn_3556_);
                        lean_dec(v_kind_3551_);
                        lean_dec(v_vis_x3f_3547_);
                        lean_dec(v___y_3546_);
                        lean_dec(v_x_3513_);
                        v___x_3559_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                        return v___x_3559_;
                    } else {
                        v___x_3560_ = lean_unsigned_to_nat(7);
                        v_struct_3561_ = l_Lean_Syntax_getArg(v_x_3513_, v___x_3560_);
                        lean_inc(v_struct_3561_);
                        v___x_3562_ = l_Lean_Syntax_isOfKind(v_struct_3561_, v___x_3557_);
                        if v___x_3562_ == 0 {
                            lean_dec(v_struct_3561_);
                            lean_dec(v_fn_3556_);
                            lean_dec(v_kind_3551_);
                            lean_dec(v_vis_x3f_3547_);
                            lean_dec(v___y_3546_);
                            lean_dec(v_x_3513_);
                            v___x_3563_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                            return v___x_3563_;
                        } else {
                            v___x_3564_ = lean_unsigned_to_nat(3);
                            v_tk_3565_ = l_Lean_Syntax_getArg(v_x_3513_, v___x_3564_);
                            v___x_3566_ = lean_unsigned_to_nat(5);
                            v___x_3567_ = l_Lean_Syntax_getArg(v_x_3513_, v___x_3566_);
                            v___x_3568_ = lean_unsigned_to_nat(8);
                            v___x_3569_ = l_Lean_Syntax_getArg(v_x_3513_, v___x_3568_);
                            lean_dec(v_x_3513_);
                            v___x_3570_ = l_Lean_Syntax_isNone(v___x_3569_);
                            if v___x_3570_ == 0 {
                                lean_inc(v___x_3569_);
                                v___x_3571_ = l_Lean_Syntax_matchesNull(v___x_3569_, v___y_3545_);
                                if v___x_3571_ == 0 {
                                    lean_dec(v___x_3569_);
                                    lean_dec(v___x_3567_);
                                    lean_dec(v_tk_3565_);
                                    lean_dec(v_struct_3561_);
                                    lean_dec(v_fn_3556_);
                                    lean_dec(v_kind_3551_);
                                    lean_dec(v_vis_x3f_3547_);
                                    lean_dec(v___y_3546_);
                                    v___x_3572_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                                    return v___x_3572_;
                                } else {
                                    v_entries_x3f_3573_ =
                                        l_Lean_Syntax_getArg(v___x_3569_, v___x_3543_);
                                    lean_dec(v___x_3569_);
                                    v___x_3574_ =
                                        l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3;
                                    lean_inc(v_entries_x3f_3573_);
                                    v___x_3575_ =
                                        l_Lean_Syntax_isOfKind(v_entries_x3f_3573_, v___x_3574_);
                                    if v___x_3575_ == 0 {
                                        lean_dec(v_entries_x3f_3573_);
                                        lean_dec(v___x_3567_);
                                        lean_dec(v_tk_3565_);
                                        lean_dec(v_struct_3561_);
                                        lean_dec(v_fn_3556_);
                                        lean_dec(v_kind_3551_);
                                        lean_dec(v_vis_x3f_3547_);
                                        lean_dec(v___y_3546_);
                                        v___x_3576_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                                        return v___x_3576_;
                                    } else {
                                        v___x_3577_ = lean_alloc_ctor(1, 1, (0) as u32);
                                        lean_ctor_set(v___x_3577_, 0, v_entries_x3f_3573_);
                                        v___y_3518_ = v_vis_x3f_3547_;
                                        v___y_3519_ = v_struct_3561_;
                                        v___y_3520_ = v_tk_3565_;
                                        v___y_3521_ = v___x_3567_;
                                        v___y_3522_ = v_kind_3551_;
                                        v___y_3523_ = v_fn_3556_;
                                        v___y_3524_ = v___y_3546_;
                                        v_entries_x3f_3525_ = v___x_3577_;
                                        v___y_3526_ = v___y_3548_;
                                        v___y_3527_ = v___y_3549_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v___x_3569_);
                                v___x_3578_ = lean_box(0);
                                v___y_3518_ = v_vis_x3f_3547_;
                                v___y_3519_ = v_struct_3561_;
                                v___y_3520_ = v_tk_3565_;
                                v___y_3521_ = v___x_3567_;
                                v___y_3522_ = v_kind_3551_;
                                v___y_3523_ = v_fn_3556_;
                                v___y_3524_ = v___y_3546_;
                                v_entries_x3f_3525_ = v___x_3578_;
                                v___y_3526_ = v___y_3548_;
                                v___y_3527_ = v___y_3549_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            5 => {
                v___x_3583_ = lean_unsigned_to_nat(1);
                v___x_3584_ = l_Lean_Syntax_getArg(v_x_3513_, v___x_3583_);
                v___x_3585_ = l_Lean_Syntax_isNone(v___x_3584_);
                if v___x_3585_ == 0 {
                    lean_inc(v___x_3584_);
                    v___x_3586_ = l_Lean_Syntax_matchesNull(v___x_3584_, v___x_3583_);
                    if v___x_3586_ == 0 {
                        lean_dec(v___x_3584_);
                        lean_dec(v_doc_x3f_3580_);
                        lean_dec(v_x_3513_);
                        v___x_3587_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
                        return v___x_3587_;
                    } else {
                        v_vis_x3f_3588_ = l_Lean_Syntax_getArg(v___x_3584_, v___x_3543_);
                        lean_dec(v___x_3584_);
                        v___x_3589_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3589_, 0, v_vis_x3f_3588_);
                        v___y_3545_ = v___x_3583_;
                        v___y_3546_ = v_doc_x3f_3580_;
                        v_vis_x3f_3547_ = v___x_3589_;
                        v___y_3548_ = v___y_3581_;
                        v___y_3549_ = v___y_3582_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3584_);
                    v___x_3590_ = lean_box(0);
                    v___y_3545_ = v___x_3583_;
                    v___y_3546_ = v_doc_x3f_3580_;
                    v_vis_x3f_3547_ = v___x_3590_;
                    v___y_3548_ = v___y_3581_;
                    v___y_3549_ = v___y_3582_;
                    state = 4;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___boxed(
    mut v_x_3602_: *mut LeanObject,
    mut v_a_3603_: *mut LeanObject,
    mut v_a_3604_: *mut LeanObject,
    mut v_a_3605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3606_: *mut LeanObject = core::ptr::null_mut();
    v_res_3606_ = l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd(v_x_3602_, v_a_3603_, v_a_3604_);
    lean_dec(v_a_3604_);
    lean_dec_ref(v_a_3603_);
    return v_res_3606_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1()
-> *mut LeanObject {
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    v___x_3614_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_3615_ = l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1;
    v___x_3616_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1;
    v___x_3617_ = lean_alloc_closure(
        l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_3618_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3614_,
        v___x_3615_,
        v___x_3616_,
        v___x_3617_,
    );
    return v___x_3618_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___boxed(
    mut v_a_3619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3620_: *mut LeanObject = core::ptr::null_mut();
    v_res_3620_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1();
    return v_res_3620_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd(
    mut v_a_3622_: *mut LeanObject,
    mut v_a_3623_: *mut LeanObject,
    mut v_a_3624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    v___x_3626_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0;
    v___x_3627_ = lean_unsigned_to_nat(2);
    v___x_3628_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(
        v___x_3626_,
        v___x_3627_,
        v_a_3622_,
        v_a_3623_,
        v_a_3624_,
    );
    return v___x_3628_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___boxed(
    mut v_a_3629_: *mut LeanObject,
    mut v_a_3630_: *mut LeanObject,
    mut v_a_3631_: *mut LeanObject,
    mut v_a_3632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3633_: *mut LeanObject = core::ptr::null_mut();
    v_res_3633_ =
        l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd(
            v_a_3629_, v_a_3630_, v_a_3631_,
        );
    lean_dec(v_a_3631_);
    lean_dec_ref(v_a_3630_);
    lean_dec(v_a_3629_);
    return v_res_3633_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0()
-> *mut LeanObject {
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    v___x_3634_ = lean_alloc_closure(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___boxed as *mut core::ffi::c_void, 4, 0);
    v___x_3635_ = lean_alloc_closure(
        l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_3635_, 0, v___x_3634_);
    return v___x_3635_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1()
-> *mut LeanObject {
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    v___x_3637_ = l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1;
    v___x_3638_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0_once), _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0);
    v___x_3639_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3637_, v___x_3638_);
    return v___x_3639_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___boxed(
    mut v_a_3640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3641_: *mut LeanObject = core::ptr::null_mut();
    v_res_3641_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1();
    return v_res_3641_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(
    mut v_sz_3642_: usize,
    mut v_i_3643_: usize,
    mut v_bs_3644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3645_: u8 = 0;
    let mut v_v_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: usize = 0;
    let mut v___x_3650_: usize = 0;
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3645_ = lean_usize_dec_lt(v_i_3643_, v_sz_3642_);
                if v___x_3645_ == 0 {
                    return v_bs_3644_;
                } else {
                    v_v_3646_ = lean_array_uget(v_bs_3644_, v_i_3643_);
                    v___x_3647_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3648_ = lean_array_uset(v_bs_3644_, v_i_3643_, v___x_3647_);
                    v___x_3649_ = 1usize;
                    v___x_3650_ = lean_usize_add(v_i_3643_, v___x_3649_);
                    v___x_3651_ = lean_array_uset(v_bs_x27_3648_, v_i_3643_, v_v_3646_);
                    v_i_3643_ = v___x_3650_;
                    v_bs_3644_ = v___x_3651_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0___boxed(
    mut v_sz_3653_: *mut LeanObject,
    mut v_i_3654_: *mut LeanObject,
    mut v_bs_3655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3656_: usize = 0;
    let mut v_i_boxed_3657_: usize = 0;
    let mut v_res_3658_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3656_ = lean_unbox_usize(v_sz_3653_);
    lean_dec(v_sz_3653_);
    v_i_boxed_3657_ = lean_unbox_usize(v_i_3654_);
    lean_dec(v_i_3654_);
    v_res_3658_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_boxed_3656_, v_i_boxed_3657_, v_bs_3655_);
    return v_res_3658_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs(
    mut v_stx_3684_: *mut LeanObject,
    mut v_a_3685_: *mut LeanObject,
    mut v_a_3686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: u8 = 0;
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: u8 = 0;
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: u8 = 0;
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: u8 = 0;
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: u8 = 0;
    let mut v___x_3702_: u8 = 0;
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: u8 = 0;
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: u8 = 0;
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3725_: usize = 0;
    let mut v___x_3726_: usize = 0;
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3734_: usize = 0;
    let mut v___x_3735_: usize = 0;
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: u8 = 0;
    let mut v___x_3741_: u8 = 0;
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3749_: usize = 0;
    let mut v___x_3750_: usize = 0;
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: u8 = 0;
    let mut v___x_3756_: u8 = 0;
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3687_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1;
                lean_inc(v_stx_3684_);
                v___x_3688_ = l_Lean_Syntax_isOfKind(v_stx_3684_, v___x_3687_);
                if v___x_3688_ == 0 {
                    v___x_3689_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3;
                    lean_inc(v_stx_3684_);
                    v___x_3690_ = l_Lean_Syntax_isOfKind(v_stx_3684_, v___x_3689_);
                    if v___x_3690_ == 0 {
                        v___x_3691_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5;
                        lean_inc(v_stx_3684_);
                        v___x_3692_ = l_Lean_Syntax_isOfKind(v_stx_3684_, v___x_3691_);
                        if v___x_3692_ == 0 {
                            v___x_3693_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7;
                            lean_inc(v_stx_3684_);
                            v___x_3694_ = l_Lean_Syntax_isOfKind(v_stx_3684_, v___x_3693_);
                            if v___x_3694_ == 0 {
                                v___x_3695_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8;
                                v___x_3696_ = l_Lean_Macro_throwErrorAt___redArg(
                                    v_stx_3684_,
                                    v___x_3695_,
                                    v_a_3685_,
                                    v_a_3686_,
                                );
                                lean_dec(v_stx_3684_);
                                return v___x_3696_;
                            } else {
                                v___x_3697_ = lean_unsigned_to_nat(0);
                                v___x_3698_ = lean_unsigned_to_nat(1);
                                v___x_3699_ = l_Lean_Syntax_getArg(v_stx_3684_, v___x_3698_);
                                v___x_3700_ = lean_unsigned_to_nat(2);
                                lean_inc(v___x_3699_);
                                v___x_3701_ = l_Lean_Syntax_matchesNull(v___x_3699_, v___x_3700_);
                                if v___x_3701_ == 0 {
                                    v___x_3702_ =
                                        l_Lean_Syntax_matchesNull(v___x_3699_, v___x_3697_);
                                    if v___x_3702_ == 0 {
                                        v___x_3703_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8;
                                        v___x_3704_ = l_Lean_Macro_throwErrorAt___redArg(
                                            v_stx_3684_,
                                            v___x_3703_,
                                            v_a_3685_,
                                            v_a_3686_,
                                        );
                                        lean_dec(v_stx_3684_);
                                        return v___x_3704_;
                                    } else {
                                        v___x_3705_ = l_Lean_mkHole(v_stx_3684_, v___x_3701_);
                                        lean_dec(v_stx_3684_);
                                        v___x_3706_ =
                                            lean_mk_empty_array_with_capacity(v___x_3698_);
                                        v___x_3707_ = lean_array_push(v___x_3706_, v___x_3705_);
                                        v___x_3708_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v___x_3708_, 0, v___x_3707_);
                                        lean_ctor_set(v___x_3708_, 1, v_a_3686_);
                                        return v___x_3708_;
                                    }
                                } else {
                                    v___x_3709_ = l_Lean_Syntax_getArg(v___x_3699_, v___x_3697_);
                                    lean_dec(v___x_3699_);
                                    v___x_3710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13;
                                    lean_inc(v___x_3709_);
                                    v___x_3711_ = l_Lean_Syntax_isOfKind(v___x_3709_, v___x_3710_);
                                    if v___x_3711_ == 0 {
                                        lean_dec(v___x_3709_);
                                        v___x_3712_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8;
                                        v___x_3713_ = l_Lean_Macro_throwErrorAt___redArg(
                                            v_stx_3684_,
                                            v___x_3712_,
                                            v_a_3685_,
                                            v_a_3686_,
                                        );
                                        lean_dec(v_stx_3684_);
                                        return v___x_3713_;
                                    } else {
                                        lean_dec(v_stx_3684_);
                                        v___x_3714_ =
                                            lean_mk_empty_array_with_capacity(v___x_3698_);
                                        v___x_3715_ = lean_array_push(v___x_3714_, v___x_3709_);
                                        v___x_3716_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v___x_3716_, 0, v___x_3715_);
                                        lean_ctor_set(v___x_3716_, 1, v_a_3686_);
                                        return v___x_3716_;
                                    }
                                }
                            }
                        } else {
                            v___x_3717_ = lean_unsigned_to_nat(2);
                            v___x_3718_ = l_Lean_Syntax_getArg(v_stx_3684_, v___x_3717_);
                            v___x_3719_ = l_Lean_Syntax_matchesNull(v___x_3718_, v___x_3717_);
                            if v___x_3719_ == 0 {
                                v___x_3720_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8;
                                v___x_3721_ = l_Lean_Macro_throwErrorAt___redArg(
                                    v_stx_3684_,
                                    v___x_3720_,
                                    v_a_3685_,
                                    v_a_3686_,
                                );
                                lean_dec(v_stx_3684_);
                                return v___x_3721_;
                            } else {
                                v___x_3722_ = lean_unsigned_to_nat(1);
                                v___x_3723_ = l_Lean_Syntax_getArg(v_stx_3684_, v___x_3722_);
                                lean_dec(v_stx_3684_);
                                v_ids_3724_ = l_Lean_Syntax_getArgs(v___x_3723_);
                                lean_dec(v___x_3723_);
                                v_sz_3725_ = lean_array_size(v_ids_3724_);
                                v___x_3726_ = 0usize;
                                v___x_3727_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_3725_, v___x_3726_, v_ids_3724_);
                                v___x_3728_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_3728_, 0, v___x_3727_);
                                lean_ctor_set(v___x_3728_, 1, v_a_3686_);
                                return v___x_3728_;
                            }
                        }
                    } else {
                        v___x_3729_ = lean_unsigned_to_nat(1);
                        v___x_3730_ = l_Lean_Syntax_getArg(v_stx_3684_, v___x_3729_);
                        v___x_3738_ = lean_unsigned_to_nat(2);
                        v___x_3739_ = l_Lean_Syntax_getArg(v_stx_3684_, v___x_3738_);
                        v___x_3740_ = l_Lean_Syntax_isNone(v___x_3739_);
                        if v___x_3740_ == 0 {
                            v___x_3741_ = l_Lean_Syntax_matchesNull(v___x_3739_, v___x_3738_);
                            if v___x_3741_ == 0 {
                                lean_dec(v___x_3730_);
                                v___x_3742_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8;
                                v___x_3743_ = l_Lean_Macro_throwErrorAt___redArg(
                                    v_stx_3684_,
                                    v___x_3742_,
                                    v_a_3685_,
                                    v_a_3686_,
                                );
                                lean_dec(v_stx_3684_);
                                return v___x_3743_;
                            } else {
                                lean_dec(v_stx_3684_);
                                v___y_3732_ = v_a_3686_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_3739_);
                            lean_dec(v_stx_3684_);
                            v___y_3732_ = v_a_3686_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_3744_ = lean_unsigned_to_nat(1);
                    v___x_3745_ = l_Lean_Syntax_getArg(v_stx_3684_, v___x_3744_);
                    v___x_3753_ = lean_unsigned_to_nat(2);
                    v___x_3754_ = l_Lean_Syntax_getArg(v_stx_3684_, v___x_3753_);
                    v___x_3755_ = l_Lean_Syntax_isNone(v___x_3754_);
                    if v___x_3755_ == 0 {
                        v___x_3756_ = l_Lean_Syntax_matchesNull(v___x_3754_, v___x_3753_);
                        if v___x_3756_ == 0 {
                            lean_dec(v___x_3745_);
                            v___x_3757_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8;
                            v___x_3758_ = l_Lean_Macro_throwErrorAt___redArg(
                                v_stx_3684_,
                                v___x_3757_,
                                v_a_3685_,
                                v_a_3686_,
                            );
                            lean_dec(v_stx_3684_);
                            return v___x_3758_;
                        } else {
                            lean_dec(v_stx_3684_);
                            v___y_3747_ = v_a_3686_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3754_);
                        lean_dec(v_stx_3684_);
                        v___y_3747_ = v_a_3686_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v_ids_3733_ = l_Lean_Syntax_getArgs(v___x_3730_);
                lean_dec(v___x_3730_);
                v_sz_3734_ = lean_array_size(v_ids_3733_);
                v___x_3735_ = 0usize;
                v___x_3736_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_3734_, v___x_3735_, v_ids_3733_);
                v___x_3737_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3737_, 0, v___x_3736_);
                lean_ctor_set(v___x_3737_, 1, v___y_3732_);
                return v___x_3737_;
            }
            2 => {
                v_ids_3748_ = l_Lean_Syntax_getArgs(v___x_3745_);
                lean_dec(v___x_3745_);
                v_sz_3749_ = lean_array_size(v_ids_3748_);
                v___x_3750_ = 0usize;
                v___x_3751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_3749_, v___x_3750_, v_ids_3748_);
                v___x_3752_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3752_, 0, v___x_3751_);
                lean_ctor_set(v___x_3752_, 1, v___y_3747_);
                return v___x_3752_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___boxed(
    mut v_stx_3759_: *mut LeanObject,
    mut v_a_3760_: *mut LeanObject,
    mut v_a_3761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3762_: *mut LeanObject = core::ptr::null_mut();
    v_res_3762_ =
        l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs(
            v_stx_3759_,
            v_a_3760_,
            v_a_3761_,
        );
    lean_dec_ref(v_a_3760_);
    return v_res_3762_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(
    mut v_as_3763_: *mut LeanObject,
    mut v_i_3764_: usize,
    mut v_stop_3765_: usize,
    mut v_b_3766_: *mut LeanObject,
    mut v___y_3767_: *mut LeanObject,
    mut v___y_3768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: usize = 0;
    let mut v___x_3773_: usize = 0;
    let mut v___x_3775_: u8 = 0;
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3775_ = lean_usize_dec_eq(v_i_3764_, v_stop_3765_);
                if v___x_3775_ == 0 {
                    v___x_3776_ = lean_array_uget_borrowed(v_as_3763_, v_i_3764_);
                    lean_inc(v___x_3776_);
                    v___x_3777_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs(v___x_3776_, v___y_3767_, v___y_3768_);
                    if lean_obj_tag(v___x_3777_) == 0 {
                        v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
                        lean_inc(v_a_3778_);
                        v_a_3779_ = lean_ctor_get(v___x_3777_, 1);
                        lean_inc(v_a_3779_);
                        lean_dec_ref_known(v___x_3777_, 2);
                        v___x_3780_ = l_Array_append___redArg(v_b_3766_, v_a_3778_);
                        lean_dec(v_a_3778_);
                        v_a_3770_ = v___x_3780_;
                        v_a_3771_ = v_a_3779_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_b_3766_);
                        if lean_obj_tag(v___x_3777_) == 0 {
                            v_a_3781_ = lean_ctor_get(v___x_3777_, 0);
                            lean_inc(v_a_3781_);
                            v_a_3782_ = lean_ctor_get(v___x_3777_, 1);
                            lean_inc(v_a_3782_);
                            lean_dec_ref_known(v___x_3777_, 2);
                            v_a_3770_ = v_a_3781_;
                            v_a_3771_ = v_a_3782_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_3777_;
                        }
                    }
                } else {
                    v___x_3783_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3783_, 0, v_b_3766_);
                    lean_ctor_set(v___x_3783_, 1, v___y_3768_);
                    return v___x_3783_;
                }
            }
            1 => {
                v___x_3772_ = 1usize;
                v___x_3773_ = lean_usize_add(v_i_3764_, v___x_3772_);
                v_i_3764_ = v___x_3773_;
                v_b_3766_ = v_a_3770_;
                v___y_3768_ = v_a_3771_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3___boxed(
    mut v_as_3784_: *mut LeanObject,
    mut v_i_3785_: *mut LeanObject,
    mut v_stop_3786_: *mut LeanObject,
    mut v_b_3787_: *mut LeanObject,
    mut v___y_3788_: *mut LeanObject,
    mut v___y_3789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3790_: usize = 0;
    let mut v_stop_boxed_3791_: usize = 0;
    let mut v_res_3792_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3790_ = lean_unbox_usize(v_i_3785_);
    lean_dec(v_i_3785_);
    v_stop_boxed_3791_ = lean_unbox_usize(v_stop_3786_);
    lean_dec(v_stop_3786_);
    v_res_3792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(v_as_3784_, v_i_boxed_3790_, v_stop_boxed_3791_, v_b_3787_, v___y_3788_, v___y_3789_);
    lean_dec_ref(v___y_3788_);
    lean_dec_ref(v_as_3784_);
    return v_res_3792_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2(
    mut v_sz_3793_: usize,
    mut v_i_3794_: usize,
    mut v_bs_3795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3796_: u8 = 0;
    let mut v_v_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: usize = 0;
    let mut v___x_3801_: usize = 0;
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3796_ = lean_usize_dec_lt(v_i_3794_, v_sz_3793_);
                if v___x_3796_ == 0 {
                    return v_bs_3795_;
                } else {
                    v_v_3797_ = lean_array_uget(v_bs_3795_, v_i_3794_);
                    v___x_3798_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3799_ = lean_array_uset(v_bs_3795_, v_i_3794_, v___x_3798_);
                    v___x_3800_ = 1usize;
                    v___x_3801_ = lean_usize_add(v_i_3794_, v___x_3800_);
                    v___x_3802_ = lean_array_uset(v_bs_x27_3799_, v_i_3794_, v_v_3797_);
                    v_i_3794_ = v___x_3801_;
                    v_bs_3795_ = v___x_3802_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2___boxed(
    mut v_sz_3804_: *mut LeanObject,
    mut v_i_3805_: *mut LeanObject,
    mut v_bs_3806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3807_: usize = 0;
    let mut v_i_boxed_3808_: usize = 0;
    let mut v_res_3809_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3807_ = lean_unbox_usize(v_sz_3804_);
    lean_dec(v_sz_3804_);
    v_i_boxed_3808_ = lean_unbox_usize(v_i_3805_);
    lean_dec(v_i_3805_);
    v_res_3809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2(v_sz_boxed_3807_, v_i_boxed_3808_, v_bs_3806_);
    return v_res_3809_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(
    mut v_sz_3810_: usize,
    mut v_i_3811_: usize,
    mut v_bs_3812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3813_: u8 = 0;
    let mut v_v_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: usize = 0;
    let mut v___x_3818_: usize = 0;
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3813_ = lean_usize_dec_lt(v_i_3811_, v_sz_3810_);
                if v___x_3813_ == 0 {
                    return v_bs_3812_;
                } else {
                    v_v_3814_ = lean_array_uget(v_bs_3812_, v_i_3811_);
                    v___x_3815_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3816_ = lean_array_uset(v_bs_3812_, v_i_3811_, v___x_3815_);
                    v___x_3817_ = 1usize;
                    v___x_3818_ = lean_usize_add(v_i_3811_, v___x_3817_);
                    v___x_3819_ = lean_array_uset(v_bs_x27_3816_, v_i_3811_, v_v_3814_);
                    v_i_3811_ = v___x_3818_;
                    v_bs_3812_ = v___x_3819_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0___boxed(
    mut v_sz_3821_: *mut LeanObject,
    mut v_i_3822_: *mut LeanObject,
    mut v_bs_3823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3824_: usize = 0;
    let mut v_i_boxed_3825_: usize = 0;
    let mut v_res_3826_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3824_ = lean_unbox_usize(v_sz_3821_);
    lean_dec(v_sz_3821_);
    v_i_boxed_3825_ = lean_unbox_usize(v_i_3822_);
    lean_dec(v_i_3822_);
    v_res_3826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(v_sz_boxed_3824_, v_i_boxed_3825_, v_bs_3823_);
    return v_res_3826_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1(
    mut v_sz_3827_: usize,
    mut v_i_3828_: usize,
    mut v_bs_3829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3830_: u8 = 0;
    let mut v_v_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: usize = 0;
    let mut v___x_3835_: usize = 0;
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3830_ = lean_usize_dec_lt(v_i_3828_, v_sz_3827_);
                if v___x_3830_ == 0 {
                    return v_bs_3829_;
                } else {
                    v_v_3831_ = lean_array_uget(v_bs_3829_, v_i_3828_);
                    v___x_3832_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3833_ = lean_array_uset(v_bs_3829_, v_i_3828_, v___x_3832_);
                    v___x_3834_ = 1usize;
                    v___x_3835_ = lean_usize_add(v_i_3828_, v___x_3834_);
                    v___x_3836_ = lean_array_uset(v_bs_x27_3833_, v_i_3828_, v_v_3831_);
                    v_i_3828_ = v___x_3835_;
                    v_bs_3829_ = v___x_3836_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1___boxed(
    mut v_sz_3838_: *mut LeanObject,
    mut v_i_3839_: *mut LeanObject,
    mut v_bs_3840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3841_: usize = 0;
    let mut v_i_boxed_3842_: usize = 0;
    let mut v_res_3843_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3841_ = lean_unbox_usize(v_sz_3838_);
    lean_dec(v_sz_3838_);
    v_i_boxed_3842_ = lean_unbox_usize(v_i_3839_);
    lean_dec(v_i_3839_);
    v_res_3843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1(v_sz_boxed_3841_, v_i_boxed_3842_, v_bs_3840_);
    return v_res_3843_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7()
-> *mut LeanObject {
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    v___x_3852_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__6;
    v___x_3853_ = l_String_toRawSubstring_x27(v___x_3852_);
    return v___x_3853_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26()
-> *mut LeanObject {
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    v___x_3893_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25;
    v___x_3894_ = l_String_toRawSubstring_x27(v___x_3893_);
    return v___x_3894_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__53()
-> *mut LeanObject {
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    v___x_3963_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__52;
    v___x_3964_ = l_String_toRawSubstring_x27(v___x_3963_);
    return v___x_3964_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56()
-> *mut LeanObject {
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    v___x_3967_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__55;
    v___x_3968_ = l_String_toRawSubstring_x27(v___x_3967_);
    return v___x_3968_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59()
-> *mut LeanObject {
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    v___x_3972_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__58;
    v___x_3973_ = l_String_toRawSubstring_x27(v___x_3972_);
    return v___x_3973_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74()
-> *mut LeanObject {
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    v___x_4004_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__73;
    v___x_4005_ = lean_mk_syntax_ident(v___x_4004_);
    return v___x_4005_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__77()
-> *mut LeanObject {
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    v___x_4009_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__76;
    v___x_4010_ = lean_mk_syntax_ident(v___x_4009_);
    return v___x_4010_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__80()
-> *mut LeanObject {
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    v___x_4014_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__79;
    v___x_4015_ = lean_mk_syntax_ident(v___x_4014_);
    return v___x_4015_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__84()
-> *mut LeanObject {
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    v___x_4023_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83;
    v___x_4024_ = l_String_toRawSubstring_x27(v___x_4023_);
    return v___x_4024_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92()
-> *mut LeanObject {
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    v___x_4043_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__91;
    v___x_4044_ = l_String_toRawSubstring_x27(v___x_4043_);
    return v___x_4044_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98()
-> *mut LeanObject {
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    v___x_4055_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97;
    v___x_4056_ = l_String_toRawSubstring_x27(v___x_4055_);
    return v___x_4056_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102()
-> *mut LeanObject {
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    v___x_4061_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__72;
    v___x_4062_ = l_String_toRawSubstring_x27(v___x_4061_);
    return v___x_4062_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(
    mut v_monad_4080_: *mut LeanObject,
    mut v_mkMonadAdapt_4081_: *mut LeanObject,
    mut v_logExceptionsDefault_4082_: *mut LeanObject,
    mut v_mkLogExceptionsTerm_4083_: *mut LeanObject,
    mut v_doc_x3f_4084_: *mut LeanObject,
    mut v_vis_x3f_4085_: *mut LeanObject,
    mut v_tk_4086_: *mut LeanObject,
    mut v_elabName_4087_: *mut LeanObject,
    mut v_type_4088_: *mut LeanObject,
    mut v_binders_4089_: *mut LeanObject,
    mut v_entries_x3f_4090_: *mut LeanObject,
    mut v_a_4091_: *mut LeanObject,
    mut v_a_4092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4118_: usize = 0;
    let mut v___y_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4130_: usize = 0;
    let mut v___y_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4152_: usize = 0;
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4154_: usize = 0;
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4324_: usize = 0;
    let mut v___y_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4336_: usize = 0;
    let mut v___y_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4366_: usize = 0;
    let mut v___y_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4380_: usize = 0;
    let mut v___y_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4415_: u8 = 0;
    let mut v_quotContext_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: u8 = 0;
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4462_: u8 = 0;
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fnName_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4495_: usize = 0;
    let mut v___x_4496_: usize = 0;
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4506_: u8 = 0;
    let mut v_reuseFailAlloc_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4508_: u8 = 0;
    let mut v___y_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4517_: u8 = 0;
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4521_: u8 = 0;
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: u8 = 0;
    let mut v___x_4524_: u8 = 0;
    let mut v___x_4525_: usize = 0;
    let mut v___x_4526_: usize = 0;
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: usize = 0;
    let mut v___x_4529_: usize = 0;
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4093_ = lean_unsigned_to_nat(0);
                v___x_4094_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__0;
                v___x_4095_ = l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0;
                v___x_4096_ = l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1;
                v___x_4522_ = lean_array_get_size(v_binders_4089_);
                v___x_4523_ = lean_nat_dec_lt(v___x_4093_, v___x_4522_);
                if v___x_4523_ == 0 {
                    v_a_4406_ = v___x_4094_;
                    v_a_4407_ = v_a_4092_;
                    state = 4;
                    continue;
                } else {
                    v___x_4524_ = lean_nat_dec_le(v___x_4522_, v___x_4522_);
                    if v___x_4524_ == 0 {
                        if v___x_4523_ == 0 {
                            v_a_4406_ = v___x_4094_;
                            v_a_4407_ = v_a_4092_;
                            state = 4;
                            continue;
                        } else {
                            v___x_4525_ = 0usize;
                            v___x_4526_ = lean_usize_of_nat(v___x_4522_);
                            v___x_4527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(v_binders_4089_, v___x_4525_, v___x_4526_, v___x_4094_, v_a_4091_, v_a_4092_);
                            v___y_4510_ = v___x_4527_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v___x_4528_ = 0usize;
                        v___x_4529_ = lean_usize_of_nat(v___x_4522_);
                        v___x_4530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(v_binders_4089_, v___x_4528_, v___x_4529_, v___x_4094_, v_a_4091_, v_a_4092_);
                        v___y_4510_ = v___x_4530_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref_n(v___y_4126_, 2);
                v___x_4134_ = l_Array_append___redArg(v___y_4126_, v___y_4133_);
                lean_dec_ref(v___y_4133_);
                lean_inc_n(v___y_4101_, 18);
                lean_inc_n(v___y_4102_, 77);
                v___x_4135_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4135_, 0, v___y_4102_);
                lean_ctor_set(v___x_4135_, 1, v___y_4101_);
                lean_ctor_set(v___x_4135_, 2, v___x_4134_);
                lean_inc_n(v___y_4115_, 22);
                v___x_4136_ = l_Lean_Syntax_node7(
                    v___y_4102_,
                    v___y_4114_,
                    v___y_4110_,
                    v___y_4115_,
                    v___x_4135_,
                    v___y_4115_,
                    v___y_4115_,
                    v___y_4115_,
                    v___y_4115_,
                );
                v___x_4137_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__1;
                lean_inc_ref_n(v___y_4116_, 4);
                v___x_4138_ =
                    l_Lean_Name_mkStr4(v___x_4095_, v___x_4096_, v___y_4116_, v___x_4137_);
                v___x_4139_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__2;
                v___x_4140_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4140_, 0, v___y_4102_);
                lean_ctor_set(v___x_4140_, 1, v___x_4139_);
                v___x_4141_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__3;
                v___x_4142_ =
                    l_Lean_Name_mkStr4(v___x_4095_, v___x_4096_, v___y_4116_, v___x_4141_);
                lean_inc_n(v___y_4120_, 2);
                v___x_4143_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4143_, 0, v___y_4120_);
                lean_ctor_set(v___x_4143_, 1, v___y_4101_);
                lean_ctor_set(v___x_4143_, 2, v___x_4094_);
                v___x_4144_ = lean_unsigned_to_nat(2);
                v___x_4145_ = lean_mk_empty_array_with_capacity(v___x_4144_);
                v___x_4146_ = lean_array_push(v___x_4145_, v_elabName_4087_);
                v___x_4147_ = lean_array_push(v___x_4146_, v___x_4143_);
                v___x_4148_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4148_, 0, v___y_4120_);
                lean_ctor_set(v___x_4148_, 1, v___x_4142_);
                lean_ctor_set(v___x_4148_, 2, v___x_4147_);
                v___x_4149_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__4;
                v___x_4150_ =
                    l_Lean_Name_mkStr4(v___x_4095_, v___x_4096_, v___y_4116_, v___x_4149_);
                v___x_4151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1(v___y_4118_, v___y_4130_, v_binders_4089_);
                v_sz_4152_ = lean_array_size(v___x_4151_);
                v___x_4153_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2(v_sz_4152_, v___y_4130_, v___x_4151_);
                v_sz_4154_ = lean_array_size(v___x_4153_);
                v___x_4155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(v_sz_4154_, v___y_4130_, v___x_4153_);
                v___x_4156_ = l_Array_append___redArg(v___y_4126_, v___x_4155_);
                lean_dec_ref(v___x_4155_);
                v___x_4157_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1;
                lean_inc_ref(v___y_4109_);
                v___x_4158_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4158_, 0, v___y_4102_);
                lean_ctor_set(v___x_4158_, 1, v___y_4109_);
                v___x_4159_ = l_Lean_Syntax_node1(v___y_4102_, v___y_4101_, v___y_4107_);
                v___x_4160_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__5;
                v___x_4161_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4161_, 0, v___y_4102_);
                lean_ctor_set(v___x_4161_, 1, v___x_4160_);
                v___x_4162_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7_once), _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7);
                v___x_4163_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9;
                lean_inc_n(v___y_4105_, 5);
                lean_inc_n(v___y_4098_, 5);
                v___x_4164_ = l_Lean_addMacroScope(v___y_4098_, v___x_4163_, v___y_4105_);
                lean_inc_n(v___y_4128_, 5);
                v___x_4165_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4165_, 0, v___x_4163_);
                lean_ctor_set(v___x_4165_, 1, v___y_4128_);
                v___x_4166_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__10;
                lean_inc_n(v___y_4121_, 8);
                v___x_4167_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4167_, 0, v___x_4166_);
                lean_ctor_set(v___x_4167_, 1, v___y_4121_);
                v___x_4168_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4168_, 0, v___x_4165_);
                lean_ctor_set(v___x_4168_, 1, v___x_4167_);
                v___x_4169_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4169_, 0, v___y_4102_);
                lean_ctor_set(v___x_4169_, 1, v___x_4162_);
                lean_ctor_set(v___x_4169_, 2, v___x_4164_);
                lean_ctor_set(v___x_4169_, 3, v___x_4168_);
                lean_inc_ref_n(v___x_4161_, 4);
                v___x_4170_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___y_4101_, v___x_4161_, v___x_4169_);
                lean_inc_ref(v___y_4100_);
                v___x_4171_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4171_, 0, v___y_4102_);
                lean_ctor_set(v___x_4171_, 1, v___y_4100_);
                lean_inc_ref_n(v___x_4171_, 3);
                lean_inc_ref_n(v___x_4158_, 3);
                v___x_4172_ = l_Lean_Syntax_node5(
                    v___y_4102_,
                    v___x_4157_,
                    v___x_4158_,
                    v___x_4159_,
                    v___x_4170_,
                    v___y_4115_,
                    v___x_4171_,
                );
                v___x_4173_ = lean_array_push(v___x_4156_, v___x_4172_);
                v___x_4174_ = l_Lean_Syntax_node1(v___y_4102_, v___y_4101_, v___y_4111_);
                lean_inc_n(v_type_4088_, 2);
                v___x_4175_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___y_4101_, v___x_4161_, v_type_4088_);
                v___x_4176_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12;
                lean_inc_ref(v___y_4117_);
                v___x_4177_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4177_, 0, v___y_4102_);
                lean_ctor_set(v___x_4177_, 1, v___y_4117_);
                v___x_4178_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__14;
                v___x_4179_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__16;
                v___x_4180_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__17;
                v___x_4181_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4181_, 0, v___y_4102_);
                lean_ctor_set(v___x_4181_, 1, v___x_4180_);
                v___x_4182_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__18;
                v___x_4183_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4183_, 0, v___y_4102_);
                lean_ctor_set(v___x_4183_, 1, v___x_4182_);
                lean_inc_ref(v___x_4183_);
                lean_inc_ref(v___x_4181_);
                v___x_4184_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___x_4179_, v___x_4181_, v___x_4183_);
                v___x_4185_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20;
                v___x_4186_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22;
                v___x_4187_ = l_Lean_Syntax_node1(v___y_4102_, v___x_4186_, v___y_4115_);
                v___x_4188_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24;
                v___x_4189_ = l_Lean_Syntax_node1(v___y_4102_, v___x_4188_, v___y_4115_);
                v___x_4190_ = l_Lean_Syntax_node6(
                    v___y_4102_,
                    v___x_4185_,
                    v___x_4181_,
                    v___y_4115_,
                    v___x_4187_,
                    v___x_4189_,
                    v___y_4115_,
                    v___x_4183_,
                );
                v___x_4191_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___x_4178_, v___x_4184_, v___x_4190_);
                lean_inc_ref_n(v___x_4177_, 5);
                v___x_4192_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___x_4176_, v___x_4177_, v___x_4191_);
                v___x_4193_ = l_Lean_Syntax_node1(v___y_4102_, v___y_4101_, v___x_4192_);
                v___x_4194_ = l_Lean_Syntax_node5(
                    v___y_4102_,
                    v___x_4157_,
                    v___x_4158_,
                    v___x_4174_,
                    v___x_4175_,
                    v___x_4193_,
                    v___x_4171_,
                );
                v___x_4195_ = lean_array_push(v___x_4173_, v___x_4194_);
                v___x_4196_ = l_Lean_Syntax_node1(v___y_4102_, v___y_4101_, v___y_4104_);
                v___x_4197_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26_once), _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26);
                v___x_4198_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__27;
                v___x_4199_ = l_Lean_addMacroScope(v___y_4098_, v___x_4198_, v___y_4105_);
                v___x_4200_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4200_, 0, v___x_4198_);
                lean_ctor_set(v___x_4200_, 1, v___y_4128_);
                v___x_4201_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__28;
                v___x_4202_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4202_, 0, v___x_4201_);
                lean_ctor_set(v___x_4202_, 1, v___y_4121_);
                v___x_4203_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4203_, 0, v___x_4200_);
                lean_ctor_set(v___x_4203_, 1, v___x_4202_);
                v___x_4204_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4204_, 0, v___y_4102_);
                lean_ctor_set(v___x_4204_, 1, v___x_4197_);
                lean_ctor_set(v___x_4204_, 2, v___x_4199_);
                lean_ctor_set(v___x_4204_, 3, v___x_4203_);
                v___x_4205_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___y_4101_, v___x_4161_, v___x_4204_);
                v___x_4206_ = l_Lean_Syntax_node2(
                    v___y_4102_,
                    v___x_4176_,
                    v___x_4177_,
                    v_logExceptionsDefault_4082_,
                );
                v___x_4207_ = l_Lean_Syntax_node1(v___y_4102_, v___y_4101_, v___x_4206_);
                v___x_4208_ = l_Lean_Syntax_node5(
                    v___y_4102_,
                    v___x_4157_,
                    v___x_4158_,
                    v___x_4196_,
                    v___x_4205_,
                    v___x_4207_,
                    v___x_4171_,
                );
                v___x_4209_ = lean_array_push(v___x_4195_, v___x_4208_);
                v___x_4210_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4210_, 0, v___y_4102_);
                lean_ctor_set(v___x_4210_, 1, v___y_4101_);
                lean_ctor_set(v___x_4210_, 2, v___x_4209_);
                v___x_4211_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30;
                v___x_4212_ = l_Lean_Syntax_node1(v___y_4102_, v___y_4101_, v_type_4088_);
                lean_inc(v___x_4212_);
                lean_inc_n(v___y_4123_, 4);
                v___x_4213_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___y_4123_, v_monad_4080_, v___x_4212_);
                v___x_4214_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___x_4211_, v___x_4161_, v___x_4213_);
                v___x_4215_ = l_Lean_Syntax_node1(v___y_4102_, v___y_4101_, v___x_4214_);
                v___x_4216_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___x_4150_, v___x_4210_, v___x_4215_);
                v___x_4217_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31;
                v___x_4218_ =
                    l_Lean_Name_mkStr4(v___x_4095_, v___x_4096_, v___y_4116_, v___x_4217_);
                v___x_4219_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__32;
                v___x_4220_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33;
                v___x_4221_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4221_, 0, v___y_4102_);
                lean_ctor_set(v___x_4221_, 1, v___x_4219_);
                v___x_4222_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35;
                v___x_4223_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37;
                v___x_4224_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39;
                v___x_4225_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40;
                v___x_4226_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4226_, 0, v___y_4102_);
                lean_ctor_set(v___x_4226_, 1, v___x_4225_);
                v___x_4227_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42;
                v___x_4228_ = l_Lean_Syntax_node1(v___y_4102_, v___x_4227_, v___y_4115_);
                v___x_4229_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44;
                v___x_4230_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46;
                v___x_4231_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48;
                lean_inc_ref(v___y_4127_);
                v___x_4232_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4232_, 0, v___y_4102_);
                lean_ctor_set(v___x_4232_, 1, v___y_4127_);
                lean_ctor_set(v___x_4232_, 2, v___y_4119_);
                lean_ctor_set(v___x_4232_, 3, v___y_4121_);
                v___x_4233_ = l_Lean_Syntax_node1(v___y_4102_, v___x_4231_, v___x_4232_);
                lean_inc_ref_n(v___y_4106_, 5);
                v___x_4234_ = l_String_toRawSubstring_x27(v___y_4106_);
                v___x_4235_ = l_Lean_Name_mkStr1(v___y_4106_);
                v___x_4236_ = l_Lean_addMacroScope(v___y_4098_, v___x_4235_, v___y_4105_);
                lean_inc_ref_n(v___y_4124_, 2);
                lean_inc_ref_n(v___y_4122_, 2);
                v___x_4237_ =
                    l_Lean_Name_mkStr4(v___x_4095_, v___y_4122_, v___y_4124_, v___y_4106_);
                lean_inc(v___x_4237_);
                v___x_4238_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4238_, 0, v___x_4237_);
                lean_ctor_set(v___x_4238_, 1, v___y_4128_);
                v___x_4239_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4239_, 0, v___x_4237_);
                v___x_4240_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4240_, 0, v___x_4239_);
                lean_ctor_set(v___x_4240_, 1, v___y_4121_);
                v___x_4241_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4241_, 0, v___x_4238_);
                lean_ctor_set(v___x_4241_, 1, v___x_4240_);
                v___x_4242_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4242_, 0, v___y_4102_);
                lean_ctor_set(v___x_4242_, 1, v___x_4234_);
                lean_ctor_set(v___x_4242_, 2, v___x_4236_);
                lean_ctor_set(v___x_4242_, 3, v___x_4241_);
                v___x_4243_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___y_4123_, v___x_4242_, v___x_4212_);
                v___x_4244_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___x_4211_, v___x_4161_, v___x_4243_);
                v___x_4245_ = l_Lean_Syntax_node1(v___y_4102_, v___y_4101_, v___x_4244_);
                v___x_4246_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50;
                v___x_4247_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51;
                v___x_4248_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4248_, 0, v___y_4102_);
                lean_ctor_set(v___x_4248_, 1, v___x_4247_);
                v___x_4249_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___x_4246_, v___x_4248_, v___y_4132_);
                v___x_4250_ = l_Array_append___redArg(v___y_4126_, v___y_4131_);
                lean_dec_ref(v___y_4131_);
                v___x_4251_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4251_, 0, v___y_4102_);
                lean_ctor_set(v___x_4251_, 1, v___y_4101_);
                lean_ctor_set(v___x_4251_, 2, v___x_4250_);
                v___x_4252_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___y_4123_, v___x_4249_, v___x_4251_);
                v___x_4253_ = l_Lean_Syntax_node5(
                    v___y_4102_,
                    v___x_4230_,
                    v___x_4233_,
                    v___y_4115_,
                    v___x_4245_,
                    v___x_4177_,
                    v___x_4252_,
                );
                v___x_4254_ = l_Lean_Syntax_node1(v___y_4102_, v___x_4229_, v___x_4253_);
                lean_inc(v___x_4228_);
                lean_inc_ref(v___x_4226_);
                v___x_4255_ = l_Lean_Syntax_node4(
                    v___y_4102_,
                    v___x_4224_,
                    v___x_4226_,
                    v___y_4115_,
                    v___x_4228_,
                    v___x_4254_,
                );
                v___x_4256_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___x_4223_, v___x_4255_, v___y_4115_);
                lean_inc_ref(v___y_4108_);
                v___x_4257_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4257_, 0, v___y_4102_);
                lean_ctor_set(v___x_4257_, 1, v___y_4108_);
                lean_ctor_set(v___x_4257_, 2, v___y_4099_);
                lean_ctor_set(v___x_4257_, 3, v___y_4121_);
                v___x_4258_ = l_Lean_Syntax_node1(v___y_4102_, v___x_4231_, v___x_4257_);
                v___x_4259_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__53), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__53_once), _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__53);
                v___x_4260_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54;
                v___x_4261_ = l_Lean_Name_mkStr2(v___y_4106_, v___x_4260_);
                v___x_4262_ = l_Lean_addMacroScope(v___y_4098_, v___x_4261_, v___y_4105_);
                v___x_4263_ = l_Lean_Name_mkStr5(
                    v___x_4095_,
                    v___y_4122_,
                    v___y_4124_,
                    v___y_4106_,
                    v___x_4260_,
                );
                v___x_4264_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4264_, 0, v___x_4263_);
                lean_ctor_set(v___x_4264_, 1, v___y_4128_);
                v___x_4265_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4265_, 0, v___x_4264_);
                lean_ctor_set(v___x_4265_, 1, v___y_4121_);
                v___x_4266_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4266_, 0, v___y_4102_);
                lean_ctor_set(v___x_4266_, 1, v___x_4259_);
                lean_ctor_set(v___x_4266_, 2, v___x_4262_);
                lean_ctor_set(v___x_4266_, 3, v___x_4265_);
                v___x_4267_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56_once), _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56);
                v___x_4268_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57;
                v___x_4269_ = l_Lean_addMacroScope(v___y_4098_, v___x_4268_, v___y_4105_);
                v___x_4270_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4270_, 0, v___y_4102_);
                lean_ctor_set(v___x_4270_, 1, v___x_4267_);
                lean_ctor_set(v___x_4270_, 2, v___x_4269_);
                lean_ctor_set(v___x_4270_, 3, v___y_4121_);
                v___x_4271_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59_once), _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59);
                v___x_4272_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60;
                v___x_4273_ = l_Lean_addMacroScope(v___y_4098_, v___x_4272_, v___y_4105_);
                v___x_4274_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__61;
                v___x_4275_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4275_, 0, v___x_4274_);
                lean_ctor_set(v___x_4275_, 1, v___y_4128_);
                v___x_4276_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4276_, 0, v___x_4275_);
                lean_ctor_set(v___x_4276_, 1, v___y_4121_);
                v___x_4277_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4277_, 0, v___y_4102_);
                lean_ctor_set(v___x_4277_, 1, v___x_4271_);
                lean_ctor_set(v___x_4277_, 2, v___x_4273_);
                lean_ctor_set(v___x_4277_, 3, v___x_4276_);
                v___x_4278_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63;
                v___x_4279_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64;
                v___x_4280_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4280_, 0, v___y_4102_);
                lean_ctor_set(v___x_4280_, 1, v___x_4279_);
                lean_inc_ref(v___x_4280_);
                v___x_4281_ = l_Lean_Syntax_node3(
                    v___y_4102_,
                    v___x_4278_,
                    v___x_4280_,
                    v___x_4280_,
                    v_type_4088_,
                );
                v___x_4282_ = l_Lean_Syntax_node1(v___y_4102_, v___y_4101_, v___x_4281_);
                v___x_4283_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___y_4123_, v___x_4277_, v___x_4282_);
                v___x_4284_ = l_Lean_Syntax_node5(
                    v___y_4102_,
                    v___y_4112_,
                    v___x_4158_,
                    v___x_4270_,
                    v___x_4177_,
                    v___x_4283_,
                    v___x_4171_,
                );
                v___x_4285_ = l_Lean_Syntax_node1(v___y_4102_, v___y_4101_, v___x_4284_);
                v___x_4286_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___y_4123_, v___x_4266_, v___x_4285_);
                v___x_4287_ = l_Lean_Syntax_node5(
                    v___y_4102_,
                    v___x_4230_,
                    v___x_4258_,
                    v___y_4115_,
                    v___y_4115_,
                    v___x_4177_,
                    v___x_4286_,
                );
                v___x_4288_ = l_Lean_Syntax_node1(v___y_4102_, v___x_4229_, v___x_4287_);
                v___x_4289_ = l_Lean_Syntax_node4(
                    v___y_4102_,
                    v___x_4224_,
                    v___x_4226_,
                    v___y_4115_,
                    v___x_4228_,
                    v___x_4288_,
                );
                v___x_4290_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___x_4223_, v___x_4289_, v___y_4115_);
                v___x_4291_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66;
                v___x_4292_ = l_Lean_Syntax_node1(v___y_4102_, v___x_4291_, v___y_4113_);
                v___x_4293_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___x_4223_, v___x_4292_, v___y_4115_);
                v___x_4294_ = l_Lean_Syntax_node3(
                    v___y_4102_,
                    v___y_4101_,
                    v___x_4256_,
                    v___x_4290_,
                    v___x_4293_,
                );
                v___x_4295_ = l_Lean_Syntax_node1(v___y_4102_, v___x_4222_, v___x_4294_);
                v___x_4296_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___x_4220_, v___x_4221_, v___x_4295_);
                v___x_4297_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69;
                v___x_4298_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___x_4297_, v___y_4115_, v___y_4115_);
                v___x_4299_ = l_Lean_Syntax_node4(
                    v___y_4102_,
                    v___x_4218_,
                    v___x_4177_,
                    v___x_4296_,
                    v___x_4298_,
                    v___y_4115_,
                );
                v___x_4300_ = l_Lean_Syntax_node5(
                    v___y_4102_,
                    v___x_4138_,
                    v___x_4140_,
                    v___x_4148_,
                    v___x_4216_,
                    v___x_4299_,
                    v___y_4115_,
                );
                v___x_4301_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___y_4129_, v___x_4136_, v___x_4300_);
                v___x_4302_ =
                    l_Lean_Syntax_node2(v___y_4102_, v___y_4101_, v___y_4125_, v___x_4301_);
                v___x_4303_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4303_, 0, v___x_4302_);
                lean_ctor_set(v___x_4303_, 1, v___y_4103_);
                return v___x_4303_;
            }
            2 => {
                lean_inc_ref(v___y_4332_);
                v___x_4340_ = l_Array_append___redArg(v___y_4332_, v___y_4339_);
                lean_dec_ref(v___y_4339_);
                lean_inc(v___y_4308_);
                lean_inc(v___y_4309_);
                v___x_4341_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4341_, 0, v___y_4309_);
                lean_ctor_set(v___x_4341_, 1, v___y_4308_);
                lean_ctor_set(v___x_4341_, 2, v___x_4340_);
                if lean_obj_tag(v_vis_x3f_4085_) == 1 {
                    v_val_4342_ = lean_ctor_get(v_vis_x3f_4085_, 0);
                    lean_inc(v_val_4342_);
                    lean_dec_ref_known(v_vis_x3f_4085_, 1);
                    v___x_4343_ = l_Array_mkArray1___redArg(v_val_4342_);
                    v___y_4098_ = v___y_4305_;
                    v___y_4099_ = v___y_4306_;
                    v___y_4100_ = v___y_4307_;
                    v___y_4101_ = v___y_4308_;
                    v___y_4102_ = v___y_4309_;
                    v___y_4103_ = v___y_4311_;
                    v___y_4104_ = v___y_4310_;
                    v___y_4105_ = v___y_4312_;
                    v___y_4106_ = v___y_4313_;
                    v___y_4107_ = v___y_4314_;
                    v___y_4108_ = v___y_4316_;
                    v___y_4109_ = v___y_4315_;
                    v___y_4110_ = v___x_4341_;
                    v___y_4111_ = v___y_4317_;
                    v___y_4112_ = v___y_4318_;
                    v___y_4113_ = v___y_4319_;
                    v___y_4114_ = v___y_4320_;
                    v___y_4115_ = v___y_4321_;
                    v___y_4116_ = v___y_4322_;
                    v___y_4117_ = v___y_4323_;
                    v___y_4118_ = v___y_4324_;
                    v___y_4119_ = v___y_4325_;
                    v___y_4120_ = v___y_4326_;
                    v___y_4121_ = v___y_4327_;
                    v___y_4122_ = v___y_4328_;
                    v___y_4123_ = v___y_4329_;
                    v___y_4124_ = v___y_4330_;
                    v___y_4125_ = v___y_4331_;
                    v___y_4126_ = v___y_4332_;
                    v___y_4127_ = v___y_4333_;
                    v___y_4128_ = v___y_4334_;
                    v___y_4129_ = v___y_4335_;
                    v___y_4130_ = v___y_4336_;
                    v___y_4131_ = v___y_4337_;
                    v___y_4132_ = v___y_4338_;
                    v___y_4133_ = v___x_4343_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_vis_x3f_4085_);
                    v___x_4344_ =
                        l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7;
                    v___y_4098_ = v___y_4305_;
                    v___y_4099_ = v___y_4306_;
                    v___y_4100_ = v___y_4307_;
                    v___y_4101_ = v___y_4308_;
                    v___y_4102_ = v___y_4309_;
                    v___y_4103_ = v___y_4311_;
                    v___y_4104_ = v___y_4310_;
                    v___y_4105_ = v___y_4312_;
                    v___y_4106_ = v___y_4313_;
                    v___y_4107_ = v___y_4314_;
                    v___y_4108_ = v___y_4316_;
                    v___y_4109_ = v___y_4315_;
                    v___y_4110_ = v___x_4341_;
                    v___y_4111_ = v___y_4317_;
                    v___y_4112_ = v___y_4318_;
                    v___y_4113_ = v___y_4319_;
                    v___y_4114_ = v___y_4320_;
                    v___y_4115_ = v___y_4321_;
                    v___y_4116_ = v___y_4322_;
                    v___y_4117_ = v___y_4323_;
                    v___y_4118_ = v___y_4324_;
                    v___y_4119_ = v___y_4325_;
                    v___y_4120_ = v___y_4326_;
                    v___y_4121_ = v___y_4327_;
                    v___y_4122_ = v___y_4328_;
                    v___y_4123_ = v___y_4329_;
                    v___y_4124_ = v___y_4330_;
                    v___y_4125_ = v___y_4331_;
                    v___y_4126_ = v___y_4332_;
                    v___y_4127_ = v___y_4333_;
                    v___y_4128_ = v___y_4334_;
                    v___y_4129_ = v___y_4335_;
                    v___y_4130_ = v___y_4336_;
                    v___y_4131_ = v___y_4337_;
                    v___y_4132_ = v___y_4338_;
                    v___y_4133_ = v___x_4344_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___y_4376_);
                v___x_4384_ = l_Array_append___redArg(v___y_4376_, v___y_4383_);
                lean_dec_ref(v___y_4383_);
                lean_inc(v___y_4349_);
                lean_inc_n(v___y_4350_, 2);
                v___x_4385_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4385_, 0, v___y_4350_);
                lean_ctor_set(v___x_4385_, 1, v___y_4349_);
                lean_ctor_set(v___x_4385_, 2, v___x_4384_);
                v___x_4386_ = lean_unsigned_to_nat(9);
                v___x_4387_ = lean_mk_empty_array_with_capacity(v___x_4386_);
                lean_inc(v___y_4363_);
                v___x_4388_ = lean_array_push(v___x_4387_, v___y_4363_);
                v___x_4389_ = lean_array_push(v___x_4388_, v___y_4358_);
                v___x_4390_ = lean_array_push(v___x_4389_, v___y_4362_);
                v___x_4391_ = lean_array_push(v___x_4390_, v___y_4374_);
                lean_inc(v___y_4382_);
                v___x_4392_ = lean_array_push(v___x_4391_, v___y_4382_);
                v___x_4393_ = lean_array_push(v___x_4392_, v___y_4368_);
                v___x_4394_ = lean_array_push(v___x_4393_, v___y_4375_);
                lean_inc(v_type_4088_);
                v___x_4395_ = lean_array_push(v___x_4394_, v_type_4088_);
                v___x_4396_ = lean_array_push(v___x_4395_, v___x_4385_);
                lean_inc(v___y_4379_);
                v___x_4397_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4397_, 0, v___y_4350_);
                lean_ctor_set(v___x_4397_, 1, v___y_4379_);
                lean_ctor_set(v___x_4397_, 2, v___x_4396_);
                v___x_4398_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70;
                lean_inc_ref_n(v___y_4365_, 2);
                v___x_4399_ =
                    l_Lean_Name_mkStr4(v___x_4095_, v___x_4096_, v___y_4365_, v___x_4398_);
                v___x_4400_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__71;
                v___x_4401_ =
                    l_Lean_Name_mkStr4(v___x_4095_, v___x_4096_, v___y_4365_, v___x_4400_);
                if lean_obj_tag(v_doc_x3f_4084_) == 1 {
                    v_val_4402_ = lean_ctor_get(v_doc_x3f_4084_, 0);
                    lean_inc(v_val_4402_);
                    lean_dec_ref_known(v_doc_x3f_4084_, 1);
                    v___x_4403_ = l_Array_mkArray1___redArg(v_val_4402_);
                    v___y_4305_ = v___y_4346_;
                    v___y_4306_ = v___y_4347_;
                    v___y_4307_ = v___y_4348_;
                    v___y_4308_ = v___y_4349_;
                    v___y_4309_ = v___y_4350_;
                    v___y_4310_ = v___y_4351_;
                    v___y_4311_ = v___y_4352_;
                    v___y_4312_ = v___y_4353_;
                    v___y_4313_ = v___y_4354_;
                    v___y_4314_ = v___y_4355_;
                    v___y_4315_ = v___y_4356_;
                    v___y_4316_ = v___y_4357_;
                    v___y_4317_ = v___y_4359_;
                    v___y_4318_ = v___y_4360_;
                    v___y_4319_ = v___y_4361_;
                    v___y_4320_ = v___x_4401_;
                    v___y_4321_ = v___y_4363_;
                    v___y_4322_ = v___y_4365_;
                    v___y_4323_ = v___y_4364_;
                    v___y_4324_ = v___y_4366_;
                    v___y_4325_ = v___y_4367_;
                    v___y_4326_ = v___y_4370_;
                    v___y_4327_ = v___y_4369_;
                    v___y_4328_ = v___y_4371_;
                    v___y_4329_ = v___y_4372_;
                    v___y_4330_ = v___y_4373_;
                    v___y_4331_ = v___x_4397_;
                    v___y_4332_ = v___y_4376_;
                    v___y_4333_ = v___y_4377_;
                    v___y_4334_ = v___y_4378_;
                    v___y_4335_ = v___x_4399_;
                    v___y_4336_ = v___y_4380_;
                    v___y_4337_ = v___y_4381_;
                    v___y_4338_ = v___y_4382_;
                    v___y_4339_ = v___x_4403_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_doc_x3f_4084_);
                    v___x_4404_ =
                        l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7;
                    v___y_4305_ = v___y_4346_;
                    v___y_4306_ = v___y_4347_;
                    v___y_4307_ = v___y_4348_;
                    v___y_4308_ = v___y_4349_;
                    v___y_4309_ = v___y_4350_;
                    v___y_4310_ = v___y_4351_;
                    v___y_4311_ = v___y_4352_;
                    v___y_4312_ = v___y_4353_;
                    v___y_4313_ = v___y_4354_;
                    v___y_4314_ = v___y_4355_;
                    v___y_4315_ = v___y_4356_;
                    v___y_4316_ = v___y_4357_;
                    v___y_4317_ = v___y_4359_;
                    v___y_4318_ = v___y_4360_;
                    v___y_4319_ = v___y_4361_;
                    v___y_4320_ = v___x_4401_;
                    v___y_4321_ = v___y_4363_;
                    v___y_4322_ = v___y_4365_;
                    v___y_4323_ = v___y_4364_;
                    v___y_4324_ = v___y_4366_;
                    v___y_4325_ = v___y_4367_;
                    v___y_4326_ = v___y_4370_;
                    v___y_4327_ = v___y_4369_;
                    v___y_4328_ = v___y_4371_;
                    v___y_4329_ = v___y_4372_;
                    v___y_4330_ = v___y_4373_;
                    v___y_4331_ = v___x_4397_;
                    v___y_4332_ = v___y_4376_;
                    v___y_4333_ = v___y_4377_;
                    v___y_4334_ = v___y_4378_;
                    v___y_4335_ = v___x_4399_;
                    v___y_4336_ = v___y_4380_;
                    v___y_4337_ = v___y_4381_;
                    v___y_4338_ = v___y_4382_;
                    v___y_4339_ = v___x_4404_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_4408_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__73;
                v___x_4409_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74_once), _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74);
                lean_inc_ref(v_a_4091_);
                v___x_4410_ = lean_apply_3(
                    v_mkLogExceptionsTerm_4083_,
                    v___x_4409_,
                    v_a_4091_,
                    v_a_4407_,
                );
                if lean_obj_tag(v___x_4410_) == 0 {
                    v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
                    v_a_4412_ = lean_ctor_get(v___x_4410_, 1);
                    v_isSharedCheck_4508_ = (!lean_is_exclusive(v___x_4410_)) as u8;
                    if v_isSharedCheck_4508_ == 0 {
                        v___x_4414_ = v___x_4410_;
                        v_isShared_4415_ = v_isSharedCheck_4508_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4412_);
                        lean_inc(v_a_4411_);
                        lean_dec(v___x_4410_);
                        v___x_4414_ = lean_box(0);
                        v_isShared_4415_ = v_isSharedCheck_4508_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_4406_);
                    lean_dec(v_entries_x3f_4090_);
                    lean_dec_ref(v_binders_4089_);
                    lean_dec(v_type_4088_);
                    lean_dec(v_elabName_4087_);
                    lean_dec(v_tk_4086_);
                    lean_dec(v_vis_x3f_4085_);
                    lean_dec(v_doc_x3f_4084_);
                    lean_dec(v_logExceptionsDefault_4082_);
                    lean_dec_ref(v_mkMonadAdapt_4081_);
                    lean_dec(v_monad_4080_);
                    return v___x_4410_;
                }
            }
            5 => {
                v_quotContext_4416_ = lean_ctor_get(v_a_4091_, 1);
                v_currMacroScope_4417_ = lean_ctor_get(v_a_4091_, 2);
                v_ref_4418_ = lean_ctor_get(v_a_4091_, 5);
                v___x_4419_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__77), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__77_once), _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__77);
                v___x_4420_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__80), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__80_once), _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__80);
                v___x_4421_ = 0;
                v___x_4422_ = l_Lean_SourceInfo_fromRef(v_ref_4418_, v___x_4421_);
                v___x_4423_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82;
                v___x_4424_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__84), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__84_once), _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__84);
                v___x_4425_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85;
                v___x_4426_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__87;
                lean_inc_n(v_currMacroScope_4417_, 2);
                lean_inc_n(v_quotContext_4416_, 2);
                v___x_4427_ =
                    l_Lean_addMacroScope(v_quotContext_4416_, v___x_4426_, v_currMacroScope_4417_);
                v___x_4428_ = l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5;
                v___x_4429_ = l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6;
                v___x_4430_ = lean_box(0);
                v___x_4431_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__90;
                lean_inc_n(v___x_4422_, 3);
                v___x_4432_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4432_, 0, v___x_4422_);
                lean_ctor_set(v___x_4432_, 1, v___x_4424_);
                lean_ctor_set(v___x_4432_, 2, v___x_4427_);
                lean_ctor_set(v___x_4432_, 3, v___x_4431_);
                v___x_4433_ = l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__5;
                v___x_4434_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92_once), _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92);
                v___x_4435_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93;
                v___x_4436_ =
                    l_Lean_addMacroScope(v_quotContext_4416_, v___x_4435_, v_currMacroScope_4417_);
                lean_inc(v___x_4436_);
                v___x_4437_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4437_, 0, v___x_4422_);
                lean_ctor_set(v___x_4437_, 1, v___x_4434_);
                lean_ctor_set(v___x_4437_, 2, v___x_4436_);
                lean_ctor_set(v___x_4437_, 3, v___x_4430_);
                v___x_4438_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95;
                v___x_4439_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96;
                if v_isShared_4415_ == 0 {
                    lean_ctor_set_tag(v___x_4414_, 2);
                    lean_ctor_set(v___x_4414_, 1, v___x_4439_);
                    lean_ctor_set(v___x_4414_, 0, v___x_4422_);
                    v___x_4441_ = v___x_4414_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4507_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4422_);
                    lean_ctor_set(v_reuseFailAlloc_4507_, 1, v___x_4439_);
                    v___x_4441_ = v_reuseFailAlloc_4507_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4442_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98_once), _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98);
                v___x_4443_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99;
                lean_inc_n(v_currMacroScope_4417_, 2);
                lean_inc_n(v_quotContext_4416_, 2);
                v___x_4444_ =
                    l_Lean_addMacroScope(v_quotContext_4416_, v___x_4443_, v_currMacroScope_4417_);
                lean_inc(v___x_4444_);
                lean_inc_n(v___x_4422_, 7);
                v___x_4445_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4445_, 0, v___x_4422_);
                lean_ctor_set(v___x_4445_, 1, v___x_4442_);
                lean_ctor_set(v___x_4445_, 2, v___x_4444_);
                lean_ctor_set(v___x_4445_, 3, v___x_4430_);
                v___x_4446_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__100;
                v___x_4447_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4447_, 0, v___x_4422_);
                lean_ctor_set(v___x_4447_, 1, v___x_4446_);
                v___x_4448_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__101;
                v___x_4449_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4449_, 0, v___x_4422_);
                lean_ctor_set(v___x_4449_, 1, v___x_4448_);
                lean_inc_ref(v___x_4449_);
                lean_inc_ref(v___x_4447_);
                lean_inc_ref(v___x_4445_);
                lean_inc_ref(v___x_4441_);
                v___x_4450_ = l_Lean_Syntax_node5(
                    v___x_4422_,
                    v___x_4438_,
                    v___x_4441_,
                    v___x_4445_,
                    v___x_4447_,
                    v___x_4445_,
                    v___x_4449_,
                );
                v___x_4451_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102_once), _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102);
                v___x_4452_ =
                    l_Lean_addMacroScope(v_quotContext_4416_, v___x_4408_, v_currMacroScope_4417_);
                v___x_4453_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4453_, 0, v___x_4422_);
                lean_ctor_set(v___x_4453_, 1, v___x_4451_);
                lean_ctor_set(v___x_4453_, 2, v___x_4452_);
                lean_ctor_set(v___x_4453_, 3, v___x_4430_);
                v___x_4454_ = l_Lean_Syntax_node5(
                    v___x_4422_,
                    v___x_4438_,
                    v___x_4441_,
                    v___x_4453_,
                    v___x_4447_,
                    v_a_4411_,
                    v___x_4449_,
                );
                v___x_4455_ = l_Lean_Syntax_node5(
                    v___x_4422_,
                    v___x_4433_,
                    v___x_4437_,
                    v___x_4420_,
                    v___x_4419_,
                    v___x_4450_,
                    v___x_4454_,
                );
                v___x_4456_ =
                    l_Lean_Syntax_node2(v___x_4422_, v___x_4423_, v___x_4432_, v___x_4455_);
                lean_inc_ref(v_a_4091_);
                v___x_4457_ = lean_apply_3(v_mkMonadAdapt_4081_, v___x_4456_, v_a_4091_, v_a_4412_);
                if lean_obj_tag(v___x_4457_) == 0 {
                    v_a_4458_ = lean_ctor_get(v___x_4457_, 0);
                    v_a_4459_ = lean_ctor_get(v___x_4457_, 1);
                    v_isSharedCheck_4506_ = (!lean_is_exclusive(v___x_4457_)) as u8;
                    if v_isSharedCheck_4506_ == 0 {
                        v___x_4461_ = v___x_4457_;
                        v_isShared_4462_ = v_isSharedCheck_4506_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4459_);
                        lean_inc(v_a_4458_);
                        lean_dec(v___x_4457_);
                        v___x_4461_ = lean_box(0);
                        v_isShared_4462_ = v_isSharedCheck_4506_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4444_);
                    lean_dec(v___x_4436_);
                    lean_dec_ref(v_a_4406_);
                    lean_dec(v_entries_x3f_4090_);
                    lean_dec_ref(v_binders_4089_);
                    lean_dec(v_type_4088_);
                    lean_dec(v_elabName_4087_);
                    lean_dec(v_tk_4086_);
                    lean_dec(v_vis_x3f_4085_);
                    lean_dec(v_doc_x3f_4084_);
                    lean_dec(v_logExceptionsDefault_4082_);
                    lean_dec(v_monad_4080_);
                    return v___x_4457_;
                }
            }
            7 => {
                v___x_4463_ = l_Lean_TSyntax_getId(v_elabName_4087_);
                v___x_4464_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__104;
                v___x_4465_ = l_Lean_Name_append(v___x_4463_, v___x_4464_);
                v_fnName_4466_ = l_Lean_mkIdentFrom(v_elabName_4087_, v___x_4465_, v___x_4421_);
                v___x_4467_ = lean_unsigned_to_nat(3);
                v___x_4468_ = lean_mk_empty_array_with_capacity(v___x_4467_);
                v___x_4469_ = lean_array_push(v___x_4468_, v_tk_4086_);
                lean_inc(v_elabName_4087_);
                v___x_4470_ = lean_array_push(v___x_4469_, v_elabName_4087_);
                lean_inc(v_type_4088_);
                v___x_4471_ = lean_array_push(v___x_4470_, v_type_4088_);
                v___x_4472_ = lean_box(2);
                v___x_4473_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4473_, 0, v___x_4472_);
                lean_ctor_set(v___x_4473_, 1, v___x_4433_);
                lean_ctor_set(v___x_4473_, 2, v___x_4471_);
                v_ref_4474_ = l_Lean_replaceRef(v___x_4473_, v_ref_4418_);
                lean_dec_ref_known(v___x_4473_, 3);
                v___x_4475_ = l_Lean_SourceInfo_fromRef(v_ref_4474_, v___x_4421_);
                lean_dec(v_ref_4474_);
                v___x_4476_ = l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1;
                v___x_4477_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6,
                );
                lean_inc_n(v___x_4475_, 2);
                v___x_4478_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4478_, 0, v___x_4475_);
                lean_ctor_set(v___x_4478_, 1, v___x_4433_);
                lean_ctor_set(v___x_4478_, 2, v___x_4477_);
                v___x_4479_ = l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2;
                v___x_4480_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105;
                v___x_4481_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106;
                if v_isShared_4462_ == 0 {
                    lean_ctor_set_tag(v___x_4461_, 2);
                    lean_ctor_set(v___x_4461_, 1, v___x_4480_);
                    lean_ctor_set(v___x_4461_, 0, v___x_4475_);
                    v___x_4483_ = v___x_4461_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4505_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4475_);
                    lean_ctor_set(v_reuseFailAlloc_4505_, 1, v___x_4480_);
                    v___x_4483_ = v_reuseFailAlloc_4505_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                lean_inc_n(v___x_4475_, 9);
                v___x_4484_ = l_Lean_Syntax_node1(v___x_4475_, v___x_4481_, v___x_4483_);
                v___x_4485_ = l_Lean_Syntax_node1(v___x_4475_, v___x_4433_, v___x_4484_);
                v___x_4486_ = l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4;
                v___x_4487_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107;
                v___x_4488_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108;
                v___x_4489_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4489_, 0, v___x_4475_);
                lean_ctor_set(v___x_4489_, 1, v___x_4487_);
                v___x_4490_ = l_Lean_Syntax_node1(v___x_4475_, v___x_4488_, v___x_4489_);
                v___x_4491_ = l_Lean_Syntax_node1(v___x_4475_, v___x_4433_, v___x_4490_);
                v___x_4492_ = l_Lean_Syntax_node1(v___x_4475_, v___x_4486_, v___x_4491_);
                v___x_4493_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109;
                v___x_4494_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4494_, 0, v___x_4475_);
                lean_ctor_set(v___x_4494_, 1, v___x_4493_);
                v_sz_4495_ = lean_array_size(v_binders_4089_);
                v___x_4496_ = 0usize;
                lean_inc_ref(v_binders_4089_);
                v___x_4497_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(v_sz_4495_, v___x_4496_, v_binders_4089_);
                v___x_4498_ = l_Array_append___redArg(v___x_4477_, v___x_4497_);
                lean_dec_ref(v___x_4497_);
                v___x_4499_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4499_, 0, v___x_4475_);
                lean_ctor_set(v___x_4499_, 1, v___x_4433_);
                lean_ctor_set(v___x_4499_, 2, v___x_4498_);
                v___x_4500_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110;
                v___x_4501_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4501_, 0, v___x_4475_);
                lean_ctor_set(v___x_4501_, 1, v___x_4500_);
                if lean_obj_tag(v_entries_x3f_4090_) == 1 {
                    v_val_4502_ = lean_ctor_get(v_entries_x3f_4090_, 0);
                    lean_inc(v_val_4502_);
                    lean_dec_ref_known(v_entries_x3f_4090_, 1);
                    v___x_4503_ = l_Array_mkArray1___redArg(v_val_4502_);
                    lean_inc(v_currMacroScope_4417_);
                    lean_inc(v_quotContext_4416_);
                    v___y_4346_ = v_quotContext_4416_;
                    v___y_4347_ = v___x_4444_;
                    v___y_4348_ = v___x_4448_;
                    v___y_4349_ = v___x_4433_;
                    v___y_4350_ = v___x_4475_;
                    v___y_4351_ = v___x_4409_;
                    v___y_4352_ = v_a_4459_;
                    v___y_4353_ = v_currMacroScope_4417_;
                    v___y_4354_ = v___x_4425_;
                    v___y_4355_ = v___x_4419_;
                    v___y_4356_ = v___x_4439_;
                    v___y_4357_ = v___x_4442_;
                    v___y_4358_ = v___x_4485_;
                    v___y_4359_ = v___x_4420_;
                    v___y_4360_ = v___x_4438_;
                    v___y_4361_ = v_a_4458_;
                    v___y_4362_ = v___x_4492_;
                    v___y_4363_ = v___x_4478_;
                    v___y_4364_ = v___x_4446_;
                    v___y_4365_ = v___x_4479_;
                    v___y_4366_ = v_sz_4495_;
                    v___y_4367_ = v___x_4436_;
                    v___y_4368_ = v___x_4499_;
                    v___y_4369_ = v___x_4430_;
                    v___y_4370_ = v___x_4472_;
                    v___y_4371_ = v___x_4428_;
                    v___y_4372_ = v___x_4423_;
                    v___y_4373_ = v___x_4429_;
                    v___y_4374_ = v___x_4494_;
                    v___y_4375_ = v___x_4501_;
                    v___y_4376_ = v___x_4477_;
                    v___y_4377_ = v___x_4434_;
                    v___y_4378_ = v___x_4430_;
                    v___y_4379_ = v___x_4476_;
                    v___y_4380_ = v___x_4496_;
                    v___y_4381_ = v_a_4406_;
                    v___y_4382_ = v_fnName_4466_;
                    v___y_4383_ = v___x_4503_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_entries_x3f_4090_);
                    v___x_4504_ =
                        l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7;
                    lean_inc(v_currMacroScope_4417_);
                    lean_inc(v_quotContext_4416_);
                    v___y_4346_ = v_quotContext_4416_;
                    v___y_4347_ = v___x_4444_;
                    v___y_4348_ = v___x_4448_;
                    v___y_4349_ = v___x_4433_;
                    v___y_4350_ = v___x_4475_;
                    v___y_4351_ = v___x_4409_;
                    v___y_4352_ = v_a_4459_;
                    v___y_4353_ = v_currMacroScope_4417_;
                    v___y_4354_ = v___x_4425_;
                    v___y_4355_ = v___x_4419_;
                    v___y_4356_ = v___x_4439_;
                    v___y_4357_ = v___x_4442_;
                    v___y_4358_ = v___x_4485_;
                    v___y_4359_ = v___x_4420_;
                    v___y_4360_ = v___x_4438_;
                    v___y_4361_ = v_a_4458_;
                    v___y_4362_ = v___x_4492_;
                    v___y_4363_ = v___x_4478_;
                    v___y_4364_ = v___x_4446_;
                    v___y_4365_ = v___x_4479_;
                    v___y_4366_ = v_sz_4495_;
                    v___y_4367_ = v___x_4436_;
                    v___y_4368_ = v___x_4499_;
                    v___y_4369_ = v___x_4430_;
                    v___y_4370_ = v___x_4472_;
                    v___y_4371_ = v___x_4428_;
                    v___y_4372_ = v___x_4423_;
                    v___y_4373_ = v___x_4429_;
                    v___y_4374_ = v___x_4494_;
                    v___y_4375_ = v___x_4501_;
                    v___y_4376_ = v___x_4477_;
                    v___y_4377_ = v___x_4434_;
                    v___y_4378_ = v___x_4430_;
                    v___y_4379_ = v___x_4476_;
                    v___y_4380_ = v___x_4496_;
                    v___y_4381_ = v_a_4406_;
                    v___y_4382_ = v_fnName_4466_;
                    v___y_4383_ = v___x_4504_;
                    state = 3;
                    continue;
                }
            }
            9 => {
                if lean_obj_tag(v___y_4510_) == 0 {
                    v_a_4511_ = lean_ctor_get(v___y_4510_, 0);
                    lean_inc(v_a_4511_);
                    v_a_4512_ = lean_ctor_get(v___y_4510_, 1);
                    lean_inc(v_a_4512_);
                    lean_dec_ref_known(v___y_4510_, 2);
                    v_a_4406_ = v_a_4511_;
                    v_a_4407_ = v_a_4512_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v_entries_x3f_4090_);
                    lean_dec_ref(v_binders_4089_);
                    lean_dec(v_type_4088_);
                    lean_dec(v_elabName_4087_);
                    lean_dec(v_tk_4086_);
                    lean_dec(v_vis_x3f_4085_);
                    lean_dec(v_doc_x3f_4084_);
                    lean_dec_ref(v_mkLogExceptionsTerm_4083_);
                    lean_dec(v_logExceptionsDefault_4082_);
                    lean_dec_ref(v_mkMonadAdapt_4081_);
                    lean_dec(v_monad_4080_);
                    v_a_4513_ = lean_ctor_get(v___y_4510_, 0);
                    v_a_4514_ = lean_ctor_get(v___y_4510_, 1);
                    v_isSharedCheck_4521_ = (!lean_is_exclusive(v___y_4510_)) as u8;
                    if v_isSharedCheck_4521_ == 0 {
                        v___x_4516_ = v___y_4510_;
                        v_isShared_4517_ = v_isSharedCheck_4521_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_4514_);
                        lean_inc(v_a_4513_);
                        lean_dec(v___y_4510_);
                        v___x_4516_ = lean_box(0);
                        v_isShared_4517_ = v_isSharedCheck_4521_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_4517_ == 0 {
                    v___x_4519_ = v___x_4516_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4513_);
                    lean_ctor_set(v_reuseFailAlloc_4520_, 1, v_a_4514_);
                    v___x_4519_ = v_reuseFailAlloc_4520_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4519_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___boxed(
    mut v_monad_4531_: *mut LeanObject,
    mut v_mkMonadAdapt_4532_: *mut LeanObject,
    mut v_logExceptionsDefault_4533_: *mut LeanObject,
    mut v_mkLogExceptionsTerm_4534_: *mut LeanObject,
    mut v_doc_x3f_4535_: *mut LeanObject,
    mut v_vis_x3f_4536_: *mut LeanObject,
    mut v_tk_4537_: *mut LeanObject,
    mut v_elabName_4538_: *mut LeanObject,
    mut v_type_4539_: *mut LeanObject,
    mut v_binders_4540_: *mut LeanObject,
    mut v_entries_x3f_4541_: *mut LeanObject,
    mut v_a_4542_: *mut LeanObject,
    mut v_a_4543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4544_: *mut LeanObject = core::ptr::null_mut();
    v_res_4544_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(
        v_monad_4531_,
        v_mkMonadAdapt_4532_,
        v_logExceptionsDefault_4533_,
        v_mkLogExceptionsTerm_4534_,
        v_doc_x3f_4535_,
        v_vis_x3f_4536_,
        v_tk_4537_,
        v_elabName_4538_,
        v_type_4539_,
        v_binders_4540_,
        v_entries_x3f_4541_,
        v_a_4542_,
        v_a_4543_,
    );
    lean_dec_ref(v_a_4542_);
    return v_res_4544_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__0(
    mut v_logExceptions_4545_: *mut LeanObject,
    mut v___y_4546_: *mut LeanObject,
    mut v___y_4547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    v___x_4548_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4548_, 0, v_logExceptions_4545_);
    lean_ctor_set(v___x_4548_, 1, v___y_4547_);
    return v___x_4548_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__0___boxed(
    mut v_logExceptions_4549_: *mut LeanObject,
    mut v___y_4550_: *mut LeanObject,
    mut v___y_4551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4552_: *mut LeanObject = core::ptr::null_mut();
    v_res_4552_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__0(
        v_logExceptions_4549_,
        v___y_4550_,
        v___y_4551_,
    );
    lean_dec_ref(v___y_4550_);
    return v_res_4552_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__1(
    mut v___y_4553_: *mut LeanObject,
    mut v___y_4554_: *mut LeanObject,
    mut v___y_4555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    v___x_4556_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4556_, 0, v___y_4553_);
    lean_ctor_set(v___x_4556_, 1, v___y_4555_);
    return v___x_4556_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__1___boxed(
    mut v___y_4557_: *mut LeanObject,
    mut v___y_4558_: *mut LeanObject,
    mut v___y_4559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4560_: *mut LeanObject = core::ptr::null_mut();
    v_res_4560_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__1(
        v___y_4557_,
        v___y_4558_,
        v___y_4559_,
    );
    lean_dec_ref(v___y_4558_);
    return v_res_4560_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7() -> *mut LeanObject
{
    let mut v___x_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    v___x_4575_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6;
    v___x_4576_ = l_Lean_mkCIdent(v___x_4575_);
    return v___x_4576_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10()
-> *mut LeanObject {
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    v___x_4581_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__9;
    v___x_4582_ = l_Lean_mkCIdent(v___x_4581_);
    return v___x_4582_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab(
    mut v_x_4583_: *mut LeanObject,
    mut v_a_4584_: *mut LeanObject,
    mut v_a_4585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: u8 = 0;
    let mut v___x_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_x3f_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binders_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4609_: u8 = 0;
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4613_: u8 = 0;
    let mut v_a_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4618_: u8 = 0;
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4622_: u8 = 0;
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vis_x3f_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elabName_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: u8 = 0;
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: u8 = 0;
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: u8 = 0;
    let mut v___x_4646_: u8 = 0;
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_x3f_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: u8 = 0;
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: u8 = 0;
    let mut v___x_4661_: u8 = 0;
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vis_x3f_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: u8 = 0;
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: u8 = 0;
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: u8 = 0;
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4586_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1;
                lean_inc(v_x_4583_);
                v___x_4587_ = l_Lean_Syntax_isOfKind(v_x_4583_, v___x_4586_);
                if v___x_4587_ == 0 {
                    lean_dec(v_x_4583_);
                    v___x_4588_ = l_Lean_Macro_throwUnsupported___redArg(v_a_4585_);
                    return v___x_4588_;
                } else {
                    v___f_4589_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__2;
                    v___f_4590_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3;
                    v___x_4623_ = lean_unsigned_to_nat(0);
                    v___x_4666_ = l_Lean_Syntax_getArg(v_x_4583_, v___x_4623_);
                    v___x_4667_ = l_Lean_Syntax_isNone(v___x_4666_);
                    if v___x_4667_ == 0 {
                        v___x_4668_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_4666_);
                        v___x_4669_ = l_Lean_Syntax_matchesNull(v___x_4666_, v___x_4668_);
                        if v___x_4669_ == 0 {
                            lean_dec(v___x_4666_);
                            lean_dec(v_x_4583_);
                            v___x_4670_ = l_Lean_Macro_throwUnsupported___redArg(v_a_4585_);
                            return v___x_4670_;
                        } else {
                            v_doc_x3f_4671_ = l_Lean_Syntax_getArg(v___x_4666_, v___x_4623_);
                            lean_dec(v___x_4666_);
                            v___x_4672_ =
                                l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4;
                            lean_inc(v_doc_x3f_4671_);
                            v___x_4673_ = l_Lean_Syntax_isOfKind(v_doc_x3f_4671_, v___x_4672_);
                            if v___x_4673_ == 0 {
                                lean_dec(v_doc_x3f_4671_);
                                lean_dec(v_x_4583_);
                                v___x_4674_ = l_Lean_Macro_throwUnsupported___redArg(v_a_4585_);
                                return v___x_4674_;
                            } else {
                                v___x_4675_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_4675_, 0, v_doc_x3f_4671_);
                                v_doc_x3f_4655_ = v___x_4675_;
                                v___y_4656_ = v_a_4584_;
                                v___y_4657_ = v_a_4585_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_4666_);
                        v___x_4676_ = lean_box(0);
                        v_doc_x3f_4655_ = v___x_4676_;
                        v___y_4656_ = v_a_4584_;
                        v___y_4657_ = v_a_4585_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_binders_4601_ = l_Lean_Syntax_getArgs(v___y_4593_);
                lean_dec(v___y_4593_);
                v___x_4602_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7,
                );
                v___x_4603_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10,
                );
                v___x_4604_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_4602_, v___f_4590_, v___x_4603_, v___f_4589_, v___y_4595_, v___y_4592_, v___y_4594_, v___y_4597_, v___y_4596_, v_binders_4601_, v_entries_x3f_4598_, v___y_4599_, v___y_4600_);
                if lean_obj_tag(v___x_4604_) == 0 {
                    v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
                    v_a_4606_ = lean_ctor_get(v___x_4604_, 1);
                    v_isSharedCheck_4613_ = (!lean_is_exclusive(v___x_4604_)) as u8;
                    if v_isSharedCheck_4613_ == 0 {
                        v___x_4608_ = v___x_4604_;
                        v_isShared_4609_ = v_isSharedCheck_4613_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4606_);
                        lean_inc(v_a_4605_);
                        lean_dec(v___x_4604_);
                        v___x_4608_ = lean_box(0);
                        v_isShared_4609_ = v_isSharedCheck_4613_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4614_ = lean_ctor_get(v___x_4604_, 0);
                    v_a_4615_ = lean_ctor_get(v___x_4604_, 1);
                    v_isSharedCheck_4622_ = (!lean_is_exclusive(v___x_4604_)) as u8;
                    if v_isSharedCheck_4622_ == 0 {
                        v___x_4617_ = v___x_4604_;
                        v_isShared_4618_ = v_isSharedCheck_4622_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4615_);
                        lean_inc(v_a_4614_);
                        lean_dec(v___x_4604_);
                        v___x_4617_ = lean_box(0);
                        v_isShared_4618_ = v_isSharedCheck_4622_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4609_ == 0 {
                    v___x_4611_ = v___x_4608_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_a_4605_);
                    lean_ctor_set(v_reuseFailAlloc_4612_, 1, v_a_4606_);
                    v___x_4611_ = v_reuseFailAlloc_4612_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4611_;
            }
            4 => {
                if v_isShared_4618_ == 0 {
                    v___x_4620_ = v___x_4617_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4621_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_a_4614_);
                    lean_ctor_set(v_reuseFailAlloc_4621_, 1, v_a_4615_);
                    v___x_4620_ = v_reuseFailAlloc_4621_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4620_;
            }
            6 => {
                v___x_4630_ = lean_unsigned_to_nat(3);
                v_elabName_4631_ = l_Lean_Syntax_getArg(v_x_4583_, v___x_4630_);
                v___x_4632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13;
                lean_inc(v_elabName_4631_);
                v___x_4633_ = l_Lean_Syntax_isOfKind(v_elabName_4631_, v___x_4632_);
                if v___x_4633_ == 0 {
                    lean_dec(v_elabName_4631_);
                    lean_dec(v_vis_x3f_4627_);
                    lean_dec(v___y_4626_);
                    lean_dec(v_x_4583_);
                    v___x_4634_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4629_);
                    return v___x_4634_;
                } else {
                    v___x_4635_ = lean_unsigned_to_nat(4);
                    v_type_4636_ = l_Lean_Syntax_getArg(v_x_4583_, v___x_4635_);
                    lean_inc(v_type_4636_);
                    v___x_4637_ = l_Lean_Syntax_isOfKind(v_type_4636_, v___x_4632_);
                    if v___x_4637_ == 0 {
                        lean_dec(v_type_4636_);
                        lean_dec(v_elabName_4631_);
                        lean_dec(v_vis_x3f_4627_);
                        lean_dec(v___y_4626_);
                        lean_dec(v_x_4583_);
                        v___x_4638_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4629_);
                        return v___x_4638_;
                    } else {
                        v___x_4639_ = lean_unsigned_to_nat(2);
                        v_tk_4640_ = l_Lean_Syntax_getArg(v_x_4583_, v___x_4639_);
                        v___x_4641_ = lean_unsigned_to_nat(5);
                        v___x_4642_ = l_Lean_Syntax_getArg(v_x_4583_, v___x_4641_);
                        v___x_4643_ = lean_unsigned_to_nat(6);
                        v___x_4644_ = l_Lean_Syntax_getArg(v_x_4583_, v___x_4643_);
                        lean_dec(v_x_4583_);
                        v___x_4645_ = l_Lean_Syntax_isNone(v___x_4644_);
                        if v___x_4645_ == 0 {
                            lean_inc(v___x_4644_);
                            v___x_4646_ = l_Lean_Syntax_matchesNull(v___x_4644_, v___y_4625_);
                            if v___x_4646_ == 0 {
                                lean_dec(v___x_4644_);
                                lean_dec(v___x_4642_);
                                lean_dec(v_tk_4640_);
                                lean_dec(v_type_4636_);
                                lean_dec(v_elabName_4631_);
                                lean_dec(v_vis_x3f_4627_);
                                lean_dec(v___y_4626_);
                                v___x_4647_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4629_);
                                return v___x_4647_;
                            } else {
                                v_entries_x3f_4648_ =
                                    l_Lean_Syntax_getArg(v___x_4644_, v___x_4623_);
                                lean_dec(v___x_4644_);
                                v___x_4649_ =
                                    l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3;
                                lean_inc(v_entries_x3f_4648_);
                                v___x_4650_ =
                                    l_Lean_Syntax_isOfKind(v_entries_x3f_4648_, v___x_4649_);
                                if v___x_4650_ == 0 {
                                    lean_dec(v_entries_x3f_4648_);
                                    lean_dec(v___x_4642_);
                                    lean_dec(v_tk_4640_);
                                    lean_dec(v_type_4636_);
                                    lean_dec(v_elabName_4631_);
                                    lean_dec(v_vis_x3f_4627_);
                                    lean_dec(v___y_4626_);
                                    v___x_4651_ =
                                        l_Lean_Macro_throwUnsupported___redArg(v___y_4629_);
                                    return v___x_4651_;
                                } else {
                                    v___x_4652_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_4652_, 0, v_entries_x3f_4648_);
                                    v___y_4592_ = v_vis_x3f_4627_;
                                    v___y_4593_ = v___x_4642_;
                                    v___y_4594_ = v_tk_4640_;
                                    v___y_4595_ = v___y_4626_;
                                    v___y_4596_ = v_type_4636_;
                                    v___y_4597_ = v_elabName_4631_;
                                    v_entries_x3f_4598_ = v___x_4652_;
                                    v___y_4599_ = v___y_4628_;
                                    v___y_4600_ = v___y_4629_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_4644_);
                            v___x_4653_ = lean_box(0);
                            v___y_4592_ = v_vis_x3f_4627_;
                            v___y_4593_ = v___x_4642_;
                            v___y_4594_ = v_tk_4640_;
                            v___y_4595_ = v___y_4626_;
                            v___y_4596_ = v_type_4636_;
                            v___y_4597_ = v_elabName_4631_;
                            v_entries_x3f_4598_ = v___x_4653_;
                            v___y_4599_ = v___y_4628_;
                            v___y_4600_ = v___y_4629_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            7 => {
                v___x_4658_ = lean_unsigned_to_nat(1);
                v___x_4659_ = l_Lean_Syntax_getArg(v_x_4583_, v___x_4658_);
                v___x_4660_ = l_Lean_Syntax_isNone(v___x_4659_);
                if v___x_4660_ == 0 {
                    lean_inc(v___x_4659_);
                    v___x_4661_ = l_Lean_Syntax_matchesNull(v___x_4659_, v___x_4658_);
                    if v___x_4661_ == 0 {
                        lean_dec(v___x_4659_);
                        lean_dec(v_doc_x3f_4655_);
                        lean_dec(v_x_4583_);
                        v___x_4662_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4657_);
                        return v___x_4662_;
                    } else {
                        v_vis_x3f_4663_ = l_Lean_Syntax_getArg(v___x_4659_, v___x_4623_);
                        lean_dec(v___x_4659_);
                        v___x_4664_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4664_, 0, v_vis_x3f_4663_);
                        v___y_4625_ = v___x_4658_;
                        v___y_4626_ = v_doc_x3f_4655_;
                        v_vis_x3f_4627_ = v___x_4664_;
                        v___y_4628_ = v___y_4656_;
                        v___y_4629_ = v___y_4657_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4659_);
                    v___x_4665_ = lean_box(0);
                    v___y_4625_ = v___x_4658_;
                    v___y_4626_ = v_doc_x3f_4655_;
                    v_vis_x3f_4627_ = v___x_4665_;
                    v___y_4628_ = v___y_4656_;
                    v___y_4629_ = v___y_4657_;
                    state = 6;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___boxed(
    mut v_x_4677_: *mut LeanObject,
    mut v_a_4678_: *mut LeanObject,
    mut v_a_4679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4680_: *mut LeanObject = core::ptr::null_mut();
    v_res_4680_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab(v_x_4677_, v_a_4678_, v_a_4679_);
    lean_dec_ref(v_a_4678_);
    return v_res_4680_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1()
-> *mut LeanObject {
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
    v___x_4688_ = l_Lean_Elab_macroAttribute;
    v___x_4689_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1;
    v___x_4690_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1;
    v___x_4691_ = lean_alloc_closure(
        l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_4692_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4688_,
        v___x_4689_,
        v___x_4690_,
        v___x_4691_,
    );
    return v___x_4692_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___boxed(
    mut v_a_4693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4694_: *mut LeanObject = core::ptr::null_mut();
    v_res_4694_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1();
    return v_res_4694_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab(
    mut v_a_4695_: *mut LeanObject,
    mut v_a_4696_: *mut LeanObject,
    mut v_a_4697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    v___x_4699_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0;
    v___x_4700_ = lean_unsigned_to_nat(2);
    v___x_4701_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(
        v___x_4699_,
        v___x_4700_,
        v_a_4695_,
        v_a_4696_,
        v_a_4697_,
    );
    return v___x_4701_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___boxed(
    mut v_a_4702_: *mut LeanObject,
    mut v_a_4703_: *mut LeanObject,
    mut v_a_4704_: *mut LeanObject,
    mut v_a_4705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4706_: *mut LeanObject = core::ptr::null_mut();
    v_res_4706_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab(v_a_4702_, v_a_4703_, v_a_4704_);
    lean_dec(v_a_4704_);
    lean_dec_ref(v_a_4703_);
    lean_dec(v_a_4702_);
    return v_res_4706_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0()
-> *mut LeanObject {
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    v___x_4707_ = lean_alloc_closure(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___boxed as *mut core::ffi::c_void, 4, 0);
    v___x_4708_ = lean_alloc_closure(
        l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_4708_, 0, v___x_4707_);
    return v___x_4708_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1()
-> *mut LeanObject {
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    v___x_4710_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1;
    v___x_4711_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0_once), _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0);
    v___x_4712_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4710_, v___x_4711_);
    return v___x_4712_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___boxed(
    mut v_a_4713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4714_: *mut LeanObject = core::ptr::null_mut();
    v_res_4714_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1();
    return v_res_4714_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9()
-> *mut LeanObject {
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    v___x_4726_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__8;
    v___x_4727_ = l_String_toRawSubstring_x27(v___x_4726_);
    return v___x_4727_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14()
-> *mut LeanObject {
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut LeanObject = core::ptr::null_mut();
    v___x_4732_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__13;
    v___x_4733_ = l_String_toRawSubstring_x27(v___x_4732_);
    return v___x_4733_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22()
-> *mut LeanObject {
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    v___x_4748_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__21;
    v___x_4749_ = l_String_toRawSubstring_x27(v___x_4748_);
    return v___x_4749_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1(
    mut v___x_4752_: *mut LeanObject,
    mut v___x_4753_: *mut LeanObject,
    mut v___x_4754_: *mut LeanObject,
    mut v___x_4755_: *mut LeanObject,
    mut v___x_4756_: *mut LeanObject,
    mut v_logExceptions_4757_: *mut LeanObject,
    mut v___y_4758_: *mut LeanObject,
    mut v___y_4759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_quotContext_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: u8 = 0;
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    v_quotContext_4760_ = lean_ctor_get(v___y_4758_, 1);
    v_currMacroScope_4761_ = lean_ctor_get(v___y_4758_, 2);
    v_ref_4762_ = lean_ctor_get(v___y_4758_, 5);
    v___x_4763_ = 0;
    v___x_4764_ = l_Lean_SourceInfo_fromRef(v_ref_4762_, v___x_4763_);
    v___x_4765_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__1;
    v___x_4766_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__2;
    lean_inc_n(v___x_4764_, 13);
    v___x_4767_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_4767_, 0, v___x_4764_);
    lean_ctor_set(v___x_4767_, 1, v___x_4766_);
    v___x_4768_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__3;
    lean_inc_ref_n(v___x_4754_, 4);
    lean_inc_ref_n(v___x_4753_, 3);
    lean_inc_ref_n(v___x_4752_, 8);
    v___x_4769_ = l_Lean_Name_mkStr4(v___x_4752_, v___x_4753_, v___x_4754_, v___x_4768_);
    v___x_4770_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__4;
    v___x_4771_ = l_Lean_Name_mkStr4(v___x_4752_, v___x_4753_, v___x_4754_, v___x_4770_);
    v___x_4772_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__5;
    v___x_4773_ = l_Lean_Name_mkStr4(v___x_4752_, v___x_4753_, v___x_4754_, v___x_4772_);
    v___x_4774_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96;
    v___x_4775_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_4775_, 0, v___x_4764_);
    lean_ctor_set(v___x_4775_, 1, v___x_4774_);
    v___x_4776_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__7;
    v___x_4777_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9_once
        ),
        _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9,
    );
    v___x_4778_ = lean_box(0);
    lean_inc_n(v_currMacroScope_4761_, 3);
    lean_inc_n(v_quotContext_4760_, 3);
    v___x_4779_ = l_Lean_addMacroScope(v_quotContext_4760_, v___x_4778_, v_currMacroScope_4761_);
    lean_inc_ref_n(v___x_4755_, 2);
    v___x_4780_ = l_Lean_Name_mkStr3(v___x_4752_, v___x_4755_, v___x_4756_);
    v___x_4781_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4781_, 0, v___x_4780_);
    v___x_4782_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__10;
    v___x_4783_ = l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2;
    v___x_4784_ = l_Lean_Name_mkStr3(v___x_4752_, v___x_4782_, v___x_4783_);
    v___x_4785_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4785_, 0, v___x_4784_);
    v___x_4786_ = l_Lean_Name_mkStr3(v___x_4752_, v___x_4755_, v___x_4783_);
    v___x_4787_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4787_, 0, v___x_4786_);
    v___x_4788_ = l_Lean_Name_mkStr3(v___x_4752_, v___x_4755_, v___x_4754_);
    v___x_4789_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4789_, 0, v___x_4788_);
    v___x_4790_ = l_Lean_Name_mkStr2(v___x_4752_, v___x_4782_);
    v___x_4791_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4791_, 0, v___x_4790_);
    v___x_4792_ = lean_box(0);
    v___x_4793_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4793_, 0, v___x_4791_);
    lean_ctor_set(v___x_4793_, 1, v___x_4792_);
    v___x_4794_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4794_, 0, v___x_4789_);
    lean_ctor_set(v___x_4794_, 1, v___x_4793_);
    v___x_4795_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4795_, 0, v___x_4787_);
    lean_ctor_set(v___x_4795_, 1, v___x_4794_);
    v___x_4796_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4796_, 0, v___x_4785_);
    lean_ctor_set(v___x_4796_, 1, v___x_4795_);
    v___x_4797_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4797_, 0, v___x_4781_);
    lean_ctor_set(v___x_4797_, 1, v___x_4796_);
    v___x_4798_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_4798_, 0, v___x_4764_);
    lean_ctor_set(v___x_4798_, 1, v___x_4777_);
    lean_ctor_set(v___x_4798_, 2, v___x_4779_);
    lean_ctor_set(v___x_4798_, 3, v___x_4797_);
    v___x_4799_ = l_Lean_Syntax_node1(v___x_4764_, v___x_4776_, v___x_4798_);
    v___x_4800_ = l_Lean_Syntax_node2(v___x_4764_, v___x_4773_, v___x_4775_, v___x_4799_);
    v___x_4801_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__11;
    v___x_4802_ = l_Lean_Name_mkStr4(v___x_4752_, v___x_4753_, v___x_4754_, v___x_4801_);
    v___x_4803_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__12;
    v___x_4804_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_4804_, 0, v___x_4764_);
    lean_ctor_set(v___x_4804_, 1, v___x_4803_);
    v___x_4805_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14_once
        ),
        _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14,
    );
    v___x_4806_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__15;
    v___x_4807_ = l_Lean_addMacroScope(v_quotContext_4760_, v___x_4806_, v_currMacroScope_4761_);
    v___x_4808_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__19;
    v___x_4809_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_4809_, 0, v___x_4764_);
    lean_ctor_set(v___x_4809_, 1, v___x_4805_);
    lean_ctor_set(v___x_4809_, 2, v___x_4807_);
    lean_ctor_set(v___x_4809_, 3, v___x_4808_);
    v___x_4810_ = l_Lean_Syntax_node2(v___x_4764_, v___x_4802_, v___x_4804_, v___x_4809_);
    v___x_4811_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__101;
    v___x_4812_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_4812_, 0, v___x_4764_);
    lean_ctor_set(v___x_4812_, 1, v___x_4811_);
    v___x_4813_ = l_Lean_Syntax_node3(
        v___x_4764_,
        v___x_4771_,
        v___x_4800_,
        v___x_4810_,
        v___x_4812_,
    );
    v___x_4814_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__20;
    v___x_4815_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_4815_, 0, v___x_4764_);
    lean_ctor_set(v___x_4815_, 1, v___x_4814_);
    v___x_4816_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22_once
        ),
        _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22,
    );
    v___x_4817_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__23;
    v___x_4818_ = l_Lean_addMacroScope(v_quotContext_4760_, v___x_4817_, v_currMacroScope_4761_);
    v___x_4819_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_4819_, 0, v___x_4764_);
    lean_ctor_set(v___x_4819_, 1, v___x_4816_);
    lean_ctor_set(v___x_4819_, 2, v___x_4818_);
    lean_ctor_set(v___x_4819_, 3, v___x_4792_);
    v___x_4820_ = l_Lean_Syntax_node3(
        v___x_4764_,
        v___x_4769_,
        v___x_4813_,
        v___x_4815_,
        v___x_4819_,
    );
    v___x_4821_ = l_Lean_Syntax_node3(
        v___x_4764_,
        v___x_4765_,
        v_logExceptions_4757_,
        v___x_4767_,
        v___x_4820_,
    );
    v___x_4822_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4822_, 0, v___x_4821_);
    lean_ctor_set(v___x_4822_, 1, v___y_4759_);
    return v___x_4822_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___boxed(
    mut v___x_4823_: *mut LeanObject,
    mut v___x_4824_: *mut LeanObject,
    mut v___x_4825_: *mut LeanObject,
    mut v___x_4826_: *mut LeanObject,
    mut v___x_4827_: *mut LeanObject,
    mut v_logExceptions_4828_: *mut LeanObject,
    mut v___y_4829_: *mut LeanObject,
    mut v___y_4830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4831_: *mut LeanObject = core::ptr::null_mut();
    v_res_4831_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1(
        v___x_4823_,
        v___x_4824_,
        v___x_4825_,
        v___x_4826_,
        v___x_4827_,
        v_logExceptions_4828_,
        v___y_4829_,
        v___y_4830_,
    );
    lean_dec_ref(v___y_4829_);
    return v_res_4831_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5() -> *mut LeanObject
{
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    v___x_4850_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4;
    v___x_4851_ = l_Lean_mkCIdent(v___x_4850_);
    return v___x_4851_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8() -> *mut LeanObject
{
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    v___x_4856_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__7;
    v___x_4857_ = l_Lean_mkCIdent(v___x_4856_);
    return v___x_4857_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab(
    mut v_x_4858_: *mut LeanObject,
    mut v_a_4859_: *mut LeanObject,
    mut v_a_4860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: u8 = 0;
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_x3f_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binders_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4884_: u8 = 0;
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4888_: u8 = 0;
    let mut v_a_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4893_: u8 = 0;
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4897_: u8 = 0;
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vis_x3f_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elabName_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: u8 = 0;
    let mut v___x_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: u8 = 0;
    let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: u8 = 0;
    let mut v___x_4921_: u8 = 0;
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_x3f_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: u8 = 0;
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: u8 = 0;
    let mut v___x_4936_: u8 = 0;
    let mut v___x_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vis_x3f_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: u8 = 0;
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: u8 = 0;
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: u8 = 0;
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4861_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1;
                lean_inc(v_x_4858_);
                v___x_4862_ = l_Lean_Syntax_isOfKind(v_x_4858_, v___x_4861_);
                if v___x_4862_ == 0 {
                    lean_dec(v_x_4858_);
                    v___x_4863_ = l_Lean_Macro_throwUnsupported___redArg(v_a_4860_);
                    return v___x_4863_;
                } else {
                    v___f_4864_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3;
                    v___x_4898_ = lean_unsigned_to_nat(0);
                    v___x_4941_ = l_Lean_Syntax_getArg(v_x_4858_, v___x_4898_);
                    v___x_4942_ = l_Lean_Syntax_isNone(v___x_4941_);
                    if v___x_4942_ == 0 {
                        v___x_4943_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_4941_);
                        v___x_4944_ = l_Lean_Syntax_matchesNull(v___x_4941_, v___x_4943_);
                        if v___x_4944_ == 0 {
                            lean_dec(v___x_4941_);
                            lean_dec(v_x_4858_);
                            v___x_4945_ = l_Lean_Macro_throwUnsupported___redArg(v_a_4860_);
                            return v___x_4945_;
                        } else {
                            v_doc_x3f_4946_ = l_Lean_Syntax_getArg(v___x_4941_, v___x_4898_);
                            lean_dec(v___x_4941_);
                            v___x_4947_ =
                                l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4;
                            lean_inc(v_doc_x3f_4946_);
                            v___x_4948_ = l_Lean_Syntax_isOfKind(v_doc_x3f_4946_, v___x_4947_);
                            if v___x_4948_ == 0 {
                                lean_dec(v_doc_x3f_4946_);
                                lean_dec(v_x_4858_);
                                v___x_4949_ = l_Lean_Macro_throwUnsupported___redArg(v_a_4860_);
                                return v___x_4949_;
                            } else {
                                v___x_4950_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_4950_, 0, v_doc_x3f_4946_);
                                v_doc_x3f_4930_ = v___x_4950_;
                                v___y_4931_ = v_a_4859_;
                                v___y_4932_ = v_a_4860_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_4941_);
                        v___x_4951_ = lean_box(0);
                        v_doc_x3f_4930_ = v___x_4951_;
                        v___y_4931_ = v_a_4859_;
                        v___y_4932_ = v_a_4860_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___f_4875_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__2;
                v_binders_4876_ = l_Lean_Syntax_getArgs(v___y_4867_);
                lean_dec(v___y_4867_);
                v___x_4877_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5,
                );
                v___x_4878_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8,
                );
                v___x_4879_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_4877_, v___f_4864_, v___x_4878_, v___f_4875_, v___y_4870_, v___y_4868_, v___y_4869_, v___y_4871_, v___y_4866_, v_binders_4876_, v_entries_x3f_4872_, v___y_4873_, v___y_4874_);
                if lean_obj_tag(v___x_4879_) == 0 {
                    v_a_4880_ = lean_ctor_get(v___x_4879_, 0);
                    v_a_4881_ = lean_ctor_get(v___x_4879_, 1);
                    v_isSharedCheck_4888_ = (!lean_is_exclusive(v___x_4879_)) as u8;
                    if v_isSharedCheck_4888_ == 0 {
                        v___x_4883_ = v___x_4879_;
                        v_isShared_4884_ = v_isSharedCheck_4888_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4881_);
                        lean_inc(v_a_4880_);
                        lean_dec(v___x_4879_);
                        v___x_4883_ = lean_box(0);
                        v_isShared_4884_ = v_isSharedCheck_4888_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4889_ = lean_ctor_get(v___x_4879_, 0);
                    v_a_4890_ = lean_ctor_get(v___x_4879_, 1);
                    v_isSharedCheck_4897_ = (!lean_is_exclusive(v___x_4879_)) as u8;
                    if v_isSharedCheck_4897_ == 0 {
                        v___x_4892_ = v___x_4879_;
                        v_isShared_4893_ = v_isSharedCheck_4897_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4890_);
                        lean_inc(v_a_4889_);
                        lean_dec(v___x_4879_);
                        v___x_4892_ = lean_box(0);
                        v_isShared_4893_ = v_isSharedCheck_4897_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4884_ == 0 {
                    v___x_4886_ = v___x_4883_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4887_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4887_, 0, v_a_4880_);
                    lean_ctor_set(v_reuseFailAlloc_4887_, 1, v_a_4881_);
                    v___x_4886_ = v_reuseFailAlloc_4887_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4886_;
            }
            4 => {
                if v_isShared_4893_ == 0 {
                    v___x_4895_ = v___x_4892_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4896_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4896_, 0, v_a_4889_);
                    lean_ctor_set(v_reuseFailAlloc_4896_, 1, v_a_4890_);
                    v___x_4895_ = v_reuseFailAlloc_4896_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4895_;
            }
            6 => {
                v___x_4905_ = lean_unsigned_to_nat(3);
                v_elabName_4906_ = l_Lean_Syntax_getArg(v_x_4858_, v___x_4905_);
                v___x_4907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13;
                lean_inc(v_elabName_4906_);
                v___x_4908_ = l_Lean_Syntax_isOfKind(v_elabName_4906_, v___x_4907_);
                if v___x_4908_ == 0 {
                    lean_dec(v_elabName_4906_);
                    lean_dec(v_vis_x3f_4902_);
                    lean_dec(v___y_4901_);
                    lean_dec(v_x_4858_);
                    v___x_4909_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4904_);
                    return v___x_4909_;
                } else {
                    v___x_4910_ = lean_unsigned_to_nat(4);
                    v_type_4911_ = l_Lean_Syntax_getArg(v_x_4858_, v___x_4910_);
                    lean_inc(v_type_4911_);
                    v___x_4912_ = l_Lean_Syntax_isOfKind(v_type_4911_, v___x_4907_);
                    if v___x_4912_ == 0 {
                        lean_dec(v_type_4911_);
                        lean_dec(v_elabName_4906_);
                        lean_dec(v_vis_x3f_4902_);
                        lean_dec(v___y_4901_);
                        lean_dec(v_x_4858_);
                        v___x_4913_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4904_);
                        return v___x_4913_;
                    } else {
                        v___x_4914_ = lean_unsigned_to_nat(2);
                        v_tk_4915_ = l_Lean_Syntax_getArg(v_x_4858_, v___x_4914_);
                        v___x_4916_ = lean_unsigned_to_nat(5);
                        v___x_4917_ = l_Lean_Syntax_getArg(v_x_4858_, v___x_4916_);
                        v___x_4918_ = lean_unsigned_to_nat(6);
                        v___x_4919_ = l_Lean_Syntax_getArg(v_x_4858_, v___x_4918_);
                        lean_dec(v_x_4858_);
                        v___x_4920_ = l_Lean_Syntax_isNone(v___x_4919_);
                        if v___x_4920_ == 0 {
                            lean_inc(v___x_4919_);
                            v___x_4921_ = l_Lean_Syntax_matchesNull(v___x_4919_, v___y_4900_);
                            if v___x_4921_ == 0 {
                                lean_dec(v___x_4919_);
                                lean_dec(v___x_4917_);
                                lean_dec(v_tk_4915_);
                                lean_dec(v_type_4911_);
                                lean_dec(v_elabName_4906_);
                                lean_dec(v_vis_x3f_4902_);
                                lean_dec(v___y_4901_);
                                v___x_4922_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4904_);
                                return v___x_4922_;
                            } else {
                                v_entries_x3f_4923_ =
                                    l_Lean_Syntax_getArg(v___x_4919_, v___x_4898_);
                                lean_dec(v___x_4919_);
                                v___x_4924_ =
                                    l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3;
                                lean_inc(v_entries_x3f_4923_);
                                v___x_4925_ =
                                    l_Lean_Syntax_isOfKind(v_entries_x3f_4923_, v___x_4924_);
                                if v___x_4925_ == 0 {
                                    lean_dec(v_entries_x3f_4923_);
                                    lean_dec(v___x_4917_);
                                    lean_dec(v_tk_4915_);
                                    lean_dec(v_type_4911_);
                                    lean_dec(v_elabName_4906_);
                                    lean_dec(v_vis_x3f_4902_);
                                    lean_dec(v___y_4901_);
                                    v___x_4926_ =
                                        l_Lean_Macro_throwUnsupported___redArg(v___y_4904_);
                                    return v___x_4926_;
                                } else {
                                    v___x_4927_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_4927_, 0, v_entries_x3f_4923_);
                                    v___y_4866_ = v_type_4911_;
                                    v___y_4867_ = v___x_4917_;
                                    v___y_4868_ = v_vis_x3f_4902_;
                                    v___y_4869_ = v_tk_4915_;
                                    v___y_4870_ = v___y_4901_;
                                    v___y_4871_ = v_elabName_4906_;
                                    v_entries_x3f_4872_ = v___x_4927_;
                                    v___y_4873_ = v___y_4903_;
                                    v___y_4874_ = v___y_4904_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_4919_);
                            v___x_4928_ = lean_box(0);
                            v___y_4866_ = v_type_4911_;
                            v___y_4867_ = v___x_4917_;
                            v___y_4868_ = v_vis_x3f_4902_;
                            v___y_4869_ = v_tk_4915_;
                            v___y_4870_ = v___y_4901_;
                            v___y_4871_ = v_elabName_4906_;
                            v_entries_x3f_4872_ = v___x_4928_;
                            v___y_4873_ = v___y_4903_;
                            v___y_4874_ = v___y_4904_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            7 => {
                v___x_4933_ = lean_unsigned_to_nat(1);
                v___x_4934_ = l_Lean_Syntax_getArg(v_x_4858_, v___x_4933_);
                v___x_4935_ = l_Lean_Syntax_isNone(v___x_4934_);
                if v___x_4935_ == 0 {
                    lean_inc(v___x_4934_);
                    v___x_4936_ = l_Lean_Syntax_matchesNull(v___x_4934_, v___x_4933_);
                    if v___x_4936_ == 0 {
                        lean_dec(v___x_4934_);
                        lean_dec(v_doc_x3f_4930_);
                        lean_dec(v_x_4858_);
                        v___x_4937_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4932_);
                        return v___x_4937_;
                    } else {
                        v_vis_x3f_4938_ = l_Lean_Syntax_getArg(v___x_4934_, v___x_4898_);
                        lean_dec(v___x_4934_);
                        v___x_4939_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4939_, 0, v_vis_x3f_4938_);
                        v___y_4900_ = v___x_4933_;
                        v___y_4901_ = v_doc_x3f_4930_;
                        v_vis_x3f_4902_ = v___x_4939_;
                        v___y_4903_ = v___y_4931_;
                        v___y_4904_ = v___y_4932_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4934_);
                    v___x_4940_ = lean_box(0);
                    v___y_4900_ = v___x_4933_;
                    v___y_4901_ = v_doc_x3f_4930_;
                    v_vis_x3f_4902_ = v___x_4940_;
                    v___y_4903_ = v___y_4931_;
                    v___y_4904_ = v___y_4932_;
                    state = 6;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___boxed(
    mut v_x_4952_: *mut LeanObject,
    mut v_a_4953_: *mut LeanObject,
    mut v_a_4954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4955_: *mut LeanObject = core::ptr::null_mut();
    v_res_4955_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab(v_x_4952_, v_a_4953_, v_a_4954_);
    lean_dec_ref(v_a_4953_);
    return v_res_4955_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1()
-> *mut LeanObject {
    let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut LeanObject = core::ptr::null_mut();
    v___x_4963_ = l_Lean_Elab_macroAttribute;
    v___x_4964_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1;
    v___x_4965_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1;
    v___x_4966_ = lean_alloc_closure(
        l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_4967_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4963_,
        v___x_4964_,
        v___x_4965_,
        v___x_4966_,
    );
    return v___x_4967_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___boxed(
    mut v_a_4968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4969_: *mut LeanObject = core::ptr::null_mut();
    v_res_4969_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1();
    return v_res_4969_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab(
    mut v_a_4970_: *mut LeanObject,
    mut v_a_4971_: *mut LeanObject,
    mut v_a_4972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut LeanObject = core::ptr::null_mut();
    v___x_4974_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0;
    v___x_4975_ = lean_unsigned_to_nat(2);
    v___x_4976_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(
        v___x_4974_,
        v___x_4975_,
        v_a_4970_,
        v_a_4971_,
        v_a_4972_,
    );
    return v___x_4976_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___boxed(
    mut v_a_4977_: *mut LeanObject,
    mut v_a_4978_: *mut LeanObject,
    mut v_a_4979_: *mut LeanObject,
    mut v_a_4980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4981_: *mut LeanObject = core::ptr::null_mut();
    v_res_4981_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab(v_a_4977_, v_a_4978_, v_a_4979_);
    lean_dec(v_a_4979_);
    lean_dec_ref(v_a_4978_);
    lean_dec(v_a_4977_);
    return v_res_4981_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0()
-> *mut LeanObject {
    let mut v___x_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut LeanObject = core::ptr::null_mut();
    v___x_4982_ = lean_alloc_closure(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___boxed as *mut core::ffi::c_void, 4, 0);
    v___x_4983_ = lean_alloc_closure(
        l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_4983_, 0, v___x_4982_);
    return v___x_4983_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1()
-> *mut LeanObject {
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    v___x_4985_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1;
    v___x_4986_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0_once), _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0);
    v___x_4987_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4985_, v___x_4986_);
    return v___x_4987_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___boxed(
    mut v_a_4988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4989_: *mut LeanObject = core::ptr::null_mut();
    v_res_4989_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1();
    return v_res_4989_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1()
-> *mut LeanObject {
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
    v___x_4991_ = l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__0;
    v___x_4992_ = l_String_toRawSubstring_x27(v___x_4991_);
    return v___x_4992_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1(
    mut v___x_4995_: *mut LeanObject,
    mut v___x_4996_: *mut LeanObject,
    mut v___x_4997_: *mut LeanObject,
    mut v___x_4998_: *mut LeanObject,
    mut v___x_4999_: *mut LeanObject,
    mut v_logExceptions_5000_: *mut LeanObject,
    mut v___y_5001_: *mut LeanObject,
    mut v___y_5002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_quotContext_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: u8 = 0;
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
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    v_quotContext_5003_ = lean_ctor_get(v___y_5001_, 1);
    v_currMacroScope_5004_ = lean_ctor_get(v___y_5001_, 2);
    v_ref_5005_ = lean_ctor_get(v___y_5001_, 5);
    v___x_5006_ = 0;
    v___x_5007_ = l_Lean_SourceInfo_fromRef(v_ref_5005_, v___x_5006_);
    v___x_5008_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__1;
    v___x_5009_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__2;
    lean_inc_n(v___x_5007_, 13);
    v___x_5010_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_5010_, 0, v___x_5007_);
    lean_ctor_set(v___x_5010_, 1, v___x_5009_);
    v___x_5011_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__3;
    lean_inc_ref_n(v___x_4997_, 4);
    lean_inc_ref_n(v___x_4996_, 3);
    lean_inc_ref_n(v___x_4995_, 8);
    v___x_5012_ = l_Lean_Name_mkStr4(v___x_4995_, v___x_4996_, v___x_4997_, v___x_5011_);
    v___x_5013_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__4;
    v___x_5014_ = l_Lean_Name_mkStr4(v___x_4995_, v___x_4996_, v___x_4997_, v___x_5013_);
    v___x_5015_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__5;
    v___x_5016_ = l_Lean_Name_mkStr4(v___x_4995_, v___x_4996_, v___x_4997_, v___x_5015_);
    v___x_5017_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96;
    v___x_5018_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_5018_, 0, v___x_5007_);
    lean_ctor_set(v___x_5018_, 1, v___x_5017_);
    v___x_5019_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__7;
    v___x_5020_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9_once
        ),
        _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9,
    );
    v___x_5021_ = lean_box(0);
    lean_inc_n(v_currMacroScope_5004_, 3);
    lean_inc_n(v_quotContext_5003_, 3);
    v___x_5022_ = l_Lean_addMacroScope(v_quotContext_5003_, v___x_5021_, v_currMacroScope_5004_);
    lean_inc_ref_n(v___x_4998_, 2);
    v___x_5023_ = l_Lean_Name_mkStr3(v___x_4995_, v___x_4998_, v___x_4999_);
    v___x_5024_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5024_, 0, v___x_5023_);
    v___x_5025_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__10;
    v___x_5026_ = l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2;
    v___x_5027_ = l_Lean_Name_mkStr3(v___x_4995_, v___x_5025_, v___x_5026_);
    v___x_5028_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5028_, 0, v___x_5027_);
    v___x_5029_ = l_Lean_Name_mkStr3(v___x_4995_, v___x_4998_, v___x_5026_);
    v___x_5030_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5030_, 0, v___x_5029_);
    v___x_5031_ = l_Lean_Name_mkStr3(v___x_4995_, v___x_4998_, v___x_4997_);
    v___x_5032_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5032_, 0, v___x_5031_);
    v___x_5033_ = l_Lean_Name_mkStr2(v___x_4995_, v___x_5025_);
    v___x_5034_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5034_, 0, v___x_5033_);
    v___x_5035_ = lean_box(0);
    v___x_5036_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5036_, 0, v___x_5034_);
    lean_ctor_set(v___x_5036_, 1, v___x_5035_);
    v___x_5037_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5037_, 0, v___x_5032_);
    lean_ctor_set(v___x_5037_, 1, v___x_5036_);
    v___x_5038_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5038_, 0, v___x_5030_);
    lean_ctor_set(v___x_5038_, 1, v___x_5037_);
    v___x_5039_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5039_, 0, v___x_5028_);
    lean_ctor_set(v___x_5039_, 1, v___x_5038_);
    v___x_5040_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5040_, 0, v___x_5024_);
    lean_ctor_set(v___x_5040_, 1, v___x_5039_);
    v___x_5041_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_5041_, 0, v___x_5007_);
    lean_ctor_set(v___x_5041_, 1, v___x_5020_);
    lean_ctor_set(v___x_5041_, 2, v___x_5022_);
    lean_ctor_set(v___x_5041_, 3, v___x_5040_);
    v___x_5042_ = l_Lean_Syntax_node1(v___x_5007_, v___x_5019_, v___x_5041_);
    v___x_5043_ = l_Lean_Syntax_node2(v___x_5007_, v___x_5016_, v___x_5018_, v___x_5042_);
    v___x_5044_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__11;
    v___x_5045_ = l_Lean_Name_mkStr4(v___x_4995_, v___x_4996_, v___x_4997_, v___x_5044_);
    v___x_5046_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__12;
    v___x_5047_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_5047_, 0, v___x_5007_);
    lean_ctor_set(v___x_5047_, 1, v___x_5046_);
    v___x_5048_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14_once
        ),
        _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14,
    );
    v___x_5049_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__15;
    v___x_5050_ = l_Lean_addMacroScope(v_quotContext_5003_, v___x_5049_, v_currMacroScope_5004_);
    v___x_5051_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__19;
    v___x_5052_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_5052_, 0, v___x_5007_);
    lean_ctor_set(v___x_5052_, 1, v___x_5048_);
    lean_ctor_set(v___x_5052_, 2, v___x_5050_);
    lean_ctor_set(v___x_5052_, 3, v___x_5051_);
    v___x_5053_ = l_Lean_Syntax_node2(v___x_5007_, v___x_5045_, v___x_5047_, v___x_5052_);
    v___x_5054_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__101;
    v___x_5055_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_5055_, 0, v___x_5007_);
    lean_ctor_set(v___x_5055_, 1, v___x_5054_);
    v___x_5056_ = l_Lean_Syntax_node3(
        v___x_5007_,
        v___x_5014_,
        v___x_5043_,
        v___x_5053_,
        v___x_5055_,
    );
    v___x_5057_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__20;
    v___x_5058_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_5058_, 0, v___x_5007_);
    lean_ctor_set(v___x_5058_, 1, v___x_5057_);
    v___x_5059_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1,
    );
    v___x_5060_ = l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__2;
    v___x_5061_ = l_Lean_addMacroScope(v_quotContext_5003_, v___x_5060_, v_currMacroScope_5004_);
    v___x_5062_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_5062_, 0, v___x_5007_);
    lean_ctor_set(v___x_5062_, 1, v___x_5059_);
    lean_ctor_set(v___x_5062_, 2, v___x_5061_);
    lean_ctor_set(v___x_5062_, 3, v___x_5035_);
    v___x_5063_ = l_Lean_Syntax_node3(
        v___x_5007_,
        v___x_5012_,
        v___x_5056_,
        v___x_5058_,
        v___x_5062_,
    );
    v___x_5064_ = l_Lean_Syntax_node3(
        v___x_5007_,
        v___x_5008_,
        v_logExceptions_5000_,
        v___x_5010_,
        v___x_5063_,
    );
    v___x_5065_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5065_, 0, v___x_5064_);
    lean_ctor_set(v___x_5065_, 1, v___y_5002_);
    return v___x_5065_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___boxed(
    mut v___x_5066_: *mut LeanObject,
    mut v___x_5067_: *mut LeanObject,
    mut v___x_5068_: *mut LeanObject,
    mut v___x_5069_: *mut LeanObject,
    mut v___x_5070_: *mut LeanObject,
    mut v_logExceptions_5071_: *mut LeanObject,
    mut v___y_5072_: *mut LeanObject,
    mut v___y_5073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5074_: *mut LeanObject = core::ptr::null_mut();
    v_res_5074_ = l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1(
        v___x_5066_,
        v___x_5067_,
        v___x_5068_,
        v___x_5069_,
        v___x_5070_,
        v_logExceptions_5071_,
        v___y_5072_,
        v___y_5073_,
    );
    lean_dec_ref(v___y_5072_);
    return v_res_5074_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6() -> *mut LeanObject
{
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    v___x_5094_ = l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5;
    v___x_5095_ = l_Lean_mkCIdent(v___x_5094_);
    return v___x_5095_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeclareTacticConfig(
    mut v_x_5096_: *mut LeanObject,
    mut v_a_5097_: *mut LeanObject,
    mut v_a_5098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: u8 = 0;
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_x3f_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binders_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5122_: u8 = 0;
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5126_: u8 = 0;
    let mut v_a_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5131_: u8 = 0;
    let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5135_: u8 = 0;
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vis_x3f_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elabName_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: u8 = 0;
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: u8 = 0;
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: u8 = 0;
    let mut v___x_5159_: u8 = 0;
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_x3f_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: u8 = 0;
    let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: u8 = 0;
    let mut v___x_5174_: u8 = 0;
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vis_x3f_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: u8 = 0;
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: u8 = 0;
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: u8 = 0;
    let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5099_ = l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1;
                lean_inc(v_x_5096_);
                v___x_5100_ = l_Lean_Syntax_isOfKind(v_x_5096_, v___x_5099_);
                if v___x_5100_ == 0 {
                    lean_dec(v_x_5096_);
                    v___x_5101_ = l_Lean_Macro_throwUnsupported___redArg(v_a_5098_);
                    return v___x_5101_;
                } else {
                    v___f_5102_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3;
                    v___x_5136_ = lean_unsigned_to_nat(0);
                    v___x_5179_ = l_Lean_Syntax_getArg(v_x_5096_, v___x_5136_);
                    v___x_5180_ = l_Lean_Syntax_isNone(v___x_5179_);
                    if v___x_5180_ == 0 {
                        v___x_5181_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_5179_);
                        v___x_5182_ = l_Lean_Syntax_matchesNull(v___x_5179_, v___x_5181_);
                        if v___x_5182_ == 0 {
                            lean_dec(v___x_5179_);
                            lean_dec(v_x_5096_);
                            v___x_5183_ = l_Lean_Macro_throwUnsupported___redArg(v_a_5098_);
                            return v___x_5183_;
                        } else {
                            v_doc_x3f_5184_ = l_Lean_Syntax_getArg(v___x_5179_, v___x_5136_);
                            lean_dec(v___x_5179_);
                            v___x_5185_ =
                                l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4;
                            lean_inc(v_doc_x3f_5184_);
                            v___x_5186_ = l_Lean_Syntax_isOfKind(v_doc_x3f_5184_, v___x_5185_);
                            if v___x_5186_ == 0 {
                                lean_dec(v_doc_x3f_5184_);
                                lean_dec(v_x_5096_);
                                v___x_5187_ = l_Lean_Macro_throwUnsupported___redArg(v_a_5098_);
                                return v___x_5187_;
                            } else {
                                v___x_5188_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_5188_, 0, v_doc_x3f_5184_);
                                v_doc_x3f_5168_ = v___x_5188_;
                                v___y_5169_ = v_a_5097_;
                                v___y_5170_ = v_a_5098_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_5179_);
                        v___x_5189_ = lean_box(0);
                        v_doc_x3f_5168_ = v___x_5189_;
                        v___y_5169_ = v_a_5097_;
                        v___y_5170_ = v_a_5098_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___f_5113_ = l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__2;
                v_binders_5114_ = l_Lean_Syntax_getArgs(v___y_5106_);
                lean_dec(v___y_5106_);
                v___x_5115_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6,
                );
                v___x_5116_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8,
                );
                v___x_5117_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_5115_, v___f_5102_, v___x_5116_, v___f_5113_, v___y_5109_, v___y_5108_, v___y_5107_, v___y_5104_, v___y_5105_, v_binders_5114_, v_entries_x3f_5110_, v___y_5111_, v___y_5112_);
                if lean_obj_tag(v___x_5117_) == 0 {
                    v_a_5118_ = lean_ctor_get(v___x_5117_, 0);
                    v_a_5119_ = lean_ctor_get(v___x_5117_, 1);
                    v_isSharedCheck_5126_ = (!lean_is_exclusive(v___x_5117_)) as u8;
                    if v_isSharedCheck_5126_ == 0 {
                        v___x_5121_ = v___x_5117_;
                        v_isShared_5122_ = v_isSharedCheck_5126_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5119_);
                        lean_inc(v_a_5118_);
                        lean_dec(v___x_5117_);
                        v___x_5121_ = lean_box(0);
                        v_isShared_5122_ = v_isSharedCheck_5126_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_5127_ = lean_ctor_get(v___x_5117_, 0);
                    v_a_5128_ = lean_ctor_get(v___x_5117_, 1);
                    v_isSharedCheck_5135_ = (!lean_is_exclusive(v___x_5117_)) as u8;
                    if v_isSharedCheck_5135_ == 0 {
                        v___x_5130_ = v___x_5117_;
                        v_isShared_5131_ = v_isSharedCheck_5135_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5128_);
                        lean_inc(v_a_5127_);
                        lean_dec(v___x_5117_);
                        v___x_5130_ = lean_box(0);
                        v_isShared_5131_ = v_isSharedCheck_5135_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5122_ == 0 {
                    v___x_5124_ = v___x_5121_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5125_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_a_5118_);
                    lean_ctor_set(v_reuseFailAlloc_5125_, 1, v_a_5119_);
                    v___x_5124_ = v_reuseFailAlloc_5125_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5124_;
            }
            4 => {
                if v_isShared_5131_ == 0 {
                    v___x_5133_ = v___x_5130_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5134_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5134_, 0, v_a_5127_);
                    lean_ctor_set(v_reuseFailAlloc_5134_, 1, v_a_5128_);
                    v___x_5133_ = v_reuseFailAlloc_5134_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5133_;
            }
            6 => {
                v___x_5143_ = lean_unsigned_to_nat(3);
                v_elabName_5144_ = l_Lean_Syntax_getArg(v_x_5096_, v___x_5143_);
                v___x_5145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13;
                lean_inc(v_elabName_5144_);
                v___x_5146_ = l_Lean_Syntax_isOfKind(v_elabName_5144_, v___x_5145_);
                if v___x_5146_ == 0 {
                    lean_dec(v_elabName_5144_);
                    lean_dec(v_vis_x3f_5140_);
                    lean_dec(v___y_5139_);
                    lean_dec(v_x_5096_);
                    v___x_5147_ = l_Lean_Macro_throwUnsupported___redArg(v___y_5142_);
                    return v___x_5147_;
                } else {
                    v___x_5148_ = lean_unsigned_to_nat(4);
                    v_type_5149_ = l_Lean_Syntax_getArg(v_x_5096_, v___x_5148_);
                    lean_inc(v_type_5149_);
                    v___x_5150_ = l_Lean_Syntax_isOfKind(v_type_5149_, v___x_5145_);
                    if v___x_5150_ == 0 {
                        lean_dec(v_type_5149_);
                        lean_dec(v_elabName_5144_);
                        lean_dec(v_vis_x3f_5140_);
                        lean_dec(v___y_5139_);
                        lean_dec(v_x_5096_);
                        v___x_5151_ = l_Lean_Macro_throwUnsupported___redArg(v___y_5142_);
                        return v___x_5151_;
                    } else {
                        v___x_5152_ = lean_unsigned_to_nat(2);
                        v_tk_5153_ = l_Lean_Syntax_getArg(v_x_5096_, v___x_5152_);
                        v___x_5154_ = lean_unsigned_to_nat(5);
                        v___x_5155_ = l_Lean_Syntax_getArg(v_x_5096_, v___x_5154_);
                        v___x_5156_ = lean_unsigned_to_nat(6);
                        v___x_5157_ = l_Lean_Syntax_getArg(v_x_5096_, v___x_5156_);
                        lean_dec(v_x_5096_);
                        v___x_5158_ = l_Lean_Syntax_isNone(v___x_5157_);
                        if v___x_5158_ == 0 {
                            lean_inc(v___x_5157_);
                            v___x_5159_ = l_Lean_Syntax_matchesNull(v___x_5157_, v___y_5138_);
                            if v___x_5159_ == 0 {
                                lean_dec(v___x_5157_);
                                lean_dec(v___x_5155_);
                                lean_dec(v_tk_5153_);
                                lean_dec(v_type_5149_);
                                lean_dec(v_elabName_5144_);
                                lean_dec(v_vis_x3f_5140_);
                                lean_dec(v___y_5139_);
                                v___x_5160_ = l_Lean_Macro_throwUnsupported___redArg(v___y_5142_);
                                return v___x_5160_;
                            } else {
                                v_entries_x3f_5161_ =
                                    l_Lean_Syntax_getArg(v___x_5157_, v___x_5136_);
                                lean_dec(v___x_5157_);
                                v___x_5162_ =
                                    l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3;
                                lean_inc(v_entries_x3f_5161_);
                                v___x_5163_ =
                                    l_Lean_Syntax_isOfKind(v_entries_x3f_5161_, v___x_5162_);
                                if v___x_5163_ == 0 {
                                    lean_dec(v_entries_x3f_5161_);
                                    lean_dec(v___x_5155_);
                                    lean_dec(v_tk_5153_);
                                    lean_dec(v_type_5149_);
                                    lean_dec(v_elabName_5144_);
                                    lean_dec(v_vis_x3f_5140_);
                                    lean_dec(v___y_5139_);
                                    v___x_5164_ =
                                        l_Lean_Macro_throwUnsupported___redArg(v___y_5142_);
                                    return v___x_5164_;
                                } else {
                                    v___x_5165_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_5165_, 0, v_entries_x3f_5161_);
                                    v___y_5104_ = v_elabName_5144_;
                                    v___y_5105_ = v_type_5149_;
                                    v___y_5106_ = v___x_5155_;
                                    v___y_5107_ = v_tk_5153_;
                                    v___y_5108_ = v_vis_x3f_5140_;
                                    v___y_5109_ = v___y_5139_;
                                    v_entries_x3f_5110_ = v___x_5165_;
                                    v___y_5111_ = v___y_5141_;
                                    v___y_5112_ = v___y_5142_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_5157_);
                            v___x_5166_ = lean_box(0);
                            v___y_5104_ = v_elabName_5144_;
                            v___y_5105_ = v_type_5149_;
                            v___y_5106_ = v___x_5155_;
                            v___y_5107_ = v_tk_5153_;
                            v___y_5108_ = v_vis_x3f_5140_;
                            v___y_5109_ = v___y_5139_;
                            v_entries_x3f_5110_ = v___x_5166_;
                            v___y_5111_ = v___y_5141_;
                            v___y_5112_ = v___y_5142_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            7 => {
                v___x_5171_ = lean_unsigned_to_nat(1);
                v___x_5172_ = l_Lean_Syntax_getArg(v_x_5096_, v___x_5171_);
                v___x_5173_ = l_Lean_Syntax_isNone(v___x_5172_);
                if v___x_5173_ == 0 {
                    lean_inc(v___x_5172_);
                    v___x_5174_ = l_Lean_Syntax_matchesNull(v___x_5172_, v___x_5171_);
                    if v___x_5174_ == 0 {
                        lean_dec(v___x_5172_);
                        lean_dec(v_doc_x3f_5168_);
                        lean_dec(v_x_5096_);
                        v___x_5175_ = l_Lean_Macro_throwUnsupported___redArg(v___y_5170_);
                        return v___x_5175_;
                    } else {
                        v_vis_x3f_5176_ = l_Lean_Syntax_getArg(v___x_5172_, v___x_5136_);
                        lean_dec(v___x_5172_);
                        v___x_5177_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_5177_, 0, v_vis_x3f_5176_);
                        v___y_5138_ = v___x_5171_;
                        v___y_5139_ = v_doc_x3f_5168_;
                        v_vis_x3f_5140_ = v___x_5177_;
                        v___y_5141_ = v___y_5169_;
                        v___y_5142_ = v___y_5170_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5172_);
                    v___x_5178_ = lean_box(0);
                    v___y_5138_ = v___x_5171_;
                    v___y_5139_ = v_doc_x3f_5168_;
                    v_vis_x3f_5140_ = v___x_5178_;
                    v___y_5141_ = v___y_5169_;
                    v___y_5142_ = v___y_5170_;
                    state = 6;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___boxed(
    mut v_x_5190_: *mut LeanObject,
    mut v_a_5191_: *mut LeanObject,
    mut v_a_5192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5193_: *mut LeanObject = core::ptr::null_mut();
    v_res_5193_ = l_Lean_Elab_ConfigEval_elabDeclareTacticConfig(v_x_5190_, v_a_5191_, v_a_5192_);
    lean_dec_ref(v_a_5191_);
    return v_res_5193_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1()
-> *mut LeanObject {
    let mut v___x_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut LeanObject = core::ptr::null_mut();
    v___x_5201_ = l_Lean_Elab_macroAttribute;
    v___x_5202_ = l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1;
    v___x_5203_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1;
    v___x_5204_ = lean_alloc_closure(
        l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_5205_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5201_,
        v___x_5202_,
        v___x_5203_,
        v___x_5204_,
    );
    return v___x_5205_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___boxed(
    mut v_a_5206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5207_: *mut LeanObject = core::ptr::null_mut();
    v_res_5207_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1();
    return v_res_5207_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig(
    mut v_a_5208_: *mut LeanObject,
    mut v_a_5209_: *mut LeanObject,
    mut v_a_5210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    v___x_5212_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0;
    v___x_5213_ = lean_unsigned_to_nat(2);
    v___x_5214_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(
        v___x_5212_,
        v___x_5213_,
        v_a_5208_,
        v_a_5209_,
        v_a_5210_,
    );
    return v___x_5214_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___boxed(
    mut v_a_5215_: *mut LeanObject,
    mut v_a_5216_: *mut LeanObject,
    mut v_a_5217_: *mut LeanObject,
    mut v_a_5218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5219_: *mut LeanObject = core::ptr::null_mut();
    v_res_5219_ =
        l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig(
            v_a_5215_, v_a_5216_, v_a_5217_,
        );
    lean_dec(v_a_5217_);
    lean_dec_ref(v_a_5216_);
    lean_dec(v_a_5215_);
    return v_res_5219_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0()
-> *mut LeanObject {
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    v___x_5220_ = lean_alloc_closure(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___boxed as *mut core::ffi::c_void, 4, 0);
    v___x_5221_ = lean_alloc_closure(
        l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_5221_, 0, v___x_5220_);
    return v___x_5221_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1()
-> *mut LeanObject {
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
    v___x_5223_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1;
    v___x_5224_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0_once), _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0);
    v___x_5225_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_5223_, v___x_5224_);
    return v___x_5225_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___boxed(
    mut v_a_5226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5227_: *mut LeanObject = core::ptr::null_mut();
    v_res_5227_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1();
    return v_res_5227_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1()
-> *mut LeanObject {
    let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
    v___x_5229_ = l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__0;
    v___x_5230_ = l_String_toRawSubstring_x27(v___x_5229_);
    return v___x_5230_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1(
    mut v___x_5232_: *mut LeanObject,
    mut v___x_5233_: *mut LeanObject,
    mut v___x_5234_: *mut LeanObject,
    mut v___x_5235_: *mut LeanObject,
    mut v___x_5236_: *mut LeanObject,
    mut v_eval_5237_: *mut LeanObject,
    mut v___y_5238_: *mut LeanObject,
    mut v___y_5239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_quotContext_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: u8 = 0;
    let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    v_quotContext_5240_ = lean_ctor_get(v___y_5238_, 1);
    v_currMacroScope_5241_ = lean_ctor_get(v___y_5238_, 2);
    v_ref_5242_ = lean_ctor_get(v___y_5238_, 5);
    v___x_5243_ = 0;
    v___x_5244_ = l_Lean_SourceInfo_fromRef(v_ref_5242_, v___x_5243_);
    v___x_5245_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81;
    lean_inc_ref(v___x_5232_);
    v___x_5246_ = l_Lean_Name_mkStr4(v___x_5232_, v___x_5233_, v___x_5234_, v___x_5245_);
    v___x_5247_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1,
    );
    v___x_5248_ = l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__2;
    lean_inc_ref(v___x_5235_);
    v___x_5249_ = l_Lean_Name_mkStr2(v___x_5235_, v___x_5248_);
    lean_inc(v_currMacroScope_5241_);
    lean_inc(v_quotContext_5240_);
    v___x_5250_ = l_Lean_addMacroScope(v_quotContext_5240_, v___x_5249_, v_currMacroScope_5241_);
    v___x_5251_ = l_Lean_Name_mkStr4(v___x_5232_, v___x_5236_, v___x_5235_, v___x_5248_);
    v___x_5252_ = lean_box(0);
    v___x_5253_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5253_, 0, v___x_5251_);
    lean_ctor_set(v___x_5253_, 1, v___x_5252_);
    v___x_5254_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5254_, 0, v___x_5253_);
    lean_ctor_set(v___x_5254_, 1, v___x_5252_);
    lean_inc_n(v___x_5244_, 2);
    v___x_5255_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_5255_, 0, v___x_5244_);
    lean_ctor_set(v___x_5255_, 1, v___x_5247_);
    lean_ctor_set(v___x_5255_, 2, v___x_5250_);
    lean_ctor_set(v___x_5255_, 3, v___x_5254_);
    v___x_5256_ = l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__5;
    v___x_5257_ = l_Lean_Syntax_node1(v___x_5244_, v___x_5256_, v_eval_5237_);
    v___x_5258_ = l_Lean_Syntax_node2(v___x_5244_, v___x_5246_, v___x_5255_, v___x_5257_);
    v___x_5259_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5259_, 0, v___x_5258_);
    lean_ctor_set(v___x_5259_, 1, v___y_5239_);
    return v___x_5259_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___boxed(
    mut v___x_5260_: *mut LeanObject,
    mut v___x_5261_: *mut LeanObject,
    mut v___x_5262_: *mut LeanObject,
    mut v___x_5263_: *mut LeanObject,
    mut v___x_5264_: *mut LeanObject,
    mut v_eval_5265_: *mut LeanObject,
    mut v___y_5266_: *mut LeanObject,
    mut v___y_5267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5268_: *mut LeanObject = core::ptr::null_mut();
    v_res_5268_ = l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1(
        v___x_5260_,
        v___x_5261_,
        v___x_5262_,
        v___x_5263_,
        v___x_5264_,
        v_eval_5265_,
        v___y_5266_,
        v___y_5267_,
    );
    lean_dec_ref(v___y_5266_);
    return v_res_5268_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5() -> *mut LeanObject
{
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    v___x_5287_ = l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4;
    v___x_5288_ = l_Lean_mkCIdent(v___x_5287_);
    return v___x_5288_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeclareCommandConfig(
    mut v_x_5289_: *mut LeanObject,
    mut v_a_5290_: *mut LeanObject,
    mut v_a_5291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: u8 = 0;
    let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_x3f_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binders_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5315_: u8 = 0;
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5319_: u8 = 0;
    let mut v_a_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5324_: u8 = 0;
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5328_: u8 = 0;
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vis_x3f_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elabName_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: u8 = 0;
    let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: u8 = 0;
    let mut v___x_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: u8 = 0;
    let mut v___x_5352_: u8 = 0;
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_x3f_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: u8 = 0;
    let mut v___x_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: u8 = 0;
    let mut v___x_5367_: u8 = 0;
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vis_x3f_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: u8 = 0;
    let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: u8 = 0;
    let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: u8 = 0;
    let mut v___x_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5292_ = l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1;
                lean_inc(v_x_5289_);
                v___x_5293_ = l_Lean_Syntax_isOfKind(v_x_5289_, v___x_5292_);
                if v___x_5293_ == 0 {
                    lean_dec(v_x_5289_);
                    v___x_5294_ = l_Lean_Macro_throwUnsupported___redArg(v_a_5291_);
                    return v___x_5294_;
                } else {
                    v___f_5295_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__2;
                    v___x_5329_ = lean_unsigned_to_nat(0);
                    v___x_5372_ = l_Lean_Syntax_getArg(v_x_5289_, v___x_5329_);
                    v___x_5373_ = l_Lean_Syntax_isNone(v___x_5372_);
                    if v___x_5373_ == 0 {
                        v___x_5374_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_5372_);
                        v___x_5375_ = l_Lean_Syntax_matchesNull(v___x_5372_, v___x_5374_);
                        if v___x_5375_ == 0 {
                            lean_dec(v___x_5372_);
                            lean_dec(v_x_5289_);
                            v___x_5376_ = l_Lean_Macro_throwUnsupported___redArg(v_a_5291_);
                            return v___x_5376_;
                        } else {
                            v_doc_x3f_5377_ = l_Lean_Syntax_getArg(v___x_5372_, v___x_5329_);
                            lean_dec(v___x_5372_);
                            v___x_5378_ =
                                l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4;
                            lean_inc(v_doc_x3f_5377_);
                            v___x_5379_ = l_Lean_Syntax_isOfKind(v_doc_x3f_5377_, v___x_5378_);
                            if v___x_5379_ == 0 {
                                lean_dec(v_doc_x3f_5377_);
                                lean_dec(v_x_5289_);
                                v___x_5380_ = l_Lean_Macro_throwUnsupported___redArg(v_a_5291_);
                                return v___x_5380_;
                            } else {
                                v___x_5381_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_5381_, 0, v_doc_x3f_5377_);
                                v_doc_x3f_5361_ = v___x_5381_;
                                v___y_5362_ = v_a_5290_;
                                v___y_5363_ = v_a_5291_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_5372_);
                        v___x_5382_ = lean_box(0);
                        v_doc_x3f_5361_ = v___x_5382_;
                        v___y_5362_ = v_a_5290_;
                        v___y_5363_ = v_a_5291_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_binders_5306_ = l_Lean_Syntax_getArgs(v___y_5298_);
                lean_dec(v___y_5298_);
                v___f_5307_ = l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__2;
                v___x_5308_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5,
                );
                v___x_5309_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8,
                );
                v___x_5310_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_5308_, v___f_5307_, v___x_5309_, v___f_5295_, v___y_5302_, v___y_5301_, v___y_5300_, v___y_5297_, v___y_5299_, v_binders_5306_, v_entries_x3f_5303_, v___y_5304_, v___y_5305_);
                if lean_obj_tag(v___x_5310_) == 0 {
                    v_a_5311_ = lean_ctor_get(v___x_5310_, 0);
                    v_a_5312_ = lean_ctor_get(v___x_5310_, 1);
                    v_isSharedCheck_5319_ = (!lean_is_exclusive(v___x_5310_)) as u8;
                    if v_isSharedCheck_5319_ == 0 {
                        v___x_5314_ = v___x_5310_;
                        v_isShared_5315_ = v_isSharedCheck_5319_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5312_);
                        lean_inc(v_a_5311_);
                        lean_dec(v___x_5310_);
                        v___x_5314_ = lean_box(0);
                        v_isShared_5315_ = v_isSharedCheck_5319_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_5320_ = lean_ctor_get(v___x_5310_, 0);
                    v_a_5321_ = lean_ctor_get(v___x_5310_, 1);
                    v_isSharedCheck_5328_ = (!lean_is_exclusive(v___x_5310_)) as u8;
                    if v_isSharedCheck_5328_ == 0 {
                        v___x_5323_ = v___x_5310_;
                        v_isShared_5324_ = v_isSharedCheck_5328_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5321_);
                        lean_inc(v_a_5320_);
                        lean_dec(v___x_5310_);
                        v___x_5323_ = lean_box(0);
                        v_isShared_5324_ = v_isSharedCheck_5328_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5315_ == 0 {
                    v___x_5317_ = v___x_5314_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_a_5311_);
                    lean_ctor_set(v_reuseFailAlloc_5318_, 1, v_a_5312_);
                    v___x_5317_ = v_reuseFailAlloc_5318_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5317_;
            }
            4 => {
                if v_isShared_5324_ == 0 {
                    v___x_5326_ = v___x_5323_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5327_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_a_5320_);
                    lean_ctor_set(v_reuseFailAlloc_5327_, 1, v_a_5321_);
                    v___x_5326_ = v_reuseFailAlloc_5327_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5326_;
            }
            6 => {
                v___x_5336_ = lean_unsigned_to_nat(3);
                v_elabName_5337_ = l_Lean_Syntax_getArg(v_x_5289_, v___x_5336_);
                v___x_5338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13;
                lean_inc(v_elabName_5337_);
                v___x_5339_ = l_Lean_Syntax_isOfKind(v_elabName_5337_, v___x_5338_);
                if v___x_5339_ == 0 {
                    lean_dec(v_elabName_5337_);
                    lean_dec(v_vis_x3f_5333_);
                    lean_dec(v___y_5331_);
                    lean_dec(v_x_5289_);
                    v___x_5340_ = l_Lean_Macro_throwUnsupported___redArg(v___y_5335_);
                    return v___x_5340_;
                } else {
                    v___x_5341_ = lean_unsigned_to_nat(4);
                    v_type_5342_ = l_Lean_Syntax_getArg(v_x_5289_, v___x_5341_);
                    lean_inc(v_type_5342_);
                    v___x_5343_ = l_Lean_Syntax_isOfKind(v_type_5342_, v___x_5338_);
                    if v___x_5343_ == 0 {
                        lean_dec(v_type_5342_);
                        lean_dec(v_elabName_5337_);
                        lean_dec(v_vis_x3f_5333_);
                        lean_dec(v___y_5331_);
                        lean_dec(v_x_5289_);
                        v___x_5344_ = l_Lean_Macro_throwUnsupported___redArg(v___y_5335_);
                        return v___x_5344_;
                    } else {
                        v___x_5345_ = lean_unsigned_to_nat(2);
                        v_tk_5346_ = l_Lean_Syntax_getArg(v_x_5289_, v___x_5345_);
                        v___x_5347_ = lean_unsigned_to_nat(5);
                        v___x_5348_ = l_Lean_Syntax_getArg(v_x_5289_, v___x_5347_);
                        v___x_5349_ = lean_unsigned_to_nat(6);
                        v___x_5350_ = l_Lean_Syntax_getArg(v_x_5289_, v___x_5349_);
                        lean_dec(v_x_5289_);
                        v___x_5351_ = l_Lean_Syntax_isNone(v___x_5350_);
                        if v___x_5351_ == 0 {
                            lean_inc(v___x_5350_);
                            v___x_5352_ = l_Lean_Syntax_matchesNull(v___x_5350_, v___y_5332_);
                            if v___x_5352_ == 0 {
                                lean_dec(v___x_5350_);
                                lean_dec(v___x_5348_);
                                lean_dec(v_tk_5346_);
                                lean_dec(v_type_5342_);
                                lean_dec(v_elabName_5337_);
                                lean_dec(v_vis_x3f_5333_);
                                lean_dec(v___y_5331_);
                                v___x_5353_ = l_Lean_Macro_throwUnsupported___redArg(v___y_5335_);
                                return v___x_5353_;
                            } else {
                                v_entries_x3f_5354_ =
                                    l_Lean_Syntax_getArg(v___x_5350_, v___x_5329_);
                                lean_dec(v___x_5350_);
                                v___x_5355_ =
                                    l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3;
                                lean_inc(v_entries_x3f_5354_);
                                v___x_5356_ =
                                    l_Lean_Syntax_isOfKind(v_entries_x3f_5354_, v___x_5355_);
                                if v___x_5356_ == 0 {
                                    lean_dec(v_entries_x3f_5354_);
                                    lean_dec(v___x_5348_);
                                    lean_dec(v_tk_5346_);
                                    lean_dec(v_type_5342_);
                                    lean_dec(v_elabName_5337_);
                                    lean_dec(v_vis_x3f_5333_);
                                    lean_dec(v___y_5331_);
                                    v___x_5357_ =
                                        l_Lean_Macro_throwUnsupported___redArg(v___y_5335_);
                                    return v___x_5357_;
                                } else {
                                    v___x_5358_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_5358_, 0, v_entries_x3f_5354_);
                                    v___y_5297_ = v_elabName_5337_;
                                    v___y_5298_ = v___x_5348_;
                                    v___y_5299_ = v_type_5342_;
                                    v___y_5300_ = v_tk_5346_;
                                    v___y_5301_ = v_vis_x3f_5333_;
                                    v___y_5302_ = v___y_5331_;
                                    v_entries_x3f_5303_ = v___x_5358_;
                                    v___y_5304_ = v___y_5334_;
                                    v___y_5305_ = v___y_5335_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_5350_);
                            v___x_5359_ = lean_box(0);
                            v___y_5297_ = v_elabName_5337_;
                            v___y_5298_ = v___x_5348_;
                            v___y_5299_ = v_type_5342_;
                            v___y_5300_ = v_tk_5346_;
                            v___y_5301_ = v_vis_x3f_5333_;
                            v___y_5302_ = v___y_5331_;
                            v_entries_x3f_5303_ = v___x_5359_;
                            v___y_5304_ = v___y_5334_;
                            v___y_5305_ = v___y_5335_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            7 => {
                v___x_5364_ = lean_unsigned_to_nat(1);
                v___x_5365_ = l_Lean_Syntax_getArg(v_x_5289_, v___x_5364_);
                v___x_5366_ = l_Lean_Syntax_isNone(v___x_5365_);
                if v___x_5366_ == 0 {
                    lean_inc(v___x_5365_);
                    v___x_5367_ = l_Lean_Syntax_matchesNull(v___x_5365_, v___x_5364_);
                    if v___x_5367_ == 0 {
                        lean_dec(v___x_5365_);
                        lean_dec(v_doc_x3f_5361_);
                        lean_dec(v_x_5289_);
                        v___x_5368_ = l_Lean_Macro_throwUnsupported___redArg(v___y_5363_);
                        return v___x_5368_;
                    } else {
                        v_vis_x3f_5369_ = l_Lean_Syntax_getArg(v___x_5365_, v___x_5329_);
                        lean_dec(v___x_5365_);
                        v___x_5370_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_5370_, 0, v_vis_x3f_5369_);
                        v___y_5331_ = v_doc_x3f_5361_;
                        v___y_5332_ = v___x_5364_;
                        v_vis_x3f_5333_ = v___x_5370_;
                        v___y_5334_ = v___y_5362_;
                        v___y_5335_ = v___y_5363_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5365_);
                    v___x_5371_ = lean_box(0);
                    v___y_5331_ = v_doc_x3f_5361_;
                    v___y_5332_ = v___x_5364_;
                    v_vis_x3f_5333_ = v___x_5371_;
                    v___y_5334_ = v___y_5362_;
                    v___y_5335_ = v___y_5363_;
                    state = 6;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___boxed(
    mut v_x_5383_: *mut LeanObject,
    mut v_a_5384_: *mut LeanObject,
    mut v_a_5385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5386_: *mut LeanObject = core::ptr::null_mut();
    v_res_5386_ = l_Lean_Elab_ConfigEval_elabDeclareCommandConfig(v_x_5383_, v_a_5384_, v_a_5385_);
    lean_dec_ref(v_a_5384_);
    return v_res_5386_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1()
-> *mut LeanObject {
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut LeanObject = core::ptr::null_mut();
    v___x_5394_ = l_Lean_Elab_macroAttribute;
    v___x_5395_ = l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1;
    v___x_5396_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1;
    v___x_5397_ = lean_alloc_closure(
        l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_5398_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5394_,
        v___x_5395_,
        v___x_5396_,
        v___x_5397_,
    );
    return v___x_5398_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___boxed(
    mut v_a_5399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5400_: *mut LeanObject = core::ptr::null_mut();
    v_res_5400_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1();
    return v_res_5400_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab(
    mut v_a_5401_: *mut LeanObject,
    mut v_a_5402_: *mut LeanObject,
    mut v_a_5403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut LeanObject = core::ptr::null_mut();
    v___x_5405_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0;
    v___x_5406_ = lean_unsigned_to_nat(2);
    v___x_5407_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(
        v___x_5405_,
        v___x_5406_,
        v_a_5401_,
        v_a_5402_,
        v_a_5403_,
    );
    return v___x_5407_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___boxed(
    mut v_a_5408_: *mut LeanObject,
    mut v_a_5409_: *mut LeanObject,
    mut v_a_5410_: *mut LeanObject,
    mut v_a_5411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5412_: *mut LeanObject = core::ptr::null_mut();
    v_res_5412_ =
        l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab(
            v_a_5408_, v_a_5409_, v_a_5410_,
        );
    lean_dec(v_a_5410_);
    lean_dec_ref(v_a_5409_);
    lean_dec(v_a_5408_);
    return v_res_5412_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0()
-> *mut LeanObject {
    let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    v___x_5413_ = lean_alloc_closure(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___boxed as *mut core::ffi::c_void, 4, 0);
    v___x_5414_ = lean_alloc_closure(
        l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_5414_, 0, v___x_5413_);
    return v___x_5414_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1()
-> *mut LeanObject {
    let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    v___x_5416_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1;
    v___x_5417_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0_once), _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0);
    v___x_5418_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_5416_, v___x_5417_);
    return v___x_5418_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___boxed(
    mut v_a_5419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5420_: *mut LeanObject = core::ptr::null_mut();
    v_res_5420_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1();
    return v_res_5420_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ConfigEval_Builtins(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_ConfigEval_Commands(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_MissingDocs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ConfigEval_Builtins(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_ConfigEval_Builtins(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_ConfigEval_Commands(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Linter_MissingDocs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Builtins(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ConfigEval_Builtins(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_ConfigEval_Builtins(builtin);
}
