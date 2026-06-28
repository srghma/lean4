// Lean compiler output
// Module: Lake.DSL.DeclUtil
// Imports: Lake.Util.Binder Lake.Config.MetaClasses Lean.Elab.Command
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_TSepArray_getElems___redArg, l_Lean_Syntax_isNone, l_Lean_Syntax_mkSep,
    l_Lean_TSyntax_getId, l_Lean_TSyntax_getString, l_Lean_mkIdentFrom, l_Lean_mkOptionalNode,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getHeadInfo,
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node5, l_Lean_Syntax_node7, l_Lean_addMacroScope, l_Lean_replaceRef,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Lake::Config::MetaClasses::{
    initialize_Lake_Config_MetaClasses, runtime_initialize_Lake_Config_MetaClasses,
};
use crate::r#gen::Lake::Util::Binder::{
    initialize_Lake_Util_Binder, runtime_initialize_Lake_Util_Binder,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_elabCommand___boxed,
    l_Lean_Elab_Command_getCurrMacroScope___redArg, l_Lean_Elab_Command_getRef___redArg,
    l_Lean_Elab_Command_getScope___redArg,
    l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM,
    l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed,
    l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed,
    l_Lean_Elab_Command_instMonadEnvCommandElabM,
    l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM,
    l_Lean_Elab_Command_instMonadRefCommandElabM, l_Lean_Elab_Command_withFreshMacroScope___redArg,
    l_Lean_Elab_Command_withMacroExpansion___redArg, runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Environment::{l_Lean_Environment_header, l_Lean_getMainModule___redArg};
use crate::r#gen::Lean::Exception::l_Lean_throwErrorAt___redArg;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag,
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_MessageData_ofSyntax, l_Lean_MessageLog_add, l_Lean_indentD,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_Lake_DSL_packageDeclName___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [95, 112, 97, 99, 107, 97, 103, 101, 0],
    };
static mut l_Lake_DSL_packageDeclName___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageDeclName___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageDeclName___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageDeclName___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17191938545305502623 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageDeclName___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageDeclName___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_packageDeclName: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageDeclName___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandAttrs___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lake_DSL_expandAttrs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandAttrs___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lake_DSL_expandAttrs___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandAttrs___closed__2_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lake_DSL_expandAttrs___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandAttrs___closed__3_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0],
    };
static mut l_Lake_DSL_expandAttrs___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_expandAttrs___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_expandAttrs___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_expandAttrs___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_expandAttrs___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__3_value)
                as *mut crate::leanh::LeanObject,
            2533412339571800130 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandAttrs___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandAttrs___closed__5_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_DSL_expandAttrs___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_identOrStr___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [105, 100, 101, 110, 116, 79, 114, 83, 116, 114, 0],
    };
static mut l_Lake_DSL_identOrStr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_identOrStr___closed__1_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [76, 97, 107, 101, 0],
    };
static mut l_Lake_DSL_identOrStr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_identOrStr___closed__2_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [68, 83, 76, 0],
    };
static mut l_Lake_DSL_identOrStr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_identOrStr___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_identOrStr___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_identOrStr___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3600053300008893637 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_identOrStr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_identOrStr___closed__4_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [111, 114, 101, 108, 115, 101, 0],
    };
static mut l_Lake_DSL_identOrStr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_identOrStr___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__4_value)
                as *mut crate::leanh::LeanObject,
            393173242845875278 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_identOrStr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_identOrStr___closed__6_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [105, 100, 101, 110, 116, 0],
    };
static mut l_Lake_DSL_identOrStr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_identOrStr___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__6_value)
                as *mut crate::leanh::LeanObject,
            5117844058249666356 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_identOrStr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_identOrStr___closed__8_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__7_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_identOrStr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_identOrStr___closed__9_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [115, 116, 114, 0],
    };
static mut l_Lake_DSL_identOrStr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_identOrStr___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__9_value)
                as *mut crate::leanh::LeanObject,
            9232979286016572671 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_identOrStr___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_identOrStr___closed__11_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_identOrStr___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_identOrStr___closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_identOrStr___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_identOrStr___closed__13_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_identOrStr___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__13_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_identOrStr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declField___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [100, 101, 99, 108, 70, 105, 101, 108, 100, 0],
    };
static mut l_Lake_DSL_declField___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declField___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_declField___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_declField___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_declField___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13249778076259124224 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declField___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declField___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declField___closed__2_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Lake_DSL_declField___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declField___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declField___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__2_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declField___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declField___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declField___closed__4_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [32, 58, 61, 32, 0],
    };
static mut l_Lake_DSL_declField___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declField___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declField___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_declField___closed__4_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_declField___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declField___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declField___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declField___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declField___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declField___closed__7_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lake_DSL_declField___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declField___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declField___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__7_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declField___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declField___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declField___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__8_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declField___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declField___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declField___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declField___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declField___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declField___closed__11_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declField___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declField___closed__11_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_declField: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declField___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_structVal___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [115, 116, 114, 117, 99, 116, 86, 97, 108, 0],
    };
static mut l_Lake_DSL_structVal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_structVal___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_structVal___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_structVal___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_structVal___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_structVal___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_structVal___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_structVal___closed__0_value)
                as *mut crate::leanh::LeanObject,
            10845500395294116975 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_structVal___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_structVal___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_structVal___closed__2_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [123, 0],
    };
static mut l_Lake_DSL_structVal___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_structVal___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_structVal___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_structVal___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_structVal___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_structVal___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_structVal___closed__4_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 115, 0,
        ],
    };
static mut l_Lake_DSL_structVal___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_structVal___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_structVal___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_structVal___closed__4_value)
                as *mut crate::leanh::LeanObject,
            14407125511728798128 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_structVal___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_structVal___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_structVal___closed__6_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            115, 101, 112, 66, 121, 73, 110, 100, 101, 110, 116, 83, 101, 109, 105, 99, 111, 108,
            111, 110, 0,
        ],
    };
static mut l_Lake_DSL_structVal___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_structVal___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_structVal___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_structVal___closed__6_value)
                as *mut crate::leanh::LeanObject,
            8450841259565682059 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_structVal___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_structVal___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_structVal___closed__8_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_DSL_structVal___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_structVal___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_structVal___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_structVal___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_DSL_structVal___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_structVal___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_structVal___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_structVal___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_structVal___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_structVal___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_structVal___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_structVal___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_structVal___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_structVal___closed__11_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [125, 0],
    };
static mut l_Lake_DSL_structVal___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_structVal___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_structVal___closed__12_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_structVal___closed__11_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_structVal___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_structVal___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_structVal___closed__13_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_structVal___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_structVal___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_structVal___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_structVal___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_structVal___closed__14_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_structVal___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_structVal___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_structVal___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_structVal___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_structVal___closed__14_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_structVal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_structVal___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValDo___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [100, 101, 99, 108, 86, 97, 108, 68, 111, 0],
    };
static mut l_Lake_DSL_declValDo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_declValDo___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_declValDo___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_declValDo___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11022427548561232637 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declValDo___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValDo___closed__2_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [112, 112, 83, 112, 97, 99, 101, 0],
    };
static mut l_Lake_DSL_declValDo___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValDo___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__2_value)
                as *mut crate::leanh::LeanObject,
            17761616517784022991 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declValDo___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValDo___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__3_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_declValDo___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValDo___closed__5_value: crate::leanh::LeanStringObject<3> =
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
static mut l_Lake_DSL_declValDo___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_declValDo___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_declValDo___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__6_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_declValDo___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__6_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_declValDo___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__6_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__5_value)
                as *mut crate::leanh::LeanObject,
            5817315006727311029 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declValDo___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValDo___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 8,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__6_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_declValDo___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValDo___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declValDo___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValDo___closed__9_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0],
    };
static mut l_Lake_DSL_declValDo___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValDo___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__9_value)
                as *mut crate::leanh::LeanObject,
            18170484695678750185 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declValDo___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValDo___closed__11_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [119, 104, 101, 114, 101, 68, 101, 99, 108, 115, 0],
    };
static mut l_Lake_DSL_declValDo___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__11_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_declValDo___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_declValDo___closed__12_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__12_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_declValDo___closed__12_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__12_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_declValDo___closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__12_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__11_value)
                as *mut crate::leanh::LeanObject,
            4503069825835506739 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declValDo___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValDo___closed__13_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 8,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__12_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_declValDo___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValDo___closed__14_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declValDo___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValDo___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declValDo___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValDo___closed__16_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declValDo___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__16_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_declValDo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValStruct___closed__0_value: crate::leanh::LeanStringObject<14> =
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
            100, 101, 99, 108, 86, 97, 108, 83, 116, 114, 117, 99, 116, 0,
        ],
    };
static mut l_Lake_DSL_declValStruct___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValStruct___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_declValStruct___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_declValStruct___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declValStruct___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_declValStruct___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declValStruct___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValStruct___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1004026287653508741 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declValStruct___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValStruct___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValStruct___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_structVal___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declValStruct___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValStruct___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValStruct___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValStruct___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declValStruct___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValStruct___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValStruct___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_declValStruct___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValStruct___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValStruct___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declValStruct___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValStruct___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_declValStruct: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValStruct___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValWhere___closed__0_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [100, 101, 99, 108, 86, 97, 108, 87, 104, 101, 114, 101, 0],
    };
static mut l_Lake_DSL_declValWhere___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValWhere___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_declValWhere___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_declValWhere___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declValWhere___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_declValWhere___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declValWhere___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValWhere___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5906021167542994327 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declValWhere___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValWhere___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValWhere___closed__2_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [32, 119, 104, 101, 114, 101, 32, 0],
    };
static mut l_Lake_DSL_declValWhere___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValWhere___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValWhere___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_declValWhere___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declValWhere___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValWhere___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValWhere___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValWhere___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_structVal___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declValWhere___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValWhere___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValWhere___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValWhere___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declValWhere___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValWhere___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_declValWhere___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_declValWhere___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValWhere___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValWhere___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_declValWhere___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValWhere___closed__6_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_declValWhere: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_declValWhere___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_simpleDeclSig___closed__0_value: crate::leanh::LeanStringObject<14> =
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
            115, 105, 109, 112, 108, 101, 68, 101, 99, 108, 83, 105, 103, 0,
        ],
    };
static mut l_Lake_DSL_simpleDeclSig___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_simpleDeclSig___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_simpleDeclSig___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_simpleDeclSig___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__0_value)
                as *mut crate::leanh::LeanObject,
            524234751356640840 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_simpleDeclSig___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_simpleDeclSig___closed__2_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0],
    };
static mut l_Lake_DSL_simpleDeclSig___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_simpleDeclSig___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_simpleDeclSig___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_simpleDeclSig___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_simpleDeclSig___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__3_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__2_value)
                as *mut crate::leanh::LeanObject,
            4498178684837002829 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_simpleDeclSig___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_simpleDeclSig___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 8,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_simpleDeclSig___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_simpleDeclSig___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_simpleDeclSig___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_simpleDeclSig___closed__6_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [67, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lake_DSL_simpleDeclSig___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_simpleDeclSig___closed__7_value: crate::leanh::LeanStringObject<14> =
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
            100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0,
        ],
    };
static mut l_Lake_DSL_simpleDeclSig___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_simpleDeclSig___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_simpleDeclSig___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__8_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_simpleDeclSig___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__8_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_simpleDeclSig___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__8_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__7_value)
                as *mut crate::leanh::LeanObject,
            13585030837571646948 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_simpleDeclSig___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_simpleDeclSig___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 8,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_simpleDeclSig___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_simpleDeclSig___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_simpleDeclSig___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_simpleDeclSig___closed__11_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_simpleDeclSig___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_simpleDeclSig: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_optConfig___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
    };
static mut l_Lake_DSL_optConfig___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_optConfig___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_optConfig___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_optConfig___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_optConfig___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_optConfig___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_optConfig___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_optConfig___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2937396280676515247 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_optConfig___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_optConfig___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_optConfig___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValWhere___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declValStruct___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_optConfig___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_optConfig___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_optConfig___closed__3_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_optConfig___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_optConfig___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_optConfig___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_optConfig___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_optConfig___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_optConfig___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_optConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_optConfig___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_optConfig___closed__4_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_optConfig: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_optConfig___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_bracketedSimpleBinder___closed__0_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            98, 114, 97, 99, 107, 101, 116, 101, 100, 83, 105, 109, 112, 108, 101, 66, 105, 110,
            100, 101, 114, 0,
        ],
    };
static mut l_Lake_DSL_bracketedSimpleBinder___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_bracketedSimpleBinder___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_bracketedSimpleBinder___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_bracketedSimpleBinder___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5586398111930117255 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_bracketedSimpleBinder___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_bracketedSimpleBinder___closed__2_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [40, 0],
    };
static mut l_Lake_DSL_bracketedSimpleBinder___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_bracketedSimpleBinder___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_bracketedSimpleBinder___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_bracketedSimpleBinder___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_bracketedSimpleBinder___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_bracketedSimpleBinder___closed__5_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [32, 58, 32, 0],
    };
static mut l_Lake_DSL_bracketedSimpleBinder___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_bracketedSimpleBinder___closed__6_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_bracketedSimpleBinder___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_bracketedSimpleBinder___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_bracketedSimpleBinder___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_bracketedSimpleBinder___closed__8_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_DSL_declValDo___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_bracketedSimpleBinder___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_bracketedSimpleBinder___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_bracketedSimpleBinder___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_bracketedSimpleBinder___closed__10_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [41, 0],
    };
static mut l_Lake_DSL_bracketedSimpleBinder___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_bracketedSimpleBinder___closed__11_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_bracketedSimpleBinder___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_bracketedSimpleBinder___closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_declField___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_bracketedSimpleBinder___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_bracketedSimpleBinder___closed__13_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_bracketedSimpleBinder___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_bracketedSimpleBinder: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_simpleBinder___closed__0_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [115, 105, 109, 112, 108, 101, 66, 105, 110, 100, 101, 114, 0],
    };
static mut l_Lake_DSL_simpleBinder___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_simpleBinder___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_simpleBinder___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_simpleBinder___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_simpleBinder___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_simpleBinder___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_simpleBinder___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_simpleBinder___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2660935129428660282 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_simpleBinder___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_simpleBinder___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_simpleBinder___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_bracketedSimpleBinder___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_simpleBinder___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_simpleBinder___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_simpleBinder___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_simpleBinder___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_simpleBinder___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_simpleBinder___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_simpleBinder___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_simpleBinder___closed__3_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_simpleBinder: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_simpleBinder___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lake_DSL_expandOptSimpleBinder___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_expandOptSimpleBinder___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_expandOptSimpleBinder___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_expandOptSimpleBinder___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_expandOptSimpleBinder___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3984140175429830279 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__2_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Lake_DSL_expandOptSimpleBinder___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__3_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_expandOptSimpleBinder___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_expandOptSimpleBinder___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_expandOptSimpleBinder___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_expandOptSimpleBinder___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__3_value)
                as *mut crate::leanh::LeanObject,
            5346268661279150583 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__5_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_DSL_expandOptSimpleBinder___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_expandOptSimpleBinder___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_expandOptSimpleBinder___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__6_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_expandOptSimpleBinder___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__6_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_expandOptSimpleBinder___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__6_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__5_value)
                as *mut crate::leanh::LeanObject,
            7306243862518720553 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__7_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__7_value)
                as *mut crate::leanh::LeanObject,
            9871775667037945883 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__9_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_DSL_expandOptSimpleBinder___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_expandOptSimpleBinder___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l_Lake_DSL_expandOptSimpleBinder___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_expandOptSimpleBinder___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__11_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_identOrStr___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__12_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__12_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_expandOptSimpleBinder___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_expandOptSimpleBinder___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__13_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_expandOptSimpleBinder___closed__13_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__13_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__14_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__14_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_expandOptSimpleBinder___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_expandOptSimpleBinder___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__15_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_expandOptSimpleBinder___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__15_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__16_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__16_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_expandOptSimpleBinder___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_expandOptSimpleBinder___closed__17_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__17_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__18_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__19_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__20_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__21_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__20_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__22_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__18_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__21_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__23_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__16_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__22_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__24_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__14_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__25_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__24_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__26_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [58, 0],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__27_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lake_DSL_expandOptSimpleBinder___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_expandOptSimpleBinder___closed__28_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__27_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_expandOptSimpleBinder___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__28_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,6117808163008040242 as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__3_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 76, 86, 97, 108, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__3_value) as *mut crate::leanh::LeanObject,14295752356045161913 as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__7_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 68, 101, 102, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
static l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__7_value) as *mut crate::leanh::LeanObject,7440505896048223825 as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__9_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__0_value: crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 102, 105, 101, 108, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 115, 121, 110, 116, 97, 120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [114, 101, 100, 101, 102, 105, 110, 101, 100, 32, 102, 105, 101, 108, 100, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [39, 32, 40, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [39, 32, 105, 115, 32, 97, 110, 32, 97, 108, 105, 97, 115, 32, 111, 102, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [39, 41, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [117, 110, 107, 110, 111, 119, 110, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [39, 32, 102, 105, 101, 108, 100, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__18: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_structVal___closed__4_value)
            as *mut crate::leanh::LeanObject,
        5018042693327868416 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__1_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_expandOptSimpleBinder___closed__28_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,13655884332201764339 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__2_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___closed__0_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0],
    };
static mut l_Lake_DSL_elabConfig___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_elabConfig___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___closed__1_value: crate::leanh::LeanStringObject<14> =
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
            100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0,
        ],
    };
static mut l_Lake_DSL_elabConfig___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_elabConfig___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___closed__2_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0],
    };
static mut l_Lake_DSL_elabConfig___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_elabConfig___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___closed__3_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [100, 101, 102, 0],
    };
static mut l_Lake_DSL_elabConfig___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_elabConfig___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___closed__4_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [100, 101, 99, 108, 73, 100, 0],
    };
static mut l_Lake_DSL_elabConfig___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_elabConfig___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___closed__5_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0],
    };
static mut l_Lake_DSL_elabConfig___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_elabConfig___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_elabConfig___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_elabConfig___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_elabConfig___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_elabConfig___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_elabConfig___closed__8_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_DSL_elabConfig___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_elabConfig___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___closed__9_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_DSL_elabConfig___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_elabConfig___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___closed__10_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [119, 104, 101, 114, 101, 0],
    };
static mut l_Lake_DSL_elabConfig___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_elabConfig___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___closed__11_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            119, 104, 101, 114, 101, 83, 116, 114, 117, 99, 116, 73, 110, 115, 116, 0,
        ],
    };
static mut l_Lake_DSL_elabConfig___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_elabConfig___closed__11_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_elabConfig___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_elabConfig___closed__12_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_elabConfig___closed__12_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_expandAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_elabConfig___closed__12_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_elabConfig___closed__12_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_simpleDeclSig___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_elabConfig___closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_elabConfig___closed__12_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_elabConfig___closed__11_value)
                as *mut crate::leanh::LeanObject,
            7794500365561932708 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_elabConfig___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_elabConfig___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_elabConfig___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_elabConfig___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_DSL_elabConfig___closed__14_value: crate::leanh::LeanStringObject<32> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 99, 111, 110, 102, 105, 103, 117,
            114, 97, 116, 105, 111, 110, 32, 115, 121, 110, 116, 97, 120, 0,
        ],
    };
static mut l_Lake_DSL_elabConfig___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_elabConfig___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_elabConfig___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_elabConfig___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lake_DSL_expandAttrs(
    mut v_attrs_x3f_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_attrs_x3f_1720_) == 1 {
        let mut v_val_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1723_: u8 = 0;
        v_val_1721_ = crate::leanh::lean_ctor_get(v_attrs_x3f_1720_, 0);
        crate::leanh::lean_inc_n(v_val_1721_, 2);
        crate::leanh::lean_dec_ref_known(v_attrs_x3f_1720_, 1);
        v___x_1722_ = l_Lake_DSL_expandAttrs___closed__4;
        v___x_1723_ = l_Lean_Syntax_isOfKind(v_val_1721_, v___x_1722_);
        if v___x_1723_ == 0 {
            let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_val_1721_);
            v___x_1724_ = l_Lake_DSL_expandAttrs___closed__5;
            return v___x_1724_;
        } else {
            let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_attrs_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1725_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1726_ = l_Lean_Syntax_getArg(v_val_1721_, v___x_1725_);
            crate::leanh::lean_dec(v_val_1721_);
            v_attrs_1727_ = l_Lean_Syntax_getArgs(v___x_1726_);
            crate::leanh::lean_dec(v___x_1726_);
            v___x_1728_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_attrs_1727_);
            crate::leanh::lean_dec_ref(v_attrs_1727_);
            return v___x_1728_;
        }
    } else {
        let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_attrs_x3f_1720_);
        v___x_1729_ = l_Lake_DSL_expandAttrs___closed__5;
        return v___x_1729_;
    }
}
pub unsafe fn l_Lake_DSL_expandIdentOrStrAsIdent(
    mut v_stx_1759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: u8 = 0;
    v___x_1760_ = l_Lake_DSL_identOrStr___closed__3;
    crate::leanh::lean_inc(v_stx_1759_);
    v___x_1761_ = l_Lean_Syntax_isOfKind(v_stx_1759_, v___x_1760_);
    if v___x_1761_ == 0 {
        let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_1759_);
        v___x_1762_ = crate::leanh::lean_box(0);
        return v___x_1762_;
    } else {
        let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1766_: u8 = 0;
        v___x_1763_ = crate::leanh::lean_unsigned_to_nat(0);
        v_x_1764_ = l_Lean_Syntax_getArg(v_stx_1759_, v___x_1763_);
        crate::leanh::lean_dec(v_stx_1759_);
        v___x_1765_ = l_Lake_DSL_identOrStr___closed__7;
        crate::leanh::lean_inc(v_x_1764_);
        v___x_1766_ = l_Lean_Syntax_isOfKind(v_x_1764_, v___x_1765_);
        if v___x_1766_ == 0 {
            let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1768_: u8 = 0;
            v___x_1767_ = l_Lake_DSL_identOrStr___closed__10;
            crate::leanh::lean_inc(v_x_1764_);
            v___x_1768_ = l_Lean_Syntax_isOfKind(v_x_1764_, v___x_1767_);
            if v___x_1768_ == 0 {
                let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_x_1764_);
                v___x_1769_ = crate::leanh::lean_box(0);
                return v___x_1769_;
            } else {
                let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1770_ = l_Lean_TSyntax_getString(v_x_1764_);
                v___x_1771_ = crate::leanh::lean_box(0);
                v___x_1772_ = l_Lean_Name_str___override(v___x_1771_, v___x_1770_);
                v___x_1773_ = l_Lean_mkIdentFrom(v_x_1764_, v___x_1772_, v___x_1766_);
                crate::leanh::lean_dec(v_x_1764_);
                return v___x_1773_;
            }
        } else {
            return v_x_1764_;
        }
    }
}
pub unsafe fn _init_l_Lake_DSL_expandOptSimpleBinder___closed__10() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2051_ = l_Lake_DSL_expandOptSimpleBinder___closed__9;
    v___x_2052_ = l_String_toRawSubstring_x27(v___x_2051_);
    return v___x_2052_;
}
pub unsafe fn l_Lake_DSL_expandOptSimpleBinder(
    mut v_stx_x3f_2098_: *mut crate::leanh::LeanObject,
    mut v_a_2099_: *mut crate::leanh::LeanObject,
    mut v_a_2100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: u8 = 0;
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: u8 = 0;
    let mut v_ref_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: u8 = 0;
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: u8 = 0;
    let mut v_ref_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_x3f_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: u8 = 0;
    let mut v___x_2183_: u8 = 0;
    let mut v_ref_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_x3f_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_stx_x3f_2098_) == 0 {
                    v_ref_2101_ = crate::leanh::lean_ctor_get(v_a_2099_, 5);
                    v___x_2102_ = 0;
                    v___x_2103_ = l_Lean_SourceInfo_fromRef(v_ref_2101_, v___x_2102_);
                    v___x_2104_ = l_Lake_DSL_expandOptSimpleBinder___closed__1;
                    v___x_2105_ = l_Lake_DSL_expandOptSimpleBinder___closed__2;
                    crate::leanh::lean_inc(v___x_2103_);
                    v___x_2106_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2106_, 0, v___x_2103_);
                    crate::leanh::lean_ctor_set(v___x_2106_, 1, v___x_2105_);
                    v___x_2107_ = l_Lean_Syntax_node1(v___x_2103_, v___x_2104_, v___x_2106_);
                    v___x_2108_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2108_, 0, v___x_2107_);
                    crate::leanh::lean_ctor_set(v___x_2108_, 1, v_a_2100_);
                    return v___x_2108_;
                } else {
                    v_val_2109_ = crate::leanh::lean_ctor_get(v_stx_x3f_2098_, 0);
                    v_isSharedCheck_2197_ =
                        (!crate::leanh::lean_is_exclusive(v_stx_x3f_2098_)) as u8;
                    if v_isSharedCheck_2197_ == 0 {
                        v___x_2111_ = v_stx_x3f_2098_;
                        v_isShared_2112_ = v_isSharedCheck_2197_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2109_);
                        crate::leanh::lean_dec(v_stx_x3f_2098_);
                        v___x_2111_ = crate::leanh::lean_box(0);
                        v_isShared_2112_ = v_isSharedCheck_2197_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2113_ = l_Lake_DSL_simpleBinder___closed__1;
                crate::leanh::lean_inc(v_val_2109_);
                v___x_2114_ = l_Lean_Syntax_isOfKind(v_val_2109_, v___x_2113_);
                if v___x_2114_ == 0 {
                    crate::leanh::lean_del_object(v___x_2111_);
                    crate::leanh::lean_dec(v_val_2109_);
                    v_ref_2115_ = crate::leanh::lean_ctor_get(v_a_2099_, 5);
                    v___x_2116_ = l_Lean_SourceInfo_fromRef(v_ref_2115_, v___x_2114_);
                    v___x_2117_ = l_Lake_DSL_expandOptSimpleBinder___closed__1;
                    v___x_2118_ = l_Lake_DSL_expandOptSimpleBinder___closed__2;
                    crate::leanh::lean_inc(v___x_2116_);
                    v___x_2119_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2119_, 0, v___x_2116_);
                    crate::leanh::lean_ctor_set(v___x_2119_, 1, v___x_2118_);
                    v___x_2120_ = l_Lean_Syntax_node1(v___x_2116_, v___x_2117_, v___x_2119_);
                    v___x_2121_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2121_, 0, v___x_2120_);
                    crate::leanh::lean_ctor_set(v___x_2121_, 1, v_a_2100_);
                    return v___x_2121_;
                } else {
                    v___x_2122_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2123_ = l_Lean_Syntax_getArg(v_val_2109_, v___x_2122_);
                    crate::leanh::lean_dec(v_val_2109_);
                    v___x_2124_ = l_Lake_DSL_identOrStr___closed__7;
                    crate::leanh::lean_inc(v___x_2123_);
                    v___x_2125_ = l_Lean_Syntax_isOfKind(v___x_2123_, v___x_2124_);
                    if v___x_2125_ == 0 {
                        v___x_2126_ = l_Lake_DSL_bracketedSimpleBinder___closed__1;
                        crate::leanh::lean_inc(v___x_2123_);
                        v___x_2127_ = l_Lean_Syntax_isOfKind(v___x_2123_, v___x_2126_);
                        if v___x_2127_ == 0 {
                            crate::leanh::lean_dec(v___x_2123_);
                            crate::leanh::lean_del_object(v___x_2111_);
                            v_ref_2128_ = crate::leanh::lean_ctor_get(v_a_2099_, 5);
                            v___x_2129_ = l_Lean_SourceInfo_fromRef(v_ref_2128_, v___x_2125_);
                            v___x_2130_ = l_Lake_DSL_expandOptSimpleBinder___closed__1;
                            v___x_2131_ = l_Lake_DSL_expandOptSimpleBinder___closed__2;
                            crate::leanh::lean_inc(v___x_2129_);
                            v___x_2132_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2132_, 0, v___x_2129_);
                            crate::leanh::lean_ctor_set(v___x_2132_, 1, v___x_2131_);
                            v___x_2133_ =
                                l_Lean_Syntax_node1(v___x_2129_, v___x_2130_, v___x_2132_);
                            v___x_2134_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2134_, 0, v___x_2133_);
                            crate::leanh::lean_ctor_set(v___x_2134_, 1, v_a_2100_);
                            return v___x_2134_;
                        } else {
                            v___x_2135_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_2136_ = l_Lean_Syntax_getArg(v___x_2123_, v___x_2135_);
                            v___x_2180_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_2181_ = l_Lean_Syntax_getArg(v___x_2123_, v___x_2180_);
                            crate::leanh::lean_dec(v___x_2123_);
                            v___x_2182_ = l_Lean_Syntax_isNone(v___x_2181_);
                            if v___x_2182_ == 0 {
                                crate::leanh::lean_inc(v___x_2181_);
                                v___x_2183_ = l_Lean_Syntax_matchesNull(v___x_2181_, v___x_2180_);
                                if v___x_2183_ == 0 {
                                    crate::leanh::lean_dec(v___x_2181_);
                                    crate::leanh::lean_dec(v___x_2136_);
                                    crate::leanh::lean_del_object(v___x_2111_);
                                    v_ref_2184_ = crate::leanh::lean_ctor_get(v_a_2099_, 5);
                                    v___x_2185_ =
                                        l_Lean_SourceInfo_fromRef(v_ref_2184_, v___x_2125_);
                                    v___x_2186_ = l_Lake_DSL_expandOptSimpleBinder___closed__1;
                                    v___x_2187_ = l_Lake_DSL_expandOptSimpleBinder___closed__2;
                                    crate::leanh::lean_inc(v___x_2185_);
                                    v___x_2188_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2188_, 0, v___x_2185_);
                                    crate::leanh::lean_ctor_set(v___x_2188_, 1, v___x_2187_);
                                    v___x_2189_ =
                                        l_Lean_Syntax_node1(v___x_2185_, v___x_2186_, v___x_2188_);
                                    v___x_2190_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2190_, 0, v___x_2189_);
                                    crate::leanh::lean_ctor_set(v___x_2190_, 1, v_a_2100_);
                                    return v___x_2190_;
                                } else {
                                    v_ty_x3f_2191_ = l_Lean_Syntax_getArg(v___x_2181_, v___x_2135_);
                                    crate::leanh::lean_dec(v___x_2181_);
                                    if v_isShared_2112_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_2111_, 0, v_ty_x3f_2191_);
                                        v___x_2193_ = v___x_2111_;
                                        state = 4;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2194_ =
                                            crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2194_,
                                            0,
                                            v_ty_x3f_2191_,
                                        );
                                        v___x_2193_ = v_reuseFailAlloc_2194_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_2181_);
                                crate::leanh::lean_del_object(v___x_2111_);
                                v___x_2195_ = crate::leanh::lean_box(0);
                                v_ty_x3f_2165_ = v___x_2195_;
                                v___y_2166_ = v_a_2099_;
                                v___y_2167_ = v_a_2100_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2111_);
                        v___x_2196_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2196_, 0, v___x_2123_);
                        crate::leanh::lean_ctor_set(v___x_2196_, 1, v_a_2100_);
                        return v___x_2196_;
                    }
                }
            }
            2 => {
                v___x_2143_ = l_Lean_SourceInfo_fromRef(v_ref_2141_, v___x_2125_);
                v___x_2144_ = l_Lake_DSL_expandOptSimpleBinder___closed__4;
                v___x_2145_ = l_Lake_DSL_expandOptSimpleBinder___closed__6;
                v___x_2146_ = l_Lake_DSL_bracketedSimpleBinder___closed__2;
                crate::leanh::lean_inc_n(v___x_2143_, 7);
                v___x_2147_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2147_, 0, v___x_2143_);
                crate::leanh::lean_ctor_set(v___x_2147_, 1, v___x_2146_);
                v___x_2148_ = l_Lake_DSL_expandOptSimpleBinder___closed__8;
                v___x_2149_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_DSL_expandOptSimpleBinder___closed__10),
                    core::ptr::addr_of_mut!(l_Lake_DSL_expandOptSimpleBinder___closed__10_once),
                    _init_l_Lake_DSL_expandOptSimpleBinder___closed__10,
                );
                v___x_2150_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_currMacroScope_2140_);
                crate::leanh::lean_inc(v_quotContext_2139_);
                v___x_2151_ =
                    l_Lean_addMacroScope(v_quotContext_2139_, v___x_2150_, v_currMacroScope_2140_);
                v___x_2152_ = l_Lake_DSL_expandOptSimpleBinder___closed__25;
                v___x_2153_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2153_, 0, v___x_2143_);
                crate::leanh::lean_ctor_set(v___x_2153_, 1, v___x_2149_);
                crate::leanh::lean_ctor_set(v___x_2153_, 2, v___x_2151_);
                crate::leanh::lean_ctor_set(v___x_2153_, 3, v___x_2152_);
                v___x_2154_ = l_Lean_Syntax_node1(v___x_2143_, v___x_2148_, v___x_2153_);
                v___x_2155_ =
                    l_Lean_Syntax_node2(v___x_2143_, v___x_2145_, v___x_2147_, v___x_2154_);
                v___x_2156_ = l_Lake_DSL_expandOptSimpleBinder___closed__26;
                v___x_2157_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2157_, 0, v___x_2143_);
                crate::leanh::lean_ctor_set(v___x_2157_, 1, v___x_2156_);
                v___x_2158_ = l_Lake_DSL_expandOptSimpleBinder___closed__28;
                v___x_2159_ = l_Lean_Syntax_node1(v___x_2143_, v___x_2158_, v___y_2142_);
                v___x_2160_ = l_Lake_DSL_bracketedSimpleBinder___closed__10;
                v___x_2161_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2161_, 0, v___x_2143_);
                crate::leanh::lean_ctor_set(v___x_2161_, 1, v___x_2160_);
                v___x_2162_ = l_Lean_Syntax_node5(
                    v___x_2143_,
                    v___x_2144_,
                    v___x_2155_,
                    v___x_2136_,
                    v___x_2157_,
                    v___x_2159_,
                    v___x_2161_,
                );
                v___x_2163_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2163_, 0, v___x_2162_);
                crate::leanh::lean_ctor_set(v___x_2163_, 1, v___y_2138_);
                return v___x_2163_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_ty_x3f_2165_) == 0 {
                    v_quotContext_2168_ = crate::leanh::lean_ctor_get(v___y_2166_, 1);
                    v_currMacroScope_2169_ = crate::leanh::lean_ctor_get(v___y_2166_, 2);
                    v_ref_2170_ = crate::leanh::lean_ctor_get(v___y_2166_, 5);
                    v___x_2171_ = l_Lean_SourceInfo_fromRef(v_ref_2170_, v___x_2125_);
                    v___x_2172_ = l_Lake_DSL_expandOptSimpleBinder___closed__2;
                    crate::leanh::lean_inc(v___x_2171_);
                    v___x_2173_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2173_, 0, v___x_2171_);
                    crate::leanh::lean_ctor_set(v___x_2173_, 1, v___x_2172_);
                    v___x_2174_ = l_Lake_DSL_expandOptSimpleBinder___closed__1;
                    v___x_2175_ = l_Lean_Syntax_node1(v___x_2171_, v___x_2174_, v___x_2173_);
                    v___y_2138_ = v___y_2167_;
                    v_quotContext_2139_ = v_quotContext_2168_;
                    v_currMacroScope_2140_ = v_currMacroScope_2169_;
                    v_ref_2141_ = v_ref_2170_;
                    v___y_2142_ = v___x_2175_;
                    state = 2;
                    continue;
                } else {
                    v_quotContext_2176_ = crate::leanh::lean_ctor_get(v___y_2166_, 1);
                    v_currMacroScope_2177_ = crate::leanh::lean_ctor_get(v___y_2166_, 2);
                    v_ref_2178_ = crate::leanh::lean_ctor_get(v___y_2166_, 5);
                    v_val_2179_ = crate::leanh::lean_ctor_get(v_ty_x3f_2165_, 0);
                    crate::leanh::lean_inc(v_val_2179_);
                    crate::leanh::lean_dec_ref_known(v_ty_x3f_2165_, 1);
                    v___y_2138_ = v___y_2167_;
                    v_quotContext_2139_ = v_quotContext_2176_;
                    v_currMacroScope_2140_ = v_currMacroScope_2177_;
                    v_ref_2141_ = v_ref_2178_;
                    v___y_2142_ = v_val_2179_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_ty_x3f_2165_ = v___x_2193_;
                v___y_2166_ = v_a_2099_;
                v___y_2167_ = v_a_2100_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_DSL_expandOptSimpleBinder___boxed(
    mut v_stx_x3f_2198_: *mut crate::leanh::LeanObject,
    mut v_a_2199_: *mut crate::leanh::LeanObject,
    mut v_a_2200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2201_ = l_Lake_DSL_expandOptSimpleBinder(v_stx_x3f_2198_, v_a_2199_, v_a_2200_);
    crate::leanh::lean_dec_ref(v_a_2199_);
    return v_res_2201_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2202_: u8 = 0;
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2202_ = 0;
    v___x_2203_ = crate::leanh::lean_box(0);
    v___x_2204_ = l_Lean_SourceInfo_fromRef(v___x_2203_, v___x_2202_);
    return v___x_2204_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2217_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_2217_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2218_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5_once), _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5);
    v___x_2219_ = l_Lake_DSL_expandOptSimpleBinder___closed__28;
    v___x_2220_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0_once), _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0);
    v___x_2221_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2221_, 0, v___x_2220_);
    crate::leanh::lean_ctor_set(v___x_2221_, 1, v___x_2219_);
    crate::leanh::lean_ctor_set(v___x_2221_, 2, v___x_2218_);
    return v___x_2221_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2229_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__9;
    v___x_2230_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0_once), _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0);
    v___x_2231_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2231_, 0, v___x_2230_);
    crate::leanh::lean_ctor_set(v___x_2231_, 1, v___x_2229_);
    return v___x_2231_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(
    mut v_init_2232_: *mut crate::leanh::LeanObject,
    mut v_x_2233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: u8 = 0;
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2233_) == 0 {
                    v_k_2235_ = crate::leanh::lean_ctor_get(v_x_2233_, 1);
                    crate::leanh::lean_inc(v_k_2235_);
                    v_v_2236_ = crate::leanh::lean_ctor_get(v_x_2233_, 2);
                    crate::leanh::lean_inc(v_v_2236_);
                    v_l_2237_ = crate::leanh::lean_ctor_get(v_x_2233_, 3);
                    crate::leanh::lean_inc(v_l_2237_);
                    v_r_2238_ = crate::leanh::lean_ctor_get(v_x_2233_, 4);
                    crate::leanh::lean_inc(v_r_2238_);
                    crate::leanh::lean_dec_ref_known(v_x_2233_, 5);
                    v___x_2239_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(v_init_2232_, v_l_2237_);
                    v_a_2240_ = crate::leanh::lean_ctor_get(v___x_2239_, 0);
                    crate::leanh::lean_inc(v_a_2240_);
                    crate::leanh::lean_dec_ref(v___x_2239_);
                    v_ref_2241_ = crate::leanh::lean_ctor_get(v_v_2236_, 0);
                    crate::leanh::lean_inc(v_ref_2241_);
                    v_val_2242_ = crate::leanh::lean_ctor_get(v_v_2236_, 1);
                    crate::leanh::lean_inc(v_val_2242_);
                    crate::leanh::lean_dec(v_v_2236_);
                    v___x_2243_ = 1;
                    v___x_2244_ = l_Lean_mkIdentFrom(v_ref_2241_, v_k_2235_, v___x_2243_);
                    crate::leanh::lean_dec(v_ref_2241_);
                    v___x_2245_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0_once), _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0);
                    v___x_2246_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2;
                    v___x_2247_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4;
                    v___x_2248_ = l_Lake_DSL_expandOptSimpleBinder___closed__28;
                    v___x_2249_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__6), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__6_once), _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__6);
                    v___x_2250_ =
                        l_Lean_Syntax_node2(v___x_2245_, v___x_2247_, v___x_2244_, v___x_2249_);
                    v___x_2251_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8;
                    v___x_2252_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__10), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__10_once), _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__10);
                    v___x_2253_ = l_Lean_Syntax_node3(
                        v___x_2245_,
                        v___x_2251_,
                        v___x_2252_,
                        v___x_2249_,
                        v_val_2242_,
                    );
                    v___x_2254_ = l_Lean_Syntax_node3(
                        v___x_2245_,
                        v___x_2248_,
                        v___x_2249_,
                        v___x_2249_,
                        v___x_2253_,
                    );
                    v___x_2255_ =
                        l_Lean_Syntax_node2(v___x_2245_, v___x_2246_, v___x_2250_, v___x_2254_);
                    v___x_2256_ = lean_array_push(v_a_2240_, v___x_2255_);
                    v_init_2232_ = v___x_2256_;
                    v_x_2233_ = v_r_2238_;
                    state = 0;
                    continue;
                } else {
                    v___x_2258_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2258_, 0, v_init_2232_);
                    return v___x_2258_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___boxed(
    mut v_init_2259_: *mut crate::leanh::LeanObject,
    mut v_x_2260_: *mut crate::leanh::LeanObject,
    mut v___y_2261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2262_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(v_init_2259_, v_x_2260_);
    return v_res_2262_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(
    mut v_opts_2263_: *mut crate::leanh::LeanObject,
    mut v_opt_2264_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2265_ = crate::leanh::lean_ctor_get(v_opt_2264_, 0);
    v_defValue_2266_ = crate::leanh::lean_ctor_get(v_opt_2264_, 1);
    v_map_2267_ = crate::leanh::lean_ctor_get(v_opts_2263_, 0);
    v___x_2268_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2267_,
            v_name_2265_,
        );
    if crate::leanh::lean_obj_tag(v___x_2268_) == 0 {
        let mut v___x_2269_: u8 = 0;
        v___x_2269_ = (crate::leanh::lean_unbox(v_defValue_2266_) as u8);
        return v___x_2269_;
    } else {
        let mut v_val_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2270_ = crate::leanh::lean_ctor_get(v___x_2268_, 0);
        crate::leanh::lean_inc(v_val_2270_);
        crate::leanh::lean_dec_ref_known(v___x_2268_, 1);
        if crate::leanh::lean_obj_tag(v_val_2270_) == 1 {
            let mut v_v_2271_: u8 = 0;
            v_v_2271_ = crate::leanh::lean_ctor_get_uint8(v_val_2270_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_2270_, 0);
            return v_v_2271_;
        } else {
            let mut v___x_2272_: u8 = 0;
            crate::leanh::lean_dec(v_val_2270_);
            v___x_2272_ = (crate::leanh::lean_unbox(v_defValue_2266_) as u8);
            return v___x_2272_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8___boxed(
    mut v_opts_2273_: *mut crate::leanh::LeanObject,
    mut v_opt_2274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2275_: u8 = 0;
    let mut v_r_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2275_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(v_opts_2273_, v_opt_2274_);
    crate::leanh::lean_dec_ref(v_opt_2274_);
    crate::leanh::lean_dec_ref(v_opts_2273_);
    v_r_2276_ = crate::leanh::lean_box((v_res_2275_) as usize);
    return v_r_2276_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0(
    mut v___y_2278_: u8,
    mut v_suppressElabErrors_2279_: u8,
    mut v_x_2280_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_2280_) == 1 {
        let mut v_pre_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_2281_ = crate::leanh::lean_ctor_get(v_x_2280_, 0);
        if crate::leanh::lean_obj_tag(v_pre_2281_) == 0 {
            let mut v_str_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2284_: u8 = 0;
            v_str_2282_ = crate::leanh::lean_ctor_get(v_x_2280_, 1);
            v___x_2283_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___closed__0;
            v___x_2284_ = lean_string_dec_eq(v_str_2282_, v___x_2283_);
            if v___x_2284_ == 0 {
                return v___y_2278_;
            } else {
                return v_suppressElabErrors_2279_;
            }
        } else {
            return v___y_2278_;
        }
    } else {
        return v___y_2278_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___boxed(
    mut v___y_2285_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_2286_: *mut crate::leanh::LeanObject,
    mut v_x_2287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_9370__boxed_2288_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2289_: u8 = 0;
    let mut v_res_2290_: u8 = 0;
    let mut v_r_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_9370__boxed_2288_ = (crate::leanh::lean_unbox(v___y_2285_) as u8);
    v_suppressElabErrors_boxed_2289_ = (crate::leanh::lean_unbox(v_suppressElabErrors_2286_) as u8);
    v_res_2290_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0(v___y_9370__boxed_2288_, v_suppressElabErrors_boxed_2289_, v_x_2287_);
    crate::leanh::lean_dec(v_x_2287_);
    v_r_2291_ = crate::leanh::lean_box((v_res_2290_) as usize);
    return v_r_2291_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2292_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2292_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2293_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_2294_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2294_, 0, v___x_2293_);
    return v___x_2294_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2295_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_2296_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2297_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2297_, 0, v___x_2296_);
    crate::leanh::lean_ctor_set(v___x_2297_, 1, v___x_2296_);
    crate::leanh::lean_ctor_set(v___x_2297_, 2, v___x_2296_);
    crate::leanh::lean_ctor_set(v___x_2297_, 3, v___x_2296_);
    crate::leanh::lean_ctor_set(v___x_2297_, 4, v___x_2295_);
    crate::leanh::lean_ctor_set(v___x_2297_, 5, v___x_2295_);
    crate::leanh::lean_ctor_set(v___x_2297_, 6, v___x_2295_);
    crate::leanh::lean_ctor_set(v___x_2297_, 7, v___x_2295_);
    crate::leanh::lean_ctor_set(v___x_2297_, 8, v___x_2295_);
    crate::leanh::lean_ctor_set(v___x_2297_, 9, v___x_2295_);
    return v___x_2297_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2298_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2299_ = lean_mk_empty_array_with_capacity(v___x_2298_);
    v___x_2300_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2300_, 0, v___x_2299_);
    return v___x_2300_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2301_: usize = 0;
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2301_ = 5usize;
    v___x_2302_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2303_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2304_ = lean_mk_empty_array_with_capacity(v___x_2303_);
    v___x_2305_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_2306_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_2306_, 0, v___x_2305_);
    crate::leanh::lean_ctor_set(v___x_2306_, 1, v___x_2304_);
    crate::leanh::lean_ctor_set(v___x_2306_, 2, v___x_2302_);
    crate::leanh::lean_ctor_set(v___x_2306_, 3, v___x_2302_);
    crate::leanh::lean_ctor_set_usize(v___x_2306_, 4, v___x_2301_);
    return v___x_2306_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2307_ = crate::leanh::lean_box(1);
    v___x_2308_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4);
    v___x_2309_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_2310_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2310_, 0, v___x_2309_);
    crate::leanh::lean_ctor_set(v___x_2310_, 1, v___x_2308_);
    crate::leanh::lean_ctor_set(v___x_2310_, 2, v___x_2307_);
    return v___x_2310_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(
    mut v_msgData_2311_: *mut crate::leanh::LeanObject,
    mut v___y_2312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2314_ = lean_st_ref_get(v___y_2312_);
    v_env_2315_ = crate::leanh::lean_ctor_get(v___x_2314_, 0);
    crate::leanh::lean_inc_ref(v_env_2315_);
    crate::leanh::lean_dec(v___x_2314_);
    v___x_2316_ = lean_st_ref_get(v___y_2312_);
    v_scopes_2317_ = crate::leanh::lean_ctor_get(v___x_2316_, 2);
    crate::leanh::lean_inc(v_scopes_2317_);
    crate::leanh::lean_dec(v___x_2316_);
    v___x_2318_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2319_ = l_List_head_x21___redArg(v___x_2318_, v_scopes_2317_);
    crate::leanh::lean_dec(v_scopes_2317_);
    v_opts_2320_ = crate::leanh::lean_ctor_get(v___x_2319_, 1);
    crate::leanh::lean_inc_ref(v_opts_2320_);
    crate::leanh::lean_dec(v___x_2319_);
    v___x_2321_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2);
    v___x_2322_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5);
    v___x_2323_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2323_, 0, v_env_2315_);
    crate::leanh::lean_ctor_set(v___x_2323_, 1, v___x_2321_);
    crate::leanh::lean_ctor_set(v___x_2323_, 2, v___x_2322_);
    crate::leanh::lean_ctor_set(v___x_2323_, 3, v_opts_2320_);
    v___x_2324_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2324_, 0, v___x_2323_);
    crate::leanh::lean_ctor_set(v___x_2324_, 1, v_msgData_2311_);
    v___x_2325_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2325_, 0, v___x_2324_);
    return v___x_2325_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_msgData_2326_: *mut crate::leanh::LeanObject,
    mut v___y_2327_: *mut crate::leanh::LeanObject,
    mut v___y_2328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2329_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v_msgData_2326_, v___y_2327_);
    crate::leanh::lean_dec(v___y_2327_);
    return v_res_2329_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(
    mut v_ref_2330_: *mut crate::leanh::LeanObject,
    mut v_msgData_2331_: *mut crate::leanh::LeanObject,
    mut v_severity_2332_: u8,
    mut v_isSilent_2333_: u8,
    mut v___y_2334_: *mut crate::leanh::LeanObject,
    mut v___y_2335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2339_: u8 = 0;
    let mut v___y_2340_: u8 = 0;
    let mut v___y_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2352_: u8 = 0;
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2369_: u8 = 0;
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2382_: u8 = 0;
    let mut v_isSharedCheck_2383_: u8 = 0;
    let mut v_a_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2387_: u8 = 0;
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2391_: u8 = 0;
    let mut v_a_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2395_: u8 = 0;
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2399_: u8 = 0;
    let mut v___y_2401_: u8 = 0;
    let mut v___y_2402_: u8 = 0;
    let mut v___y_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2404_: u8 = 0;
    let mut v___y_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2408_: u8 = 0;
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2414_: u8 = 0;
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: u8 = 0;
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut v___y_2429_: u8 = 0;
    let mut v___y_2430_: u8 = 0;
    let mut v___y_2431_: u8 = 0;
    let mut v___y_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2437_: u8 = 0;
    let mut v___y_2438_: u8 = 0;
    let mut v___y_2439_: u8 = 0;
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2449_: u8 = 0;
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2453_: u8 = 0;
    let mut v___x_2454_: u8 = 0;
    let mut v___y_2456_: u8 = 0;
    let mut v___y_2457_: u8 = 0;
    let mut v___y_2458_: u8 = 0;
    let mut v___y_2460_: u8 = 0;
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: u8 = 0;
    let mut v___x_2467_: u8 = 0;
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: u8 = 0;
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: u8 = 0;
    let mut v___x_2473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2454_ = 2;
                v___x_2472_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2332_, v___x_2454_);
                if v___x_2472_ == 0 {
                    v___y_2460_ = v___x_2472_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_2331_);
                    v___x_2473_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2331_);
                    v___y_2460_ = v___x_2473_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_2346_ = l_Lean_Elab_Command_getScope___redArg(v___y_2345_);
                if crate::leanh::lean_obj_tag(v___x_2346_) == 0 {
                    v_a_2347_ = crate::leanh::lean_ctor_get(v___x_2346_, 0);
                    crate::leanh::lean_inc(v_a_2347_);
                    crate::leanh::lean_dec_ref_known(v___x_2346_, 1);
                    v___x_2348_ = l_Lean_Elab_Command_getScope___redArg(v___y_2345_);
                    if crate::leanh::lean_obj_tag(v___x_2348_) == 0 {
                        v_a_2349_ = crate::leanh::lean_ctor_get(v___x_2348_, 0);
                        v_isSharedCheck_2383_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2348_)) as u8;
                        if v_isSharedCheck_2383_ == 0 {
                            v___x_2351_ = v___x_2348_;
                            v_isShared_2352_ = v_isSharedCheck_2383_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2349_);
                            crate::leanh::lean_dec(v___x_2348_);
                            v___x_2351_ = crate::leanh::lean_box(0);
                            v_isShared_2352_ = v_isSharedCheck_2383_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2347_);
                        crate::leanh::lean_dec(v___y_2344_);
                        crate::leanh::lean_dec_ref(v___y_2342_);
                        crate::leanh::lean_dec_ref(v___y_2338_);
                        v_a_2384_ = crate::leanh::lean_ctor_get(v___x_2348_, 0);
                        v_isSharedCheck_2391_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2348_)) as u8;
                        if v_isSharedCheck_2391_ == 0 {
                            v___x_2386_ = v___x_2348_;
                            v_isShared_2387_ = v_isSharedCheck_2391_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2384_);
                            crate::leanh::lean_dec(v___x_2348_);
                            v___x_2386_ = crate::leanh::lean_box(0);
                            v_isShared_2387_ = v_isSharedCheck_2391_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2344_);
                    crate::leanh::lean_dec_ref(v___y_2342_);
                    crate::leanh::lean_dec_ref(v___y_2338_);
                    v_a_2392_ = crate::leanh::lean_ctor_get(v___x_2346_, 0);
                    v_isSharedCheck_2399_ = (!crate::leanh::lean_is_exclusive(v___x_2346_)) as u8;
                    if v_isSharedCheck_2399_ == 0 {
                        v___x_2394_ = v___x_2346_;
                        v_isShared_2395_ = v_isSharedCheck_2399_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2392_);
                        crate::leanh::lean_dec(v___x_2346_);
                        v___x_2394_ = crate::leanh::lean_box(0);
                        v_isShared_2395_ = v_isSharedCheck_2399_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2353_ = lean_st_ref_take(v___y_2345_);
                v_currNamespace_2354_ = crate::leanh::lean_ctor_get(v_a_2347_, 2);
                crate::leanh::lean_inc(v_currNamespace_2354_);
                crate::leanh::lean_dec(v_a_2347_);
                v_openDecls_2355_ = crate::leanh::lean_ctor_get(v_a_2349_, 3);
                crate::leanh::lean_inc(v_openDecls_2355_);
                crate::leanh::lean_dec(v_a_2349_);
                v_env_2356_ = crate::leanh::lean_ctor_get(v___x_2353_, 0);
                v_messages_2357_ = crate::leanh::lean_ctor_get(v___x_2353_, 1);
                v_scopes_2358_ = crate::leanh::lean_ctor_get(v___x_2353_, 2);
                v_usedQuotCtxts_2359_ = crate::leanh::lean_ctor_get(v___x_2353_, 3);
                v_nextMacroScope_2360_ = crate::leanh::lean_ctor_get(v___x_2353_, 4);
                v_maxRecDepth_2361_ = crate::leanh::lean_ctor_get(v___x_2353_, 5);
                v_ngen_2362_ = crate::leanh::lean_ctor_get(v___x_2353_, 6);
                v_auxDeclNGen_2363_ = crate::leanh::lean_ctor_get(v___x_2353_, 7);
                v_infoState_2364_ = crate::leanh::lean_ctor_get(v___x_2353_, 8);
                v_traceState_2365_ = crate::leanh::lean_ctor_get(v___x_2353_, 9);
                v_snapshotTasks_2366_ = crate::leanh::lean_ctor_get(v___x_2353_, 10);
                v_isSharedCheck_2382_ = (!crate::leanh::lean_is_exclusive(v___x_2353_)) as u8;
                if v_isSharedCheck_2382_ == 0 {
                    v___x_2368_ = v___x_2353_;
                    v_isShared_2369_ = v_isSharedCheck_2382_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2366_);
                    crate::leanh::lean_inc(v_traceState_2365_);
                    crate::leanh::lean_inc(v_infoState_2364_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2363_);
                    crate::leanh::lean_inc(v_ngen_2362_);
                    crate::leanh::lean_inc(v_maxRecDepth_2361_);
                    crate::leanh::lean_inc(v_nextMacroScope_2360_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_2359_);
                    crate::leanh::lean_inc(v_scopes_2358_);
                    crate::leanh::lean_inc(v_messages_2357_);
                    crate::leanh::lean_inc(v_env_2356_);
                    crate::leanh::lean_dec(v___x_2353_);
                    v___x_2368_ = crate::leanh::lean_box(0);
                    v_isShared_2369_ = v_isSharedCheck_2382_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2370_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2370_, 0, v_currNamespace_2354_);
                crate::leanh::lean_ctor_set(v___x_2370_, 1, v_openDecls_2355_);
                v___x_2371_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2371_, 0, v___x_2370_);
                crate::leanh::lean_ctor_set(v___x_2371_, 1, v___y_2342_);
                crate::leanh::lean_inc_ref(v___y_2343_);
                crate::leanh::lean_inc_ref(v___y_2341_);
                v___x_2372_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_2372_, 0, v___y_2341_);
                crate::leanh::lean_ctor_set(v___x_2372_, 1, v___y_2338_);
                crate::leanh::lean_ctor_set(v___x_2372_, 2, v___y_2344_);
                crate::leanh::lean_ctor_set(v___x_2372_, 3, v___y_2343_);
                crate::leanh::lean_ctor_set(v___x_2372_, 4, v___x_2371_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2372_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_2339_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2372_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_2340_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2372_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2333_,
                );
                v___x_2373_ = l_Lean_MessageLog_add(v___x_2372_, v_messages_2357_);
                if v_isShared_2369_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2368_, 1, v___x_2373_);
                    v___x_2375_ = v___x_2368_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2381_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_env_2356_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2381_, 1, v___x_2373_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2381_, 2, v_scopes_2358_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2381_, 3, v_usedQuotCtxts_2359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2381_, 4, v_nextMacroScope_2360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2381_, 5, v_maxRecDepth_2361_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2381_, 6, v_ngen_2362_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2381_, 7, v_auxDeclNGen_2363_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2381_, 8, v_infoState_2364_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2381_, 9, v_traceState_2365_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2381_, 10, v_snapshotTasks_2366_);
                    v___x_2375_ = v_reuseFailAlloc_2381_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2376_ = lean_st_ref_set(v___y_2345_, v___x_2375_);
                v___x_2377_ = crate::leanh::lean_box(0);
                if v_isShared_2352_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2351_, 0, v___x_2377_);
                    v___x_2379_ = v___x_2351_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2380_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
                    v___x_2379_ = v_reuseFailAlloc_2380_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2379_;
            }
            6 => {
                if v_isShared_2387_ == 0 {
                    v___x_2389_ = v___x_2386_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2390_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
                    v___x_2389_ = v_reuseFailAlloc_2390_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2389_;
            }
            8 => {
                if v_isShared_2395_ == 0 {
                    v___x_2397_ = v___x_2394_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2398_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
                    v___x_2397_ = v_reuseFailAlloc_2398_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2397_;
            }
            10 => {
                v_fileName_2406_ = crate::leanh::lean_ctor_get(v___y_2334_, 0);
                v_fileMap_2407_ = crate::leanh::lean_ctor_get(v___y_2334_, 1);
                v_suppressElabErrors_2408_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2334_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v___x_2409_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2331_,
                    );
                v___x_2410_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v___x_2409_, v___y_2335_);
                v_a_2411_ = crate::leanh::lean_ctor_get(v___x_2410_, 0);
                v_isSharedCheck_2427_ = (!crate::leanh::lean_is_exclusive(v___x_2410_)) as u8;
                if v_isSharedCheck_2427_ == 0 {
                    v___x_2413_ = v___x_2410_;
                    v_isShared_2414_ = v_isSharedCheck_2427_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2411_);
                    crate::leanh::lean_dec(v___x_2410_);
                    v___x_2413_ = crate::leanh::lean_box(0);
                    v_isShared_2414_ = v_isSharedCheck_2427_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_inc_ref_n(v_fileMap_2407_, 2);
                v___x_2415_ = l_Lean_FileMap_toPosition(v_fileMap_2407_, v___y_2403_);
                crate::leanh::lean_dec(v___y_2403_);
                v___x_2416_ = l_Lean_FileMap_toPosition(v_fileMap_2407_, v___y_2405_);
                crate::leanh::lean_dec(v___y_2405_);
                v___x_2417_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2417_, 0, v___x_2416_);
                v___x_2418_ = l_Lake_DSL_expandOptSimpleBinder___closed__9;
                if v_suppressElabErrors_2408_ == 0 {
                    crate::leanh::lean_del_object(v___x_2413_);
                    v___y_2338_ = v___x_2415_;
                    v___y_2339_ = v___y_2402_;
                    v___y_2340_ = v___y_2404_;
                    v___y_2341_ = v_fileName_2406_;
                    v___y_2342_ = v_a_2411_;
                    v___y_2343_ = v___x_2418_;
                    v___y_2344_ = v___x_2417_;
                    v___y_2345_ = v___y_2335_;
                    state = 1;
                    continue;
                } else {
                    v___x_2419_ = crate::leanh::lean_box((v___y_2401_) as usize);
                    v___x_2420_ = crate::leanh::lean_box((v_suppressElabErrors_2408_) as usize);
                    v___f_2421_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_2421_, 0, v___x_2419_);
                    crate::leanh::lean_closure_set(v___f_2421_, 1, v___x_2420_);
                    crate::leanh::lean_inc(v_a_2411_);
                    v___x_2422_ = l_Lean_MessageData_hasTag(v___f_2421_, v_a_2411_);
                    if v___x_2422_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2417_, 1);
                        crate::leanh::lean_dec_ref(v___x_2415_);
                        crate::leanh::lean_dec(v_a_2411_);
                        v___x_2423_ = crate::leanh::lean_box(0);
                        if v_isShared_2414_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2413_, 0, v___x_2423_);
                            v___x_2425_ = v___x_2413_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_2426_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
                            v___x_2425_ = v_reuseFailAlloc_2426_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2413_);
                        v___y_2338_ = v___x_2415_;
                        v___y_2339_ = v___y_2402_;
                        v___y_2340_ = v___y_2404_;
                        v___y_2341_ = v_fileName_2406_;
                        v___y_2342_ = v_a_2411_;
                        v___y_2343_ = v___x_2418_;
                        v___y_2344_ = v___x_2417_;
                        v___y_2345_ = v___y_2335_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_2425_;
            }
            13 => {
                v___x_2434_ = l_Lean_Syntax_getTailPos_x3f(v___y_2432_, v___y_2430_);
                crate::leanh::lean_dec(v___y_2432_);
                if crate::leanh::lean_obj_tag(v___x_2434_) == 0 {
                    crate::leanh::lean_inc(v___y_2433_);
                    v___y_2401_ = v___y_2429_;
                    v___y_2402_ = v___y_2430_;
                    v___y_2403_ = v___y_2433_;
                    v___y_2404_ = v___y_2431_;
                    v___y_2405_ = v___y_2433_;
                    state = 10;
                    continue;
                } else {
                    v_val_2435_ = crate::leanh::lean_ctor_get(v___x_2434_, 0);
                    crate::leanh::lean_inc(v_val_2435_);
                    crate::leanh::lean_dec_ref_known(v___x_2434_, 1);
                    v___y_2401_ = v___y_2429_;
                    v___y_2402_ = v___y_2430_;
                    v___y_2403_ = v___y_2433_;
                    v___y_2404_ = v___y_2431_;
                    v___y_2405_ = v_val_2435_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_2440_ = l_Lean_Elab_Command_getRef___redArg(v___y_2334_);
                if crate::leanh::lean_obj_tag(v___x_2440_) == 0 {
                    v_a_2441_ = crate::leanh::lean_ctor_get(v___x_2440_, 0);
                    crate::leanh::lean_inc(v_a_2441_);
                    crate::leanh::lean_dec_ref_known(v___x_2440_, 1);
                    v_ref_2442_ = l_Lean_replaceRef(v_ref_2330_, v_a_2441_);
                    crate::leanh::lean_dec(v_a_2441_);
                    v___x_2443_ = l_Lean_Syntax_getPos_x3f(v_ref_2442_, v___y_2438_);
                    if crate::leanh::lean_obj_tag(v___x_2443_) == 0 {
                        v___x_2444_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_2429_ = v___y_2437_;
                        v___y_2430_ = v___y_2438_;
                        v___y_2431_ = v___y_2439_;
                        v___y_2432_ = v_ref_2442_;
                        v___y_2433_ = v___x_2444_;
                        state = 13;
                        continue;
                    } else {
                        v_val_2445_ = crate::leanh::lean_ctor_get(v___x_2443_, 0);
                        crate::leanh::lean_inc(v_val_2445_);
                        crate::leanh::lean_dec_ref_known(v___x_2443_, 1);
                        v___y_2429_ = v___y_2437_;
                        v___y_2430_ = v___y_2438_;
                        v___y_2431_ = v___y_2439_;
                        v___y_2432_ = v_ref_2442_;
                        v___y_2433_ = v_val_2445_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_2331_);
                    v_a_2446_ = crate::leanh::lean_ctor_get(v___x_2440_, 0);
                    v_isSharedCheck_2453_ = (!crate::leanh::lean_is_exclusive(v___x_2440_)) as u8;
                    if v_isSharedCheck_2453_ == 0 {
                        v___x_2448_ = v___x_2440_;
                        v_isShared_2449_ = v_isSharedCheck_2453_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2446_);
                        crate::leanh::lean_dec(v___x_2440_);
                        v___x_2448_ = crate::leanh::lean_box(0);
                        v_isShared_2449_ = v_isSharedCheck_2453_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_2449_ == 0 {
                    v___x_2451_ = v___x_2448_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2452_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
                    v___x_2451_ = v_reuseFailAlloc_2452_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2451_;
            }
            17 => {
                if v___y_2458_ == 0 {
                    v___y_2437_ = v___y_2456_;
                    v___y_2438_ = v___y_2457_;
                    v___y_2439_ = v_severity_2332_;
                    state = 14;
                    continue;
                } else {
                    v___y_2437_ = v___y_2456_;
                    v___y_2438_ = v___y_2457_;
                    v___y_2439_ = v___x_2454_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_2460_ == 0 {
                    v___x_2461_ = lean_st_ref_get(v___y_2335_);
                    v_scopes_2462_ = crate::leanh::lean_ctor_get(v___x_2461_, 2);
                    crate::leanh::lean_inc(v_scopes_2462_);
                    crate::leanh::lean_dec(v___x_2461_);
                    v___x_2463_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_2464_ = l_List_head_x21___redArg(v___x_2463_, v_scopes_2462_);
                    crate::leanh::lean_dec(v_scopes_2462_);
                    v_opts_2465_ = crate::leanh::lean_ctor_get(v___x_2464_, 1);
                    crate::leanh::lean_inc_ref(v_opts_2465_);
                    crate::leanh::lean_dec(v___x_2464_);
                    v___x_2466_ = 1;
                    v___x_2467_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2332_, v___x_2466_);
                    if v___x_2467_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_2465_);
                        v___y_2456_ = v___y_2460_;
                        v___y_2457_ = v___y_2460_;
                        v___y_2458_ = v___x_2467_;
                        state = 17;
                        continue;
                    } else {
                        v___x_2468_ = l_Lean_warningAsError;
                        v___x_2469_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(v_opts_2465_, v___x_2468_);
                        crate::leanh::lean_dec_ref(v_opts_2465_);
                        v___y_2456_ = v___y_2460_;
                        v___y_2457_ = v___y_2460_;
                        v___y_2458_ = v___x_2469_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_2331_);
                    v___x_2470_ = crate::leanh::lean_box(0);
                    v___x_2471_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2471_, 0, v___x_2470_);
                    return v___x_2471_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___boxed(
    mut v_ref_2474_: *mut crate::leanh::LeanObject,
    mut v_msgData_2475_: *mut crate::leanh::LeanObject,
    mut v_severity_2476_: *mut crate::leanh::LeanObject,
    mut v_isSilent_2477_: *mut crate::leanh::LeanObject,
    mut v___y_2478_: *mut crate::leanh::LeanObject,
    mut v___y_2479_: *mut crate::leanh::LeanObject,
    mut v___y_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_2481_: u8 = 0;
    let mut v_isSilent_boxed_2482_: u8 = 0;
    let mut v_res_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2481_ = (crate::leanh::lean_unbox(v_severity_2476_) as u8);
    v_isSilent_boxed_2482_ = (crate::leanh::lean_unbox(v_isSilent_2477_) as u8);
    v_res_2483_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(v_ref_2474_, v_msgData_2475_, v_severity_boxed_2481_, v_isSilent_boxed_2482_, v___y_2478_, v___y_2479_);
    crate::leanh::lean_dec(v___y_2479_);
    crate::leanh::lean_dec_ref(v___y_2478_);
    crate::leanh::lean_dec(v_ref_2474_);
    return v_res_2483_;
}
pub unsafe fn l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(
    mut v_ref_2484_: *mut crate::leanh::LeanObject,
    mut v_msgData_2485_: *mut crate::leanh::LeanObject,
    mut v___y_2486_: *mut crate::leanh::LeanObject,
    mut v___y_2487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2489_: u8 = 0;
    let mut v___x_2490_: u8 = 0;
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2489_ = 1;
    v___x_2490_ = 0;
    v___x_2491_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(v_ref_2484_, v_msgData_2485_, v___x_2489_, v___x_2490_, v___y_2486_, v___y_2487_);
    return v___x_2491_;
}
pub unsafe fn l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2___boxed(
    mut v_ref_2492_: *mut crate::leanh::LeanObject,
    mut v_msgData_2493_: *mut crate::leanh::LeanObject,
    mut v___y_2494_: *mut crate::leanh::LeanObject,
    mut v___y_2495_: *mut crate::leanh::LeanObject,
    mut v___y_2496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2497_ =
        l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(
            v_ref_2492_,
            v_msgData_2493_,
            v___y_2494_,
            v___y_2495_,
        );
    crate::leanh::lean_dec(v___y_2495_);
    crate::leanh::lean_dec_ref(v___y_2494_);
    crate::leanh::lean_dec(v_ref_2492_);
    return v_res_2497_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(
    mut v_t_2498_: *mut crate::leanh::LeanObject,
    mut v___y_2499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_2503_: u8 = 0;
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2520_: u8 = 0;
    let mut v_enabled_2521_: u8 = 0;
    let mut v_assignment_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2527_: u8 = 0;
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2538_: u8 = 0;
    let mut v_isSharedCheck_2539_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2501_ = lean_st_ref_get(v___y_2499_);
                v_infoState_2502_ = crate::leanh::lean_ctor_get(v___x_2501_, 8);
                crate::leanh::lean_inc_ref(v_infoState_2502_);
                crate::leanh::lean_dec(v___x_2501_);
                v_enabled_2503_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_2502_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_2502_);
                if v_enabled_2503_ == 0 {
                    crate::leanh::lean_dec_ref(v_t_2498_);
                    v___x_2504_ = crate::leanh::lean_box(0);
                    v___x_2505_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2505_, 0, v___x_2504_);
                    return v___x_2505_;
                } else {
                    v___x_2506_ = lean_st_ref_take(v___y_2499_);
                    v_infoState_2507_ = crate::leanh::lean_ctor_get(v___x_2506_, 8);
                    v_env_2508_ = crate::leanh::lean_ctor_get(v___x_2506_, 0);
                    v_messages_2509_ = crate::leanh::lean_ctor_get(v___x_2506_, 1);
                    v_scopes_2510_ = crate::leanh::lean_ctor_get(v___x_2506_, 2);
                    v_usedQuotCtxts_2511_ = crate::leanh::lean_ctor_get(v___x_2506_, 3);
                    v_nextMacroScope_2512_ = crate::leanh::lean_ctor_get(v___x_2506_, 4);
                    v_maxRecDepth_2513_ = crate::leanh::lean_ctor_get(v___x_2506_, 5);
                    v_ngen_2514_ = crate::leanh::lean_ctor_get(v___x_2506_, 6);
                    v_auxDeclNGen_2515_ = crate::leanh::lean_ctor_get(v___x_2506_, 7);
                    v_traceState_2516_ = crate::leanh::lean_ctor_get(v___x_2506_, 9);
                    v_snapshotTasks_2517_ = crate::leanh::lean_ctor_get(v___x_2506_, 10);
                    v_isSharedCheck_2539_ = (!crate::leanh::lean_is_exclusive(v___x_2506_)) as u8;
                    if v_isSharedCheck_2539_ == 0 {
                        v___x_2519_ = v___x_2506_;
                        v_isShared_2520_ = v_isSharedCheck_2539_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_2517_);
                        crate::leanh::lean_inc(v_traceState_2516_);
                        crate::leanh::lean_inc(v_infoState_2507_);
                        crate::leanh::lean_inc(v_auxDeclNGen_2515_);
                        crate::leanh::lean_inc(v_ngen_2514_);
                        crate::leanh::lean_inc(v_maxRecDepth_2513_);
                        crate::leanh::lean_inc(v_nextMacroScope_2512_);
                        crate::leanh::lean_inc(v_usedQuotCtxts_2511_);
                        crate::leanh::lean_inc(v_scopes_2510_);
                        crate::leanh::lean_inc(v_messages_2509_);
                        crate::leanh::lean_inc(v_env_2508_);
                        crate::leanh::lean_dec(v___x_2506_);
                        v___x_2519_ = crate::leanh::lean_box(0);
                        v_isShared_2520_ = v_isSharedCheck_2539_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_enabled_2521_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_2507_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_2522_ = crate::leanh::lean_ctor_get(v_infoState_2507_, 0);
                v_lazyAssignment_2523_ = crate::leanh::lean_ctor_get(v_infoState_2507_, 1);
                v_trees_2524_ = crate::leanh::lean_ctor_get(v_infoState_2507_, 2);
                v_isSharedCheck_2538_ = (!crate::leanh::lean_is_exclusive(v_infoState_2507_)) as u8;
                if v_isSharedCheck_2538_ == 0 {
                    v___x_2526_ = v_infoState_2507_;
                    v_isShared_2527_ = v_isSharedCheck_2538_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_trees_2524_);
                    crate::leanh::lean_inc(v_lazyAssignment_2523_);
                    crate::leanh::lean_inc(v_assignment_2522_);
                    crate::leanh::lean_dec(v_infoState_2507_);
                    v___x_2526_ = crate::leanh::lean_box(0);
                    v_isShared_2527_ = v_isSharedCheck_2538_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2528_ = l_Lean_PersistentArray_push___redArg(v_trees_2524_, v_t_2498_);
                if v_isShared_2527_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2526_, 2, v___x_2528_);
                    v___x_2530_ = v___x_2526_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2537_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_assignment_2522_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_lazyAssignment_2523_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 2, v___x_2528_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2537_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_2521_,
                    );
                    v___x_2530_ = v_reuseFailAlloc_2537_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2520_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2519_, 8, v___x_2530_);
                    v___x_2532_ = v___x_2519_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2536_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_env_2508_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_messages_2509_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 2, v_scopes_2510_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 3, v_usedQuotCtxts_2511_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 4, v_nextMacroScope_2512_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 5, v_maxRecDepth_2513_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 6, v_ngen_2514_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 7, v_auxDeclNGen_2515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 8, v___x_2530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 9, v_traceState_2516_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 10, v_snapshotTasks_2517_);
                    v___x_2532_ = v_reuseFailAlloc_2536_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2533_ = lean_st_ref_set(v___y_2499_, v___x_2532_);
                v___x_2534_ = crate::leanh::lean_box(0);
                v___x_2535_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2535_, 0, v___x_2534_);
                return v___x_2535_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_t_2540_: *mut crate::leanh::LeanObject,
    mut v___y_2541_: *mut crate::leanh::LeanObject,
    mut v___y_2542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2543_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(v_t_2540_, v___y_2541_);
    crate::leanh::lean_dec(v___y_2541_);
    return v_res_2543_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2544_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2545_ = lean_mk_empty_array_with_capacity(v___x_2544_);
    v___x_2546_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2546_, 0, v___x_2545_);
    return v___x_2546_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2547_: usize = 0;
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2547_ = 5usize;
    v___x_2548_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2549_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2550_ = lean_mk_empty_array_with_capacity(v___x_2549_);
    v___x_2551_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0);
    v___x_2552_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_2552_, 0, v___x_2551_);
    crate::leanh::lean_ctor_set(v___x_2552_, 1, v___x_2550_);
    crate::leanh::lean_ctor_set(v___x_2552_, 2, v___x_2548_);
    crate::leanh::lean_ctor_set(v___x_2552_, 3, v___x_2548_);
    crate::leanh::lean_ctor_set_usize(v___x_2552_, 4, v___x_2547_);
    return v___x_2552_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(
    mut v_t_2553_: *mut crate::leanh::LeanObject,
    mut v___y_2554_: *mut crate::leanh::LeanObject,
    mut v___y_2555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_2559_: u8 = 0;
    v___x_2557_ = lean_st_ref_get(v___y_2555_);
    v_infoState_2558_ = crate::leanh::lean_ctor_get(v___x_2557_, 8);
    crate::leanh::lean_inc_ref(v_infoState_2558_);
    crate::leanh::lean_dec(v___x_2557_);
    v_enabled_2559_ = crate::leanh::lean_ctor_get_uint8(
        v_infoState_2558_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    crate::leanh::lean_dec_ref(v_infoState_2558_);
    if v_enabled_2559_ == 0 {
        let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_t_2553_);
        v___x_2560_ = crate::leanh::lean_box(0);
        v___x_2561_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2561_, 0, v___x_2560_);
        return v___x_2561_;
    } else {
        let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2562_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1);
        v___x_2563_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2563_, 0, v_t_2553_);
        crate::leanh::lean_ctor_set(v___x_2563_, 1, v___x_2562_);
        v___x_2564_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(v___x_2563_, v___y_2555_);
        return v___x_2564_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___boxed(
    mut v_t_2565_: *mut crate::leanh::LeanObject,
    mut v___y_2566_: *mut crate::leanh::LeanObject,
    mut v___y_2567_: *mut crate::leanh::LeanObject,
    mut v___y_2568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2569_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(v_t_2565_, v___y_2566_, v___y_2567_);
    crate::leanh::lean_dec(v___y_2567_);
    crate::leanh::lean_dec_ref(v___y_2566_);
    return v_res_2569_;
}
pub unsafe fn l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(
    mut v_info_2570_: *mut crate::leanh::LeanObject,
    mut v___y_2571_: *mut crate::leanh::LeanObject,
    mut v___y_2572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2574_ = crate::leanh::lean_alloc_ctor(8, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2574_, 0, v_info_2570_);
    v___x_2575_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(v___x_2574_, v___y_2571_, v___y_2572_);
    return v___x_2575_;
}
pub unsafe fn l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1___boxed(
    mut v_info_2576_: *mut crate::leanh::LeanObject,
    mut v___y_2577_: *mut crate::leanh::LeanObject,
    mut v___y_2578_: *mut crate::leanh::LeanObject,
    mut v___y_2579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2580_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(v_info_2576_, v___y_2577_, v___y_2578_);
    crate::leanh::lean_dec(v___y_2578_);
    crate::leanh::lean_dec_ref(v___y_2577_);
    return v_res_2580_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2581_ = crate::leanh::lean_box(1);
    v___x_2582_ = l_Lean_MessageData_ofFormat(v___x_2581_);
    return v___x_2582_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2586_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__2;
    v___x_2587_ = l_Lean_MessageData_ofFormat(v___x_2586_);
    return v___x_2587_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7(
    mut v_x_2588_: *mut crate::leanh::LeanObject,
    mut v_x_2589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2594_: u8 = 0;
    let mut v_before_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2598_: u8 = 0;
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2611_: u8 = 0;
    let mut v_unused_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2613_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2589_) == 0 {
                    return v_x_2588_;
                } else {
                    v_head_2590_ = crate::leanh::lean_ctor_get(v_x_2589_, 0);
                    v_tail_2591_ = crate::leanh::lean_ctor_get(v_x_2589_, 1);
                    v_isSharedCheck_2613_ = (!crate::leanh::lean_is_exclusive(v_x_2589_)) as u8;
                    if v_isSharedCheck_2613_ == 0 {
                        v___x_2593_ = v_x_2589_;
                        v_isShared_2594_ = v_isSharedCheck_2613_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2591_);
                        crate::leanh::lean_inc(v_head_2590_);
                        crate::leanh::lean_dec(v_x_2589_);
                        v___x_2593_ = crate::leanh::lean_box(0);
                        v_isShared_2594_ = v_isSharedCheck_2613_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_2595_ = crate::leanh::lean_ctor_get(v_head_2590_, 0);
                v_isSharedCheck_2611_ = (!crate::leanh::lean_is_exclusive(v_head_2590_)) as u8;
                if v_isSharedCheck_2611_ == 0 {
                    v_unused_2612_ = crate::leanh::lean_ctor_get(v_head_2590_, 1);
                    crate::leanh::lean_dec(v_unused_2612_);
                    v___x_2597_ = v_head_2590_;
                    v_isShared_2598_ = v_isSharedCheck_2611_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_2595_);
                    crate::leanh::lean_dec(v_head_2590_);
                    v___x_2597_ = crate::leanh::lean_box(0);
                    v_isShared_2598_ = v_isSharedCheck_2611_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2599_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0);
                if v_isShared_2598_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2597_, 7);
                    crate::leanh::lean_ctor_set(v___x_2597_, 1, v___x_2599_);
                    crate::leanh::lean_ctor_set(v___x_2597_, 0, v_x_2588_);
                    v___x_2601_ = v___x_2597_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2610_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_x_2588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 1, v___x_2599_);
                    v___x_2601_ = v_reuseFailAlloc_2610_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2602_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3);
                if v_isShared_2594_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2593_, 7);
                    crate::leanh::lean_ctor_set(v___x_2593_, 1, v___x_2602_);
                    crate::leanh::lean_ctor_set(v___x_2593_, 0, v___x_2601_);
                    v___x_2604_ = v___x_2593_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2609_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2601_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 1, v___x_2602_);
                    v___x_2604_ = v_reuseFailAlloc_2609_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2605_ = l_Lean_MessageData_ofSyntax(v_before_2595_);
                v___x_2606_ = l_Lean_indentD(v___x_2605_);
                v___x_2607_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2607_, 0, v___x_2604_);
                crate::leanh::lean_ctor_set(v___x_2607_, 1, v___x_2606_);
                v_x_2588_ = v___x_2607_;
                v_x_2589_ = v_tail_2591_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2617_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__1;
    v___x_2618_ = l_Lean_MessageData_ofFormat(v___x_2617_);
    return v___x_2618_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(
    mut v_msgData_2619_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2620_: *mut crate::leanh::LeanObject,
    mut v___y_2621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: u8 = 0;
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2636_: u8 = 0;
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2648_: u8 = 0;
    let mut v_unused_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2623_ = lean_st_ref_get(v___y_2621_);
                v_scopes_2624_ = crate::leanh::lean_ctor_get(v___x_2623_, 2);
                crate::leanh::lean_inc(v_scopes_2624_);
                crate::leanh::lean_dec(v___x_2623_);
                v___x_2625_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_2626_ = l_List_head_x21___redArg(v___x_2625_, v_scopes_2624_);
                crate::leanh::lean_dec(v_scopes_2624_);
                v_opts_2627_ = crate::leanh::lean_ctor_get(v___x_2626_, 1);
                crate::leanh::lean_inc_ref(v_opts_2627_);
                crate::leanh::lean_dec(v___x_2626_);
                v___x_2628_ = l_Lean_Elab_pp_macroStack;
                v___x_2629_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(v_opts_2627_, v___x_2628_);
                crate::leanh::lean_dec_ref(v_opts_2627_);
                if v___x_2629_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_2620_);
                    v___x_2630_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2630_, 0, v_msgData_2619_);
                    return v___x_2630_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_2620_) == 0 {
                        v___x_2631_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2631_, 0, v_msgData_2619_);
                        return v___x_2631_;
                    } else {
                        v_head_2632_ = crate::leanh::lean_ctor_get(v_macroStack_2620_, 0);
                        crate::leanh::lean_inc(v_head_2632_);
                        v_after_2633_ = crate::leanh::lean_ctor_get(v_head_2632_, 1);
                        v_isSharedCheck_2648_ =
                            (!crate::leanh::lean_is_exclusive(v_head_2632_)) as u8;
                        if v_isSharedCheck_2648_ == 0 {
                            v_unused_2649_ = crate::leanh::lean_ctor_get(v_head_2632_, 0);
                            crate::leanh::lean_dec(v_unused_2649_);
                            v___x_2635_ = v_head_2632_;
                            v_isShared_2636_ = v_isSharedCheck_2648_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_2633_);
                            crate::leanh::lean_dec(v_head_2632_);
                            v___x_2635_ = crate::leanh::lean_box(0);
                            v_isShared_2636_ = v_isSharedCheck_2648_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2637_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0);
                if v_isShared_2636_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2635_, 7);
                    crate::leanh::lean_ctor_set(v___x_2635_, 1, v___x_2637_);
                    crate::leanh::lean_ctor_set(v___x_2635_, 0, v_msgData_2619_);
                    v___x_2639_ = v___x_2635_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2647_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_msgData_2619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2647_, 1, v___x_2637_);
                    v___x_2639_ = v_reuseFailAlloc_2647_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2640_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2);
                v___x_2641_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2641_, 0, v___x_2639_);
                crate::leanh::lean_ctor_set(v___x_2641_, 1, v___x_2640_);
                v___x_2642_ = l_Lean_MessageData_ofSyntax(v_after_2633_);
                v___x_2643_ = l_Lean_indentD(v___x_2642_);
                v_msgData_2644_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_2644_, 0, v___x_2641_);
                crate::leanh::lean_ctor_set(v_msgData_2644_, 1, v___x_2643_);
                v___x_2645_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7(v_msgData_2644_, v_macroStack_2620_);
                v___x_2646_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2646_, 0, v___x_2645_);
                return v___x_2646_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_msgData_2650_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2651_: *mut crate::leanh::LeanObject,
    mut v___y_2652_: *mut crate::leanh::LeanObject,
    mut v___y_2653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2654_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(v_msgData_2650_, v_macroStack_2651_, v___y_2652_);
    crate::leanh::lean_dec(v___y_2652_);
    return v_res_2654_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(
    mut v_msg_2655_: *mut crate::leanh::LeanObject,
    mut v___y_2656_: *mut crate::leanh::LeanObject,
    mut v___y_2657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2669_: u8 = 0;
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2674_: u8 = 0;
    let mut v_a_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2678_: u8 = 0;
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2682_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2659_ = l_Lean_Elab_Command_getRef___redArg(v___y_2656_);
                if crate::leanh::lean_obj_tag(v___x_2659_) == 0 {
                    v_a_2660_ = crate::leanh::lean_ctor_get(v___x_2659_, 0);
                    crate::leanh::lean_inc(v_a_2660_);
                    crate::leanh::lean_dec_ref_known(v___x_2659_, 1);
                    v_macroStack_2661_ = crate::leanh::lean_ctor_get(v___y_2656_, 4);
                    v___x_2662_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v_msg_2655_, v___y_2657_);
                    v_a_2663_ = crate::leanh::lean_ctor_get(v___x_2662_, 0);
                    crate::leanh::lean_inc(v_a_2663_);
                    crate::leanh::lean_dec_ref(v___x_2662_);
                    v___x_2664_ = l_Lean_Elab_getBetterRef(v_a_2660_, v_macroStack_2661_);
                    crate::leanh::lean_dec(v_a_2660_);
                    crate::leanh::lean_inc(v_macroStack_2661_);
                    v___x_2665_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(v_a_2663_, v_macroStack_2661_, v___y_2657_);
                    v_a_2666_ = crate::leanh::lean_ctor_get(v___x_2665_, 0);
                    v_isSharedCheck_2674_ = (!crate::leanh::lean_is_exclusive(v___x_2665_)) as u8;
                    if v_isSharedCheck_2674_ == 0 {
                        v___x_2668_ = v___x_2665_;
                        v_isShared_2669_ = v_isSharedCheck_2674_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2666_);
                        crate::leanh::lean_dec(v___x_2665_);
                        v___x_2668_ = crate::leanh::lean_box(0);
                        v_isShared_2669_ = v_isSharedCheck_2674_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msg_2655_);
                    v_a_2675_ = crate::leanh::lean_ctor_get(v___x_2659_, 0);
                    v_isSharedCheck_2682_ = (!crate::leanh::lean_is_exclusive(v___x_2659_)) as u8;
                    if v_isSharedCheck_2682_ == 0 {
                        v___x_2677_ = v___x_2659_;
                        v_isShared_2678_ = v_isSharedCheck_2682_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2675_);
                        crate::leanh::lean_dec(v___x_2659_);
                        v___x_2677_ = crate::leanh::lean_box(0);
                        v_isShared_2678_ = v_isSharedCheck_2682_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2670_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2670_, 0, v___x_2664_);
                crate::leanh::lean_ctor_set(v___x_2670_, 1, v_a_2666_);
                if v_isShared_2669_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2668_, 1);
                    crate::leanh::lean_ctor_set(v___x_2668_, 0, v___x_2670_);
                    v___x_2672_ = v___x_2668_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2673_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
                    v___x_2672_ = v_reuseFailAlloc_2673_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2672_;
            }
            3 => {
                if v_isShared_2678_ == 0 {
                    v___x_2680_ = v___x_2677_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2681_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
                    v___x_2680_ = v_reuseFailAlloc_2681_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2680_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg___boxed(
    mut v_msg_2683_: *mut crate::leanh::LeanObject,
    mut v___y_2684_: *mut crate::leanh::LeanObject,
    mut v___y_2685_: *mut crate::leanh::LeanObject,
    mut v___y_2686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2687_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(v_msg_2683_, v___y_2684_, v___y_2685_);
    crate::leanh::lean_dec(v___y_2685_);
    crate::leanh::lean_dec_ref(v___y_2684_);
    return v_res_2687_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(
    mut v_ref_2688_: *mut crate::leanh::LeanObject,
    mut v_msg_2689_: *mut crate::leanh::LeanObject,
    mut v___y_2690_: *mut crate::leanh::LeanObject,
    mut v___y_2691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2704_: u8 = 0;
    let mut v_ref_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2711_: u8 = 0;
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2715_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2693_ = l_Lean_Elab_Command_getRef___redArg(v___y_2690_);
                if crate::leanh::lean_obj_tag(v___x_2693_) == 0 {
                    v_a_2694_ = crate::leanh::lean_ctor_get(v___x_2693_, 0);
                    crate::leanh::lean_inc(v_a_2694_);
                    crate::leanh::lean_dec_ref_known(v___x_2693_, 1);
                    v_fileName_2695_ = crate::leanh::lean_ctor_get(v___y_2690_, 0);
                    v_fileMap_2696_ = crate::leanh::lean_ctor_get(v___y_2690_, 1);
                    v_currRecDepth_2697_ = crate::leanh::lean_ctor_get(v___y_2690_, 2);
                    v_cmdPos_2698_ = crate::leanh::lean_ctor_get(v___y_2690_, 3);
                    v_macroStack_2699_ = crate::leanh::lean_ctor_get(v___y_2690_, 4);
                    v_quotContext_x3f_2700_ = crate::leanh::lean_ctor_get(v___y_2690_, 5);
                    v_currMacroScope_2701_ = crate::leanh::lean_ctor_get(v___y_2690_, 6);
                    v_snap_x3f_2702_ = crate::leanh::lean_ctor_get(v___y_2690_, 8);
                    v_cancelTk_x3f_2703_ = crate::leanh::lean_ctor_get(v___y_2690_, 9);
                    v_suppressElabErrors_2704_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_2690_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    );
                    v_ref_2705_ = l_Lean_replaceRef(v_ref_2688_, v_a_2694_);
                    crate::leanh::lean_dec(v_a_2694_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_2703_);
                    crate::leanh::lean_inc(v_snap_x3f_2702_);
                    crate::leanh::lean_inc(v_currMacroScope_2701_);
                    crate::leanh::lean_inc(v_quotContext_x3f_2700_);
                    crate::leanh::lean_inc(v_macroStack_2699_);
                    crate::leanh::lean_inc(v_cmdPos_2698_);
                    crate::leanh::lean_inc(v_currRecDepth_2697_);
                    crate::leanh::lean_inc_ref(v_fileMap_2696_);
                    crate::leanh::lean_inc_ref(v_fileName_2695_);
                    v___x_2706_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2706_, 0, v_fileName_2695_);
                    crate::leanh::lean_ctor_set(v___x_2706_, 1, v_fileMap_2696_);
                    crate::leanh::lean_ctor_set(v___x_2706_, 2, v_currRecDepth_2697_);
                    crate::leanh::lean_ctor_set(v___x_2706_, 3, v_cmdPos_2698_);
                    crate::leanh::lean_ctor_set(v___x_2706_, 4, v_macroStack_2699_);
                    crate::leanh::lean_ctor_set(v___x_2706_, 5, v_quotContext_x3f_2700_);
                    crate::leanh::lean_ctor_set(v___x_2706_, 6, v_currMacroScope_2701_);
                    crate::leanh::lean_ctor_set(v___x_2706_, 7, v_ref_2705_);
                    crate::leanh::lean_ctor_set(v___x_2706_, 8, v_snap_x3f_2702_);
                    crate::leanh::lean_ctor_set(v___x_2706_, 9, v_cancelTk_x3f_2703_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2706_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_suppressElabErrors_2704_,
                    );
                    v___x_2707_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(v_msg_2689_, v___x_2706_, v___y_2691_);
                    crate::leanh::lean_dec_ref_known(v___x_2706_, 10);
                    return v___x_2707_;
                } else {
                    crate::leanh::lean_dec_ref(v_msg_2689_);
                    v_a_2708_ = crate::leanh::lean_ctor_get(v___x_2693_, 0);
                    v_isSharedCheck_2715_ = (!crate::leanh::lean_is_exclusive(v___x_2693_)) as u8;
                    if v_isSharedCheck_2715_ == 0 {
                        v___x_2710_ = v___x_2693_;
                        v_isShared_2711_ = v_isSharedCheck_2715_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2708_);
                        crate::leanh::lean_dec(v___x_2693_);
                        v___x_2710_ = crate::leanh::lean_box(0);
                        v_isShared_2711_ = v_isSharedCheck_2715_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2711_ == 0 {
                    v___x_2713_ = v___x_2710_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2714_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
                    v___x_2713_ = v_reuseFailAlloc_2714_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2713_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg___boxed(
    mut v_ref_2716_: *mut crate::leanh::LeanObject,
    mut v_msg_2717_: *mut crate::leanh::LeanObject,
    mut v___y_2718_: *mut crate::leanh::LeanObject,
    mut v___y_2719_: *mut crate::leanh::LeanObject,
    mut v___y_2720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2721_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(v_ref_2716_, v_msg_2717_, v___y_2718_, v___y_2719_);
    crate::leanh::lean_dec(v___y_2719_);
    crate::leanh::lean_dec_ref(v___y_2718_);
    crate::leanh::lean_dec(v_ref_2716_);
    return v_res_2721_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__0;
    v___x_2724_ = l_Lean_stringToMessageData(v___x_2723_);
    return v___x_2724_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2725_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2725_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2726_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2);
    v___x_2727_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2727_, 0, v___x_2726_);
    return v___x_2727_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2728_ = crate::leanh::lean_box(1);
    v___x_2729_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4);
    v___x_2730_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3);
    v___x_2731_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2731_, 0, v___x_2730_);
    crate::leanh::lean_ctor_set(v___x_2731_, 1, v___x_2729_);
    crate::leanh::lean_ctor_set(v___x_2731_, 2, v___x_2728_);
    return v___x_2731_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5;
    v___x_2734_ = l_Lean_stringToMessageData(v___x_2733_);
    return v___x_2734_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7;
    v___x_2737_ = l_Lean_stringToMessageData(v___x_2736_);
    return v___x_2737_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9;
    v___x_2740_ = l_Lean_stringToMessageData(v___x_2739_);
    return v___x_2740_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11;
    v___x_2743_ = l_Lean_stringToMessageData(v___x_2742_);
    return v___x_2743_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13;
    v___x_2746_ = l_Lean_stringToMessageData(v___x_2745_);
    return v___x_2746_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15;
    v___x_2749_ = l_Lean_stringToMessageData(v___x_2748_);
    return v___x_2749_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17;
    v___x_2752_ = l_Lean_stringToMessageData(v___x_2751_);
    return v___x_2752_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(
    mut v_tyName_2753_: *mut crate::leanh::LeanObject,
    mut v_infos_2754_: *mut crate::leanh::LeanObject,
    mut v_as_2755_: *mut crate::leanh::LeanObject,
    mut v_sz_2756_: usize,
    mut v_i_2757_: usize,
    mut v_b_2758_: *mut crate::leanh::LeanObject,
    mut v___y_2759_: *mut crate::leanh::LeanObject,
    mut v___y_2760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: usize = 0;
    let mut v___x_2765_: usize = 0;
    let mut v___x_2767_: u8 = 0;
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: u8 = 0;
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2777_: u8 = 0;
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2781_: u8 = 0;
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_realName_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canonical_2792_: u8 = 0;
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: u8 = 0;
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2815_: u8 = 0;
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2819_: u8 = 0;
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: u8 = 0;
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2834_: u8 = 0;
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2838_: u8 = 0;
    let mut v_a_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2842_: u8 = 0;
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2767_ = lean_usize_dec_lt(v_i_2757_, v_sz_2756_);
                if v___x_2767_ == 0 {
                    crate::leanh::lean_dec(v_tyName_2753_);
                    v___x_2768_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2768_, 0, v_b_2758_);
                    return v___x_2768_;
                } else {
                    v_a_2769_ = lean_array_uget_borrowed(v_as_2755_, v_i_2757_);
                    v___x_2770_ = l_Lake_DSL_declField___closed__1;
                    crate::leanh::lean_inc(v_a_2769_);
                    v___x_2771_ = l_Lean_Syntax_isOfKind(v_a_2769_, v___x_2770_);
                    if v___x_2771_ == 0 {
                        v___x_2772_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1);
                        v___x_2773_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(v_a_2769_, v___x_2772_, v___y_2759_, v___y_2760_);
                        if crate::leanh::lean_obj_tag(v___x_2773_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2773_, 1);
                            v_a_2763_ = v_b_2758_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_b_2758_);
                            crate::leanh::lean_dec(v_tyName_2753_);
                            v_a_2774_ = crate::leanh::lean_ctor_get(v___x_2773_, 0);
                            v_isSharedCheck_2781_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2773_)) as u8;
                            if v_isSharedCheck_2781_ == 0 {
                                v___x_2776_ = v___x_2773_;
                                v_isShared_2777_ = v_isSharedCheck_2781_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2774_);
                                crate::leanh::lean_dec(v___x_2773_);
                                v___x_2776_ = crate::leanh::lean_box(0);
                                v_isShared_2777_ = v_isSharedCheck_2781_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        v___x_2782_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2783_ = l_Lean_Syntax_getArg(v_a_2769_, v___x_2782_);
                        v___x_2784_ = l_Lean_TSyntax_getId(v___x_2783_);
                        crate::leanh::lean_inc(v___x_2784_);
                        v___x_2785_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2785_, 0, v___x_2784_);
                        v___x_2786_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4);
                        crate::leanh::lean_inc(v_tyName_2753_);
                        crate::leanh::lean_inc(v_a_2769_);
                        v___x_2787_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2787_, 0, v_a_2769_);
                        crate::leanh::lean_ctor_set(v___x_2787_, 1, v___x_2785_);
                        crate::leanh::lean_ctor_set(v___x_2787_, 2, v___x_2786_);
                        crate::leanh::lean_ctor_set(v___x_2787_, 3, v_tyName_2753_);
                        v___x_2788_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(v___x_2787_, v___y_2759_, v___y_2760_);
                        if crate::leanh::lean_obj_tag(v___x_2788_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2788_, 1);
                            v___x_2789_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_infos_2754_, v___x_2784_);
                            if crate::leanh::lean_obj_tag(v___x_2789_) == 1 {
                                v_val_2790_ = crate::leanh::lean_ctor_get(v___x_2789_, 0);
                                crate::leanh::lean_inc(v_val_2790_);
                                crate::leanh::lean_dec_ref_known(v___x_2789_, 1);
                                v_realName_2791_ = crate::leanh::lean_ctor_get(v_val_2790_, 1);
                                crate::leanh::lean_inc(v_realName_2791_);
                                v_canonical_2792_ = crate::leanh::lean_ctor_get_uint8(
                                    v_val_2790_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                                        as u32,
                                );
                                crate::leanh::lean_dec(v_val_2790_);
                                v___x_2793_ = crate::leanh::lean_unsigned_to_nat(2);
                                v___x_2794_ = l_Lean_Syntax_getArg(v_a_2769_, v___x_2793_);
                                if v_canonical_2792_ == 0 {
                                    if v___x_2771_ == 0 {
                                        crate::leanh::lean_dec(v___x_2784_);
                                        state = 4;
                                        continue;
                                    } else {
                                        v___x_2798_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_realName_2791_, v_b_2758_);
                                        if v___x_2798_ == 0 {
                                            crate::leanh::lean_dec(v___x_2784_);
                                            state = 4;
                                            continue;
                                        } else {
                                            v___x_2799_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6);
                                            crate::leanh::lean_inc(v_realName_2791_);
                                            v___x_2800_ =
                                                l_Lean_MessageData_ofName(v_realName_2791_);
                                            crate::leanh::lean_inc_ref(v___x_2800_);
                                            v___x_2801_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2801_,
                                                0,
                                                v___x_2799_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_2801_,
                                                1,
                                                v___x_2800_,
                                            );
                                            v___x_2802_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8);
                                            v___x_2803_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2803_,
                                                0,
                                                v___x_2801_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_2803_,
                                                1,
                                                v___x_2802_,
                                            );
                                            v___x_2804_ = l_Lean_MessageData_ofName(v___x_2784_);
                                            v___x_2805_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2805_,
                                                0,
                                                v___x_2803_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_2805_,
                                                1,
                                                v___x_2804_,
                                            );
                                            v___x_2806_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10);
                                            v___x_2807_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2807_,
                                                0,
                                                v___x_2805_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_2807_,
                                                1,
                                                v___x_2806_,
                                            );
                                            v___x_2808_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2808_,
                                                0,
                                                v___x_2807_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_2808_,
                                                1,
                                                v___x_2800_,
                                            );
                                            v___x_2809_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12);
                                            v___x_2810_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2810_,
                                                0,
                                                v___x_2808_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_2810_,
                                                1,
                                                v___x_2809_,
                                            );
                                            v___x_2811_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(v___x_2783_, v___x_2810_, v___y_2759_, v___y_2760_);
                                            if crate::leanh::lean_obj_tag(v___x_2811_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_2811_, 1);
                                                state = 4;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v___x_2794_);
                                                crate::leanh::lean_dec(v_realName_2791_);
                                                crate::leanh::lean_dec(v___x_2783_);
                                                crate::leanh::lean_dec(v_b_2758_);
                                                crate::leanh::lean_dec(v_tyName_2753_);
                                                v_a_2812_ =
                                                    crate::leanh::lean_ctor_get(v___x_2811_, 0);
                                                v_isSharedCheck_2819_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2811_))
                                                        as u8;
                                                if v_isSharedCheck_2819_ == 0 {
                                                    v___x_2814_ = v___x_2811_;
                                                    v_isShared_2815_ = v_isSharedCheck_2819_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2812_);
                                                    crate::leanh::lean_dec(v___x_2811_);
                                                    v___x_2814_ = crate::leanh::lean_box(0);
                                                    v_isShared_2815_ = v_isSharedCheck_2819_;
                                                    state = 5;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_2784_);
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_2789_);
                                v___x_2820_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14);
                                v___x_2821_ = 0;
                                crate::leanh::lean_inc(v_tyName_2753_);
                                v___x_2822_ =
                                    l_Lean_MessageData_ofConstName(v_tyName_2753_, v___x_2821_);
                                v___x_2823_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2823_, 0, v___x_2820_);
                                crate::leanh::lean_ctor_set(v___x_2823_, 1, v___x_2822_);
                                v___x_2824_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16);
                                v___x_2825_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2825_, 0, v___x_2823_);
                                crate::leanh::lean_ctor_set(v___x_2825_, 1, v___x_2824_);
                                v___x_2826_ = l_Lean_MessageData_ofName(v___x_2784_);
                                v___x_2827_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2827_, 0, v___x_2825_);
                                crate::leanh::lean_ctor_set(v___x_2827_, 1, v___x_2826_);
                                v___x_2828_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__18), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__18_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__18);
                                v___x_2829_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2829_, 0, v___x_2827_);
                                crate::leanh::lean_ctor_set(v___x_2829_, 1, v___x_2828_);
                                v___x_2830_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(v___x_2783_, v___x_2829_, v___y_2759_, v___y_2760_);
                                crate::leanh::lean_dec(v___x_2783_);
                                if crate::leanh::lean_obj_tag(v___x_2830_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_2830_, 1);
                                    v_a_2763_ = v_b_2758_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_b_2758_);
                                    crate::leanh::lean_dec(v_tyName_2753_);
                                    v_a_2831_ = crate::leanh::lean_ctor_get(v___x_2830_, 0);
                                    v_isSharedCheck_2838_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2830_)) as u8;
                                    if v_isSharedCheck_2838_ == 0 {
                                        v___x_2833_ = v___x_2830_;
                                        v_isShared_2834_ = v_isSharedCheck_2838_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2831_);
                                        crate::leanh::lean_dec(v___x_2830_);
                                        v___x_2833_ = crate::leanh::lean_box(0);
                                        v_isShared_2834_ = v_isSharedCheck_2838_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2784_);
                            crate::leanh::lean_dec(v___x_2783_);
                            crate::leanh::lean_dec(v_b_2758_);
                            crate::leanh::lean_dec(v_tyName_2753_);
                            v_a_2839_ = crate::leanh::lean_ctor_get(v___x_2788_, 0);
                            v_isSharedCheck_2846_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2788_)) as u8;
                            if v_isSharedCheck_2846_ == 0 {
                                v___x_2841_ = v___x_2788_;
                                v_isShared_2842_ = v_isSharedCheck_2846_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2839_);
                                crate::leanh::lean_dec(v___x_2788_);
                                v___x_2841_ = crate::leanh::lean_box(0);
                                v_isShared_2842_ = v_isSharedCheck_2846_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2764_ = 1usize;
                v___x_2765_ = lean_usize_add(v_i_2757_, v___x_2764_);
                v_i_2757_ = v___x_2765_;
                v_b_2758_ = v_a_2763_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_2777_ == 0 {
                    v___x_2779_ = v___x_2776_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2780_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
                    v___x_2779_ = v_reuseFailAlloc_2780_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2779_;
            }
            4 => {
                v___x_2796_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2796_, 0, v___x_2783_);
                crate::leanh::lean_ctor_set(v___x_2796_, 1, v___x_2794_);
                v___x_2797_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_realName_2791_, v___x_2796_, v_b_2758_);
                v_a_2763_ = v___x_2797_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_2815_ == 0 {
                    v___x_2817_ = v___x_2814_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2818_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
                    v___x_2817_ = v_reuseFailAlloc_2818_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2817_;
            }
            7 => {
                if v_isShared_2834_ == 0 {
                    v___x_2836_ = v___x_2833_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2837_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
                    v___x_2836_ = v_reuseFailAlloc_2837_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2836_;
            }
            9 => {
                if v_isShared_2842_ == 0 {
                    v___x_2844_ = v___x_2841_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2845_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
                    v___x_2844_ = v_reuseFailAlloc_2845_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2844_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___boxed(
    mut v_tyName_2847_: *mut crate::leanh::LeanObject,
    mut v_infos_2848_: *mut crate::leanh::LeanObject,
    mut v_as_2849_: *mut crate::leanh::LeanObject,
    mut v_sz_2850_: *mut crate::leanh::LeanObject,
    mut v_i_2851_: *mut crate::leanh::LeanObject,
    mut v_b_2852_: *mut crate::leanh::LeanObject,
    mut v___y_2853_: *mut crate::leanh::LeanObject,
    mut v___y_2854_: *mut crate::leanh::LeanObject,
    mut v___y_2855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2856_: usize = 0;
    let mut v_i_boxed_2857_: usize = 0;
    let mut v_res_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2856_ = crate::leanh::lean_unbox_usize(v_sz_2850_);
    crate::leanh::lean_dec(v_sz_2850_);
    v_i_boxed_2857_ = crate::leanh::lean_unbox_usize(v_i_2851_);
    crate::leanh::lean_dec(v_i_2851_);
    v_res_2858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(v_tyName_2847_, v_infos_2848_, v_as_2849_, v_sz_boxed_2856_, v_i_boxed_2857_, v_b_2852_, v___y_2853_, v___y_2854_);
    crate::leanh::lean_dec(v___y_2854_);
    crate::leanh::lean_dec_ref(v___y_2853_);
    crate::leanh::lean_dec_ref(v_as_2849_);
    crate::leanh::lean_dec(v_infos_2848_);
    return v_res_2858_;
}
pub unsafe fn l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(
    mut v_tyName_2870_: *mut crate::leanh::LeanObject,
    mut v_infos_2871_: *mut crate::leanh::LeanObject,
    mut v_fs_2872_: *mut crate::leanh::LeanObject,
    mut v_a_2873_: *mut crate::leanh::LeanObject,
    mut v_a_2874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_m_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2877_: usize = 0;
    let mut v___x_2878_: usize = 0;
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2886_: u8 = 0;
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2898_: u8 = 0;
    let mut v_a_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2902_: u8 = 0;
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2906_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_m_2876_ = crate::leanh::lean_box(1);
                v_sz_2877_ = lean_array_size(v_fs_2872_);
                v___x_2878_ = 0usize;
                v___x_2879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(v_tyName_2870_, v_infos_2871_, v_fs_2872_, v_sz_2877_, v___x_2878_, v_m_2876_, v_a_2873_, v_a_2874_);
                if crate::leanh::lean_obj_tag(v___x_2879_) == 0 {
                    v_a_2880_ = crate::leanh::lean_ctor_get(v___x_2879_, 0);
                    crate::leanh::lean_inc(v_a_2880_);
                    crate::leanh::lean_dec_ref_known(v___x_2879_, 1);
                    v___x_2881_ = l_Lake_DSL_expandAttrs___closed__5;
                    v___x_2882_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(v___x_2881_, v_a_2880_);
                    v_a_2883_ = crate::leanh::lean_ctor_get(v___x_2882_, 0);
                    v_isSharedCheck_2898_ = (!crate::leanh::lean_is_exclusive(v___x_2882_)) as u8;
                    if v_isSharedCheck_2898_ == 0 {
                        v___x_2885_ = v___x_2882_;
                        v_isShared_2886_ = v_isSharedCheck_2898_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2883_);
                        crate::leanh::lean_dec(v___x_2882_);
                        v___x_2885_ = crate::leanh::lean_box(0);
                        v_isShared_2886_ = v_isSharedCheck_2898_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2899_ = crate::leanh::lean_ctor_get(v___x_2879_, 0);
                    v_isSharedCheck_2906_ = (!crate::leanh::lean_is_exclusive(v___x_2879_)) as u8;
                    if v_isSharedCheck_2906_ == 0 {
                        v___x_2901_ = v___x_2879_;
                        v_isShared_2902_ = v_isSharedCheck_2906_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2899_);
                        crate::leanh::lean_dec(v___x_2879_);
                        v___x_2901_ = crate::leanh::lean_box(0);
                        v_isShared_2902_ = v_isSharedCheck_2906_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2887_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0;
                v___x_2888_ = crate::leanh::lean_box(2);
                v___x_2889_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__2;
                v___x_2890_ = l_Lean_Syntax_mkSep(v_a_2883_, v___x_2889_);
                crate::leanh::lean_dec(v_a_2883_);
                v___x_2891_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2892_ = lean_mk_empty_array_with_capacity(v___x_2891_);
                v___x_2893_ = lean_array_push(v___x_2892_, v___x_2890_);
                v___x_2894_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2894_, 0, v___x_2888_);
                crate::leanh::lean_ctor_set(v___x_2894_, 1, v___x_2887_);
                crate::leanh::lean_ctor_set(v___x_2894_, 2, v___x_2893_);
                if v_isShared_2886_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2885_, 0, v___x_2894_);
                    v___x_2896_ = v___x_2885_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2897_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2894_);
                    v___x_2896_ = v_reuseFailAlloc_2897_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2896_;
            }
            3 => {
                if v_isShared_2902_ == 0 {
                    v___x_2904_ = v___x_2901_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2905_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
                    v___x_2904_ = v_reuseFailAlloc_2905_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2904_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___boxed(
    mut v_tyName_2907_: *mut crate::leanh::LeanObject,
    mut v_infos_2908_: *mut crate::leanh::LeanObject,
    mut v_fs_2909_: *mut crate::leanh::LeanObject,
    mut v_a_2910_: *mut crate::leanh::LeanObject,
    mut v_a_2911_: *mut crate::leanh::LeanObject,
    mut v_a_2912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2913_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(
        v_tyName_2907_,
        v_infos_2908_,
        v_fs_2909_,
        v_a_2910_,
        v_a_2911_,
    );
    crate::leanh::lean_dec(v_a_2911_);
    crate::leanh::lean_dec_ref(v_a_2910_);
    crate::leanh::lean_dec_ref(v_fs_2909_);
    crate::leanh::lean_dec(v_infos_2908_);
    return v_res_2913_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0(
    mut v_00_u03b1_2914_: *mut crate::leanh::LeanObject,
    mut v_ref_2915_: *mut crate::leanh::LeanObject,
    mut v_msg_2916_: *mut crate::leanh::LeanObject,
    mut v___y_2917_: *mut crate::leanh::LeanObject,
    mut v___y_2918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2920_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(v_ref_2915_, v_msg_2916_, v___y_2917_, v___y_2918_);
    return v___x_2920_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___boxed(
    mut v_00_u03b1_2921_: *mut crate::leanh::LeanObject,
    mut v_ref_2922_: *mut crate::leanh::LeanObject,
    mut v_msg_2923_: *mut crate::leanh::LeanObject,
    mut v___y_2924_: *mut crate::leanh::LeanObject,
    mut v___y_2925_: *mut crate::leanh::LeanObject,
    mut v___y_2926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2927_ =
        l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0(
            v_00_u03b1_2921_,
            v_ref_2922_,
            v_msg_2923_,
            v___y_2924_,
            v___y_2925_,
        );
    crate::leanh::lean_dec(v___y_2925_);
    crate::leanh::lean_dec_ref(v___y_2924_);
    crate::leanh::lean_dec(v_ref_2922_);
    return v_res_2927_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4(
    mut v_init_2928_: *mut crate::leanh::LeanObject,
    mut v_x_2929_: *mut crate::leanh::LeanObject,
    mut v___y_2930_: *mut crate::leanh::LeanObject,
    mut v___y_2931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2933_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(v_init_2928_, v_x_2929_);
    return v___x_2933_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___boxed(
    mut v_init_2934_: *mut crate::leanh::LeanObject,
    mut v_x_2935_: *mut crate::leanh::LeanObject,
    mut v___y_2936_: *mut crate::leanh::LeanObject,
    mut v___y_2937_: *mut crate::leanh::LeanObject,
    mut v___y_2938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2939_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4(v_init_2934_, v_x_2935_, v___y_2936_, v___y_2937_);
    crate::leanh::lean_dec(v___y_2937_);
    crate::leanh::lean_dec_ref(v___y_2936_);
    return v_res_2939_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1(
    mut v_msgData_2940_: *mut crate::leanh::LeanObject,
    mut v___y_2941_: *mut crate::leanh::LeanObject,
    mut v___y_2942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2944_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v_msgData_2940_, v___y_2942_);
    return v___x_2944_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_2945_: *mut crate::leanh::LeanObject,
    mut v___y_2946_: *mut crate::leanh::LeanObject,
    mut v___y_2947_: *mut crate::leanh::LeanObject,
    mut v___y_2948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2949_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1(v_msgData_2945_, v___y_2946_, v___y_2947_);
    crate::leanh::lean_dec(v___y_2947_);
    crate::leanh::lean_dec_ref(v___y_2946_);
    return v_res_2949_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0(
    mut v_00_u03b1_2950_: *mut crate::leanh::LeanObject,
    mut v_msg_2951_: *mut crate::leanh::LeanObject,
    mut v___y_2952_: *mut crate::leanh::LeanObject,
    mut v___y_2953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2955_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(v_msg_2951_, v___y_2952_, v___y_2953_);
    return v___x_2955_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___boxed(
    mut v_00_u03b1_2956_: *mut crate::leanh::LeanObject,
    mut v_msg_2957_: *mut crate::leanh::LeanObject,
    mut v___y_2958_: *mut crate::leanh::LeanObject,
    mut v___y_2959_: *mut crate::leanh::LeanObject,
    mut v___y_2960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2961_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0(v_00_u03b1_2956_, v_msg_2957_, v___y_2958_, v___y_2959_);
    crate::leanh::lean_dec(v___y_2959_);
    crate::leanh::lean_dec_ref(v___y_2958_);
    return v_res_2961_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5(
    mut v_t_2962_: *mut crate::leanh::LeanObject,
    mut v___y_2963_: *mut crate::leanh::LeanObject,
    mut v___y_2964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2966_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(v_t_2962_, v___y_2964_);
    return v___x_2966_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___boxed(
    mut v_t_2967_: *mut crate::leanh::LeanObject,
    mut v___y_2968_: *mut crate::leanh::LeanObject,
    mut v___y_2969_: *mut crate::leanh::LeanObject,
    mut v___y_2970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2971_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5(v_t_2967_, v___y_2968_, v___y_2969_);
    crate::leanh::lean_dec(v___y_2969_);
    crate::leanh::lean_dec_ref(v___y_2968_);
    return v_res_2971_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2(
    mut v_msgData_2972_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2973_: *mut crate::leanh::LeanObject,
    mut v___y_2974_: *mut crate::leanh::LeanObject,
    mut v___y_2975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2977_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(v_msgData_2972_, v_macroStack_2973_, v___y_2975_);
    return v___x_2977_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___boxed(
    mut v_msgData_2978_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2979_: *mut crate::leanh::LeanObject,
    mut v___y_2980_: *mut crate::leanh::LeanObject,
    mut v___y_2981_: *mut crate::leanh::LeanObject,
    mut v___y_2982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2983_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2(v_msgData_2978_, v_macroStack_2979_, v___y_2980_, v___y_2981_);
    crate::leanh::lean_dec(v___y_2981_);
    crate::leanh::lean_dec_ref(v___y_2980_);
    return v_res_2983_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(
    mut v___y_2984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mainModule_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2986_ = lean_st_ref_get(v___y_2984_);
    v_env_2987_ = crate::leanh::lean_ctor_get(v___x_2986_, 0);
    crate::leanh::lean_inc_ref(v_env_2987_);
    crate::leanh::lean_dec(v___x_2986_);
    v___x_2988_ = l_Lean_Environment_header(v_env_2987_);
    crate::leanh::lean_dec_ref(v_env_2987_);
    v_mainModule_2989_ = crate::leanh::lean_ctor_get(v___x_2988_, 0);
    crate::leanh::lean_inc(v_mainModule_2989_);
    crate::leanh::lean_dec_ref(v___x_2988_);
    v___x_2990_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2990_, 0, v_mainModule_2989_);
    return v___x_2990_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg___boxed(
    mut v___y_2991_: *mut crate::leanh::LeanObject,
    mut v___y_2992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2993_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(v___y_2991_);
    crate::leanh::lean_dec(v___y_2991_);
    return v_res_2993_;
}
pub unsafe fn l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0(
    mut v___x_2994_: *mut crate::leanh::LeanObject,
    mut v___y_2995_: *mut crate::leanh::LeanObject,
    mut v___y_2996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3004_: u8 = 0;
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3009_: u8 = 0;
    let mut v_a_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3013_: u8 = 0;
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3017_: u8 = 0;
    let mut v_quotContext_x3f_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_quotContext_x3f_3018_ = crate::leanh::lean_ctor_get(v___y_2995_, 5);
                if crate::leanh::lean_obj_tag(v_quotContext_x3f_3018_) == 0 {
                    v___x_3019_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(v___y_2996_);
                    v_a_3020_ = crate::leanh::lean_ctor_get(v___x_3019_, 0);
                    crate::leanh::lean_inc(v_a_3020_);
                    crate::leanh::lean_dec_ref(v___x_3019_);
                    v_a_2999_ = v_a_3020_;
                    state = 1;
                    continue;
                } else {
                    v_val_3021_ = crate::leanh::lean_ctor_get(v_quotContext_x3f_3018_, 0);
                    crate::leanh::lean_inc(v_val_3021_);
                    v_a_2999_ = v_val_3021_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3000_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2995_);
                crate::leanh::lean_dec_ref(v___y_2995_);
                if crate::leanh::lean_obj_tag(v___x_3000_) == 0 {
                    v_a_3001_ = crate::leanh::lean_ctor_get(v___x_3000_, 0);
                    v_isSharedCheck_3009_ = (!crate::leanh::lean_is_exclusive(v___x_3000_)) as u8;
                    if v_isSharedCheck_3009_ == 0 {
                        v___x_3003_ = v___x_3000_;
                        v_isShared_3004_ = v_isSharedCheck_3009_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3001_);
                        crate::leanh::lean_dec(v___x_3000_);
                        v___x_3003_ = crate::leanh::lean_box(0);
                        v_isShared_3004_ = v_isSharedCheck_3009_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2999_);
                    crate::leanh::lean_dec(v___x_2994_);
                    v_a_3010_ = crate::leanh::lean_ctor_get(v___x_3000_, 0);
                    v_isSharedCheck_3017_ = (!crate::leanh::lean_is_exclusive(v___x_3000_)) as u8;
                    if v_isSharedCheck_3017_ == 0 {
                        v___x_3012_ = v___x_3000_;
                        v_isShared_3013_ = v_isSharedCheck_3017_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3010_);
                        crate::leanh::lean_dec(v___x_3000_);
                        v___x_3012_ = crate::leanh::lean_box(0);
                        v_isShared_3013_ = v_isSharedCheck_3017_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3005_ = l_Lean_addMacroScope(v_a_2999_, v___x_2994_, v_a_3001_);
                if v_isShared_3004_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3003_, 0, v___x_3005_);
                    v___x_3007_ = v___x_3003_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3008_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3005_);
                    v___x_3007_ = v_reuseFailAlloc_3008_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3007_;
            }
            4 => {
                if v_isShared_3013_ == 0 {
                    v___x_3015_ = v___x_3012_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3016_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
                    v___x_3015_ = v_reuseFailAlloc_3016_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3015_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0___boxed(
    mut v___x_3022_: *mut crate::leanh::LeanObject,
    mut v___y_3023_: *mut crate::leanh::LeanObject,
    mut v___y_3024_: *mut crate::leanh::LeanObject,
    mut v___y_3025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3026_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0(v___x_3022_, v___y_3023_, v___y_3024_);
    crate::leanh::lean_dec(v___y_3024_);
    return v_res_3026_;
}
pub unsafe fn l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(
    mut v___y_3032_: *mut crate::leanh::LeanObject,
    mut v___y_3033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3035_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__2;
    v___x_3036_ =
        l_Lean_Elab_Command_withFreshMacroScope___redArg(v___f_3035_, v___y_3032_, v___y_3033_);
    return v___x_3036_;
}
pub unsafe fn l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___boxed(
    mut v___y_3037_: *mut crate::leanh::LeanObject,
    mut v___y_3038_: *mut crate::leanh::LeanObject,
    mut v___y_3039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3040_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(v___y_3037_, v___y_3038_);
    crate::leanh::lean_dec(v___y_3038_);
    crate::leanh::lean_dec_ref(v___y_3037_);
    return v_res_3040_;
}
pub unsafe fn l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(
    mut v_ref_3041_: *mut crate::leanh::LeanObject,
    mut v_canonical_3042_: u8,
    mut v___y_3043_: *mut crate::leanh::LeanObject,
    mut v___y_3044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3050_: u8 = 0;
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3055_: u8 = 0;
    let mut v_a_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3059_: u8 = 0;
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3063_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3046_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(v___y_3043_, v___y_3044_);
                if crate::leanh::lean_obj_tag(v___x_3046_) == 0 {
                    v_a_3047_ = crate::leanh::lean_ctor_get(v___x_3046_, 0);
                    v_isSharedCheck_3055_ = (!crate::leanh::lean_is_exclusive(v___x_3046_)) as u8;
                    if v_isSharedCheck_3055_ == 0 {
                        v___x_3049_ = v___x_3046_;
                        v_isShared_3050_ = v_isSharedCheck_3055_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3047_);
                        crate::leanh::lean_dec(v___x_3046_);
                        v___x_3049_ = crate::leanh::lean_box(0);
                        v_isShared_3050_ = v_isSharedCheck_3055_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3056_ = crate::leanh::lean_ctor_get(v___x_3046_, 0);
                    v_isSharedCheck_3063_ = (!crate::leanh::lean_is_exclusive(v___x_3046_)) as u8;
                    if v_isSharedCheck_3063_ == 0 {
                        v___x_3058_ = v___x_3046_;
                        v_isShared_3059_ = v_isSharedCheck_3063_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3056_);
                        crate::leanh::lean_dec(v___x_3046_);
                        v___x_3058_ = crate::leanh::lean_box(0);
                        v_isShared_3059_ = v_isSharedCheck_3063_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3051_ = l_Lean_mkIdentFrom(v_ref_3041_, v_a_3047_, v_canonical_3042_);
                if v_isShared_3050_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3049_, 0, v___x_3051_);
                    v___x_3053_ = v___x_3049_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3054_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3051_);
                    v___x_3053_ = v_reuseFailAlloc_3054_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3053_;
            }
            3 => {
                if v_isShared_3059_ == 0 {
                    v___x_3061_ = v___x_3058_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3062_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
                    v___x_3061_ = v_reuseFailAlloc_3062_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0___boxed(
    mut v_ref_3064_: *mut crate::leanh::LeanObject,
    mut v_canonical_3065_: *mut crate::leanh::LeanObject,
    mut v___y_3066_: *mut crate::leanh::LeanObject,
    mut v___y_3067_: *mut crate::leanh::LeanObject,
    mut v___y_3068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonical_boxed_3069_: u8 = 0;
    let mut v_res_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonical_boxed_3069_ = (crate::leanh::lean_unbox(v_canonical_3065_) as u8);
    v_res_3070_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(
        v_ref_3064_,
        v_canonical_boxed_3069_,
        v___y_3066_,
        v___y_3067_,
    );
    crate::leanh::lean_dec(v___y_3067_);
    crate::leanh::lean_dec_ref(v___y_3066_);
    crate::leanh::lean_dec(v_ref_3064_);
    return v_res_3070_;
}
pub unsafe fn l_Lake_DSL_mkConfigDeclIdent(
    mut v_stx_x3f_3071_: *mut crate::leanh::LeanObject,
    mut v_a_3072_: *mut crate::leanh::LeanObject,
    mut v_a_3073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: u8 = 0;
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3082_: u8 = 0;
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3086_: u8 = 0;
    let mut v_val_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3090_: u8 = 0;
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3095_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_stx_x3f_3071_) == 0 {
                    v___x_3075_ = l_Lean_Elab_Command_getRef___redArg(v_a_3072_);
                    if crate::leanh::lean_obj_tag(v___x_3075_) == 0 {
                        v_a_3076_ = crate::leanh::lean_ctor_get(v___x_3075_, 0);
                        crate::leanh::lean_inc(v_a_3076_);
                        crate::leanh::lean_dec_ref_known(v___x_3075_, 1);
                        v___x_3077_ = 0;
                        v___x_3078_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(v_a_3076_, v___x_3077_, v_a_3072_, v_a_3073_);
                        crate::leanh::lean_dec(v_a_3076_);
                        return v___x_3078_;
                    } else {
                        v_a_3079_ = crate::leanh::lean_ctor_get(v___x_3075_, 0);
                        v_isSharedCheck_3086_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3075_)) as u8;
                        if v_isSharedCheck_3086_ == 0 {
                            v___x_3081_ = v___x_3075_;
                            v_isShared_3082_ = v_isSharedCheck_3086_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3079_);
                            crate::leanh::lean_dec(v___x_3075_);
                            v___x_3081_ = crate::leanh::lean_box(0);
                            v_isShared_3082_ = v_isSharedCheck_3086_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_val_3087_ = crate::leanh::lean_ctor_get(v_stx_x3f_3071_, 0);
                    v_isSharedCheck_3095_ =
                        (!crate::leanh::lean_is_exclusive(v_stx_x3f_3071_)) as u8;
                    if v_isSharedCheck_3095_ == 0 {
                        v___x_3089_ = v_stx_x3f_3071_;
                        v_isShared_3090_ = v_isSharedCheck_3095_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3087_);
                        crate::leanh::lean_dec(v_stx_x3f_3071_);
                        v___x_3089_ = crate::leanh::lean_box(0);
                        v_isShared_3090_ = v_isSharedCheck_3095_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3082_ == 0 {
                    v___x_3084_ = v___x_3081_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
                    v___x_3084_ = v_reuseFailAlloc_3085_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3084_;
            }
            3 => {
                v___x_3091_ = l_Lake_DSL_expandIdentOrStrAsIdent(v_val_3087_);
                if v_isShared_3090_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3089_, 0);
                    crate::leanh::lean_ctor_set(v___x_3089_, 0, v___x_3091_);
                    v___x_3093_ = v___x_3089_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3094_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3091_);
                    v___x_3093_ = v_reuseFailAlloc_3094_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3093_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_DSL_mkConfigDeclIdent___boxed(
    mut v_stx_x3f_3096_: *mut crate::leanh::LeanObject,
    mut v_a_3097_: *mut crate::leanh::LeanObject,
    mut v_a_3098_: *mut crate::leanh::LeanObject,
    mut v_a_3099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3100_ = l_Lake_DSL_mkConfigDeclIdent(v_stx_x3f_3096_, v_a_3097_, v_a_3098_);
    crate::leanh::lean_dec(v_a_3098_);
    crate::leanh::lean_dec_ref(v_a_3097_);
    return v_res_3100_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1(
    mut v___y_3101_: *mut crate::leanh::LeanObject,
    mut v___y_3102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3104_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(v___y_3102_);
    return v___x_3104_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___boxed(
    mut v___y_3105_: *mut crate::leanh::LeanObject,
    mut v___y_3106_: *mut crate::leanh::LeanObject,
    mut v___y_3107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3108_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1(v___y_3105_, v___y_3106_);
    crate::leanh::lean_dec(v___y_3106_);
    crate::leanh::lean_dec_ref(v___y_3105_);
    return v_res_3108_;
}
pub unsafe fn _init_l_Lake_DSL_elabConfig___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3115_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_3115_;
}
pub unsafe fn _init_l_Lake_DSL_elabConfig___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3116_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__6_once),
        _init_l_Lake_DSL_elabConfig___closed__6,
    );
    v___x_3117_ = l_StateRefT_x27_instMonad___redArg(v___x_3116_);
    return v___x_3117_;
}
pub unsafe fn _init_l_Lake_DSL_elabConfig___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3127_ = l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
    v___x_3128_ = l_Lean_Elab_Command_instMonadRefCommandElabM;
    v___x_3129_ = l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
    v___x_3130_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3130_, 0, v___x_3129_);
    crate::leanh::lean_ctor_set(v___x_3130_, 1, v___x_3128_);
    crate::leanh::lean_ctor_set(v___x_3130_, 2, v___x_3127_);
    return v___x_3130_;
}
pub unsafe fn _init_l_Lake_DSL_elabConfig___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3132_ = l_Lake_DSL_elabConfig___closed__14;
    v___x_3133_ = l_Lean_stringToMessageData(v___x_3132_);
    return v___x_3133_;
}
pub unsafe fn l_Lake_DSL_elabConfig(
    mut v_tyName_3134_: *mut crate::leanh::LeanObject,
    mut v_info_3135_: *mut crate::leanh::LeanObject,
    mut v_id_3136_: *mut crate::leanh::LeanObject,
    mut v_ty_3137_: *mut crate::leanh::LeanObject,
    mut v_config_3138_: *mut crate::leanh::LeanObject,
    mut v_a_3139_: *mut crate::leanh::LeanObject,
    mut v_a_3140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: u8 = 0;
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252__overap_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3232_: u8 = 0;
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3236_: u8 = 0;
    let mut v_a_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3240_: u8 = 0;
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3244_: u8 = 0;
    let mut v_a_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3248_: u8 = 0;
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3252_: u8 = 0;
    let mut v_whereInfo_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fs_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldMap_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_whereTk_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3272_: u8 = 0;
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3276_: u8 = 0;
    let mut v_a_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3280_: u8 = 0;
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3284_: u8 = 0;
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: u8 = 0;
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268__overap_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: u8 = 0;
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: u8 = 0;
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683__overap_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: u8 = 0;
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: u8 = 0;
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981__overap_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: u8 = 0;
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079__overap_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: u8 = 0;
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164__overap_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fs_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: u8 = 0;
    let mut v___x_3350_: u8 = 0;
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273__overap_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: u8 = 0;
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310__overap_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: u8 = 0;
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406__overap_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fs_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: u8 = 0;
    let mut v___x_3383_: u8 = 0;
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516__overap_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: u8 = 0;
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553__overap_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3285_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__7),
                    core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__7_once),
                    _init_l_Lake_DSL_elabConfig___closed__7,
                );
                v_toApplicative_3286_ = crate::leanh::lean_ctor_get(v___x_3285_, 0);
                v_toFunctor_3287_ = crate::leanh::lean_ctor_get(v_toApplicative_3286_, 0);
                v_toSeq_3288_ = crate::leanh::lean_ctor_get(v_toApplicative_3286_, 2);
                v_toSeqLeft_3289_ = crate::leanh::lean_ctor_get(v_toApplicative_3286_, 3);
                v_toSeqRight_3290_ = crate::leanh::lean_ctor_get(v_toApplicative_3286_, 4);
                v___f_3291_ = l_Lake_DSL_elabConfig___closed__8;
                v___f_3292_ = l_Lake_DSL_elabConfig___closed__9;
                crate::leanh::lean_inc_ref_n(v_toFunctor_3287_, 2);
                v___f_3293_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3293_, 0, v_toFunctor_3287_);
                v___f_3294_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3294_, 0, v_toFunctor_3287_);
                v___x_3295_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3295_, 0, v___f_3293_);
                crate::leanh::lean_ctor_set(v___x_3295_, 1, v___f_3294_);
                crate::leanh::lean_inc(v_toSeqRight_3290_);
                v___f_3296_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3296_, 0, v_toSeqRight_3290_);
                crate::leanh::lean_inc(v_toSeqLeft_3289_);
                v___f_3297_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3297_, 0, v_toSeqLeft_3289_);
                crate::leanh::lean_inc(v_toSeq_3288_);
                v___f_3298_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3298_, 0, v_toSeq_3288_);
                v___x_3299_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3299_, 0, v___x_3295_);
                crate::leanh::lean_ctor_set(v___x_3299_, 1, v___f_3291_);
                crate::leanh::lean_ctor_set(v___x_3299_, 2, v___f_3298_);
                crate::leanh::lean_ctor_set(v___x_3299_, 3, v___f_3297_);
                crate::leanh::lean_ctor_set(v___x_3299_, 4, v___f_3296_);
                v___x_3300_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3300_, 0, v___x_3299_);
                crate::leanh::lean_ctor_set(v___x_3300_, 1, v___f_3292_);
                v___x_3301_ = l_Lake_DSL_optConfig___closed__1;
                crate::leanh::lean_inc(v_config_3138_);
                v___x_3302_ = l_Lean_Syntax_isOfKind(v_config_3138_, v___x_3301_);
                if v___x_3302_ == 0 {
                    crate::leanh::lean_dec(v_ty_3137_);
                    crate::leanh::lean_dec(v_id_3136_);
                    crate::leanh::lean_dec(v_tyName_3134_);
                    v___x_3303_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__13),
                        core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__13_once),
                        _init_l_Lake_DSL_elabConfig___closed__13,
                    );
                    v___x_3304_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__15),
                        core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__15_once),
                        _init_l_Lake_DSL_elabConfig___closed__15,
                    );
                    v___x_4268__overap_3305_ = l_Lean_throwErrorAt___redArg(
                        v___x_3300_,
                        v___x_3303_,
                        v_config_3138_,
                        v___x_3304_,
                    );
                    crate::leanh::lean_inc(v_a_3140_);
                    crate::leanh::lean_inc_ref(v_a_3139_);
                    v___x_3306_ = crate::leanh::lean_apply_3(
                        v___x_4268__overap_3305_,
                        v_a_3139_,
                        v_a_3140_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3306_;
                } else {
                    v___x_3307_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3308_ = l_Lean_Syntax_getArg(v_config_3138_, v___x_3307_);
                    crate::leanh::lean_inc(v___x_3308_);
                    v___x_3309_ = l_Lean_Syntax_matchesNull(v___x_3308_, v___x_3307_);
                    if v___x_3309_ == 0 {
                        v___x_3310_ = crate::leanh::lean_unsigned_to_nat(1);
                        crate::leanh::lean_inc(v___x_3308_);
                        v___x_3311_ = l_Lean_Syntax_matchesNull(v___x_3308_, v___x_3310_);
                        if v___x_3311_ == 0 {
                            crate::leanh::lean_dec(v___x_3308_);
                            crate::leanh::lean_dec(v_ty_3137_);
                            crate::leanh::lean_dec(v_id_3136_);
                            crate::leanh::lean_dec(v_tyName_3134_);
                            v___x_3312_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__13),
                                core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__13_once),
                                _init_l_Lake_DSL_elabConfig___closed__13,
                            );
                            v___x_3313_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__15),
                                core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__15_once),
                                _init_l_Lake_DSL_elabConfig___closed__15,
                            );
                            v___x_4683__overap_3314_ = l_Lean_throwErrorAt___redArg(
                                v___x_3300_,
                                v___x_3312_,
                                v_config_3138_,
                                v___x_3313_,
                            );
                            crate::leanh::lean_inc(v_a_3140_);
                            crate::leanh::lean_inc_ref(v_a_3139_);
                            v___x_3315_ = crate::leanh::lean_apply_3(
                                v___x_4683__overap_3314_,
                                v_a_3139_,
                                v_a_3140_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_3315_;
                        } else {
                            v___x_3316_ = l_Lean_Syntax_getArg(v___x_3308_, v___x_3307_);
                            crate::leanh::lean_dec(v___x_3308_);
                            v___x_3317_ = l_Lake_DSL_declValWhere___closed__1;
                            crate::leanh::lean_inc(v___x_3316_);
                            v___x_3318_ = l_Lean_Syntax_isOfKind(v___x_3316_, v___x_3317_);
                            if v___x_3318_ == 0 {
                                v___x_3319_ = l_Lake_DSL_declValStruct___closed__1;
                                crate::leanh::lean_inc(v___x_3316_);
                                v___x_3320_ = l_Lean_Syntax_isOfKind(v___x_3316_, v___x_3319_);
                                if v___x_3320_ == 0 {
                                    crate::leanh::lean_dec(v___x_3316_);
                                    crate::leanh::lean_dec(v_ty_3137_);
                                    crate::leanh::lean_dec(v_id_3136_);
                                    crate::leanh::lean_dec(v_tyName_3134_);
                                    v___x_3321_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__13),
                                        core::ptr::addr_of_mut!(
                                            l_Lake_DSL_elabConfig___closed__13_once
                                        ),
                                        _init_l_Lake_DSL_elabConfig___closed__13,
                                    );
                                    v___x_3322_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__15),
                                        core::ptr::addr_of_mut!(
                                            l_Lake_DSL_elabConfig___closed__15_once
                                        ),
                                        _init_l_Lake_DSL_elabConfig___closed__15,
                                    );
                                    v___x_4981__overap_3323_ = l_Lean_throwErrorAt___redArg(
                                        v___x_3300_,
                                        v___x_3321_,
                                        v_config_3138_,
                                        v___x_3322_,
                                    );
                                    crate::leanh::lean_inc(v_a_3140_);
                                    crate::leanh::lean_inc_ref(v_a_3139_);
                                    v___x_3324_ = crate::leanh::lean_apply_3(
                                        v___x_4981__overap_3323_,
                                        v_a_3139_,
                                        v_a_3140_,
                                        crate::leanh::lean_box(0),
                                    );
                                    return v___x_3324_;
                                } else {
                                    v___x_3325_ = l_Lean_Syntax_getArg(v___x_3316_, v___x_3307_);
                                    v___x_3326_ = l_Lake_DSL_structVal___closed__1;
                                    crate::leanh::lean_inc(v___x_3325_);
                                    v___x_3327_ = l_Lean_Syntax_isOfKind(v___x_3325_, v___x_3326_);
                                    if v___x_3327_ == 0 {
                                        crate::leanh::lean_dec(v___x_3325_);
                                        crate::leanh::lean_dec(v___x_3316_);
                                        crate::leanh::lean_dec(v_ty_3137_);
                                        crate::leanh::lean_dec(v_id_3136_);
                                        crate::leanh::lean_dec(v_tyName_3134_);
                                        v___x_3328_ = crate::leanh::lean_obj_once(
                                            core::ptr::addr_of_mut!(
                                                l_Lake_DSL_elabConfig___closed__13
                                            ),
                                            core::ptr::addr_of_mut!(
                                                l_Lake_DSL_elabConfig___closed__13_once
                                            ),
                                            _init_l_Lake_DSL_elabConfig___closed__13,
                                        );
                                        v___x_3329_ = crate::leanh::lean_obj_once(
                                            core::ptr::addr_of_mut!(
                                                l_Lake_DSL_elabConfig___closed__15
                                            ),
                                            core::ptr::addr_of_mut!(
                                                l_Lake_DSL_elabConfig___closed__15_once
                                            ),
                                            _init_l_Lake_DSL_elabConfig___closed__15,
                                        );
                                        v___x_5079__overap_3330_ = l_Lean_throwErrorAt___redArg(
                                            v___x_3300_,
                                            v___x_3328_,
                                            v_config_3138_,
                                            v___x_3329_,
                                        );
                                        crate::leanh::lean_inc(v_a_3140_);
                                        crate::leanh::lean_inc_ref(v_a_3139_);
                                        v___x_3331_ = crate::leanh::lean_apply_3(
                                            v___x_5079__overap_3330_,
                                            v_a_3139_,
                                            v_a_3140_,
                                            crate::leanh::lean_box(0),
                                        );
                                        return v___x_3331_;
                                    } else {
                                        v___x_3332_ =
                                            l_Lean_Syntax_getArg(v___x_3325_, v___x_3310_);
                                        v___x_3333_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0;
                                        crate::leanh::lean_inc(v___x_3332_);
                                        v___x_3334_ =
                                            l_Lean_Syntax_isOfKind(v___x_3332_, v___x_3333_);
                                        if v___x_3334_ == 0 {
                                            crate::leanh::lean_dec(v___x_3332_);
                                            crate::leanh::lean_dec(v___x_3325_);
                                            crate::leanh::lean_dec(v___x_3316_);
                                            crate::leanh::lean_dec(v_ty_3137_);
                                            crate::leanh::lean_dec(v_id_3136_);
                                            crate::leanh::lean_dec(v_tyName_3134_);
                                            v___x_3335_ = crate::leanh::lean_obj_once(
                                                core::ptr::addr_of_mut!(
                                                    l_Lake_DSL_elabConfig___closed__13
                                                ),
                                                core::ptr::addr_of_mut!(
                                                    l_Lake_DSL_elabConfig___closed__13_once
                                                ),
                                                _init_l_Lake_DSL_elabConfig___closed__13,
                                            );
                                            v___x_3336_ = crate::leanh::lean_obj_once(
                                                core::ptr::addr_of_mut!(
                                                    l_Lake_DSL_elabConfig___closed__15
                                                ),
                                                core::ptr::addr_of_mut!(
                                                    l_Lake_DSL_elabConfig___closed__15_once
                                                ),
                                                _init_l_Lake_DSL_elabConfig___closed__15,
                                            );
                                            v___x_5164__overap_3337_ = l_Lean_throwErrorAt___redArg(
                                                v___x_3300_,
                                                v___x_3335_,
                                                v_config_3138_,
                                                v___x_3336_,
                                            );
                                            crate::leanh::lean_inc(v_a_3140_);
                                            crate::leanh::lean_inc_ref(v_a_3139_);
                                            v___x_3338_ = crate::leanh::lean_apply_3(
                                                v___x_5164__overap_3337_,
                                                v_a_3139_,
                                                v_a_3140_,
                                                crate::leanh::lean_box(0),
                                            );
                                            return v___x_3338_;
                                        } else {
                                            v_tk_3339_ =
                                                l_Lean_Syntax_getArg(v___x_3325_, v___x_3307_);
                                            crate::leanh::lean_dec(v___x_3325_);
                                            v___x_3340_ =
                                                l_Lean_Syntax_getArg(v___x_3332_, v___x_3307_);
                                            crate::leanh::lean_dec(v___x_3332_);
                                            v___x_3348_ =
                                                l_Lean_Syntax_getArg(v___x_3316_, v___x_3310_);
                                            crate::leanh::lean_dec(v___x_3316_);
                                            v___x_3349_ = l_Lean_Syntax_isNone(v___x_3348_);
                                            if v___x_3349_ == 0 {
                                                crate::leanh::lean_inc(v___x_3348_);
                                                v___x_3350_ = l_Lean_Syntax_matchesNull(
                                                    v___x_3348_,
                                                    v___x_3310_,
                                                );
                                                if v___x_3350_ == 0 {
                                                    crate::leanh::lean_dec(v___x_3348_);
                                                    crate::leanh::lean_dec(v___x_3340_);
                                                    crate::leanh::lean_dec(v_tk_3339_);
                                                    crate::leanh::lean_dec(v_ty_3137_);
                                                    crate::leanh::lean_dec(v_id_3136_);
                                                    crate::leanh::lean_dec(v_tyName_3134_);
                                                    v___x_3351_ = crate::leanh::lean_obj_once(
                                                        core::ptr::addr_of_mut!(
                                                            l_Lake_DSL_elabConfig___closed__13
                                                        ),
                                                        core::ptr::addr_of_mut!(
                                                            l_Lake_DSL_elabConfig___closed__13_once
                                                        ),
                                                        _init_l_Lake_DSL_elabConfig___closed__13,
                                                    );
                                                    v___x_3352_ = crate::leanh::lean_obj_once(
                                                        core::ptr::addr_of_mut!(
                                                            l_Lake_DSL_elabConfig___closed__15
                                                        ),
                                                        core::ptr::addr_of_mut!(
                                                            l_Lake_DSL_elabConfig___closed__15_once
                                                        ),
                                                        _init_l_Lake_DSL_elabConfig___closed__15,
                                                    );
                                                    v___x_5273__overap_3353_ =
                                                        l_Lean_throwErrorAt___redArg(
                                                            v___x_3300_,
                                                            v___x_3351_,
                                                            v_config_3138_,
                                                            v___x_3352_,
                                                        );
                                                    crate::leanh::lean_inc(v_a_3140_);
                                                    crate::leanh::lean_inc_ref(v_a_3139_);
                                                    v___x_3354_ = crate::leanh::lean_apply_3(
                                                        v___x_5273__overap_3353_,
                                                        v_a_3139_,
                                                        v_a_3140_,
                                                        crate::leanh::lean_box(0),
                                                    );
                                                    return v___x_3354_;
                                                } else {
                                                    v_wds_x3f_3355_ = l_Lean_Syntax_getArg(
                                                        v___x_3348_,
                                                        v___x_3307_,
                                                    );
                                                    crate::leanh::lean_dec(v___x_3348_);
                                                    v___x_3356_ = l_Lake_DSL_declValDo___closed__12;
                                                    crate::leanh::lean_inc(v_wds_x3f_3355_);
                                                    v___x_3357_ = l_Lean_Syntax_isOfKind(
                                                        v_wds_x3f_3355_,
                                                        v___x_3356_,
                                                    );
                                                    if v___x_3357_ == 0 {
                                                        crate::leanh::lean_dec(v_wds_x3f_3355_);
                                                        crate::leanh::lean_dec(v___x_3340_);
                                                        crate::leanh::lean_dec(v_tk_3339_);
                                                        crate::leanh::lean_dec(v_ty_3137_);
                                                        crate::leanh::lean_dec(v_id_3136_);
                                                        crate::leanh::lean_dec(v_tyName_3134_);
                                                        v___x_3358_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__13), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__13_once), _init_l_Lake_DSL_elabConfig___closed__13);
                                                        v___x_3359_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__15), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__15_once), _init_l_Lake_DSL_elabConfig___closed__15);
                                                        v___x_5310__overap_3360_ =
                                                            l_Lean_throwErrorAt___redArg(
                                                                v___x_3300_,
                                                                v___x_3358_,
                                                                v_config_3138_,
                                                                v___x_3359_,
                                                            );
                                                        crate::leanh::lean_inc(v_a_3140_);
                                                        crate::leanh::lean_inc_ref(v_a_3139_);
                                                        v___x_3361_ = crate::leanh::lean_apply_3(
                                                            v___x_5310__overap_3360_,
                                                            v_a_3139_,
                                                            v_a_3140_,
                                                            crate::leanh::lean_box(0),
                                                        );
                                                        return v___x_3361_;
                                                    } else {
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_3300_,
                                                            2,
                                                        );
                                                        v___x_3362_ = crate::leanh::lean_alloc_ctor(
                                                            1,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_3362_,
                                                            0,
                                                            v_wds_x3f_3355_,
                                                        );
                                                        v_wds_x3f_3342_ = v___x_3362_;
                                                        v___y_3343_ = v_a_3139_;
                                                        v___y_3344_ = v_a_3140_;
                                                        state = 14;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v___x_3348_);
                                                crate::leanh::lean_dec_ref_known(v___x_3300_, 2);
                                                v___x_3363_ = crate::leanh::lean_box(0);
                                                v_wds_x3f_3342_ = v___x_3363_;
                                                v___y_3343_ = v_a_3139_;
                                                v___y_3344_ = v_a_3140_;
                                                state = 14;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                v___x_3364_ = l_Lean_Syntax_getArg(v___x_3316_, v___x_3310_);
                                v___x_3365_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0;
                                crate::leanh::lean_inc(v___x_3364_);
                                v___x_3366_ = l_Lean_Syntax_isOfKind(v___x_3364_, v___x_3365_);
                                if v___x_3366_ == 0 {
                                    crate::leanh::lean_dec(v___x_3364_);
                                    crate::leanh::lean_dec(v___x_3316_);
                                    crate::leanh::lean_dec(v_ty_3137_);
                                    crate::leanh::lean_dec(v_id_3136_);
                                    crate::leanh::lean_dec(v_tyName_3134_);
                                    v___x_3367_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__13),
                                        core::ptr::addr_of_mut!(
                                            l_Lake_DSL_elabConfig___closed__13_once
                                        ),
                                        _init_l_Lake_DSL_elabConfig___closed__13,
                                    );
                                    v___x_3368_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__15),
                                        core::ptr::addr_of_mut!(
                                            l_Lake_DSL_elabConfig___closed__15_once
                                        ),
                                        _init_l_Lake_DSL_elabConfig___closed__15,
                                    );
                                    v___x_5406__overap_3369_ = l_Lean_throwErrorAt___redArg(
                                        v___x_3300_,
                                        v___x_3367_,
                                        v_config_3138_,
                                        v___x_3368_,
                                    );
                                    crate::leanh::lean_inc(v_a_3140_);
                                    crate::leanh::lean_inc_ref(v_a_3139_);
                                    v___x_3370_ = crate::leanh::lean_apply_3(
                                        v___x_5406__overap_3369_,
                                        v_a_3139_,
                                        v_a_3140_,
                                        crate::leanh::lean_box(0),
                                    );
                                    return v___x_3370_;
                                } else {
                                    v_tk_3371_ = l_Lean_Syntax_getArg(v___x_3316_, v___x_3307_);
                                    v___x_3372_ = l_Lean_Syntax_getArg(v___x_3364_, v___x_3307_);
                                    crate::leanh::lean_dec(v___x_3364_);
                                    v___x_3380_ = crate::leanh::lean_unsigned_to_nat(2);
                                    v___x_3381_ = l_Lean_Syntax_getArg(v___x_3316_, v___x_3380_);
                                    crate::leanh::lean_dec(v___x_3316_);
                                    v___x_3382_ = l_Lean_Syntax_isNone(v___x_3381_);
                                    if v___x_3382_ == 0 {
                                        crate::leanh::lean_inc(v___x_3381_);
                                        v___x_3383_ =
                                            l_Lean_Syntax_matchesNull(v___x_3381_, v___x_3310_);
                                        if v___x_3383_ == 0 {
                                            crate::leanh::lean_dec(v___x_3381_);
                                            crate::leanh::lean_dec(v___x_3372_);
                                            crate::leanh::lean_dec(v_tk_3371_);
                                            crate::leanh::lean_dec(v_ty_3137_);
                                            crate::leanh::lean_dec(v_id_3136_);
                                            crate::leanh::lean_dec(v_tyName_3134_);
                                            v___x_3384_ = crate::leanh::lean_obj_once(
                                                core::ptr::addr_of_mut!(
                                                    l_Lake_DSL_elabConfig___closed__13
                                                ),
                                                core::ptr::addr_of_mut!(
                                                    l_Lake_DSL_elabConfig___closed__13_once
                                                ),
                                                _init_l_Lake_DSL_elabConfig___closed__13,
                                            );
                                            v___x_3385_ = crate::leanh::lean_obj_once(
                                                core::ptr::addr_of_mut!(
                                                    l_Lake_DSL_elabConfig___closed__15
                                                ),
                                                core::ptr::addr_of_mut!(
                                                    l_Lake_DSL_elabConfig___closed__15_once
                                                ),
                                                _init_l_Lake_DSL_elabConfig___closed__15,
                                            );
                                            v___x_5516__overap_3386_ = l_Lean_throwErrorAt___redArg(
                                                v___x_3300_,
                                                v___x_3384_,
                                                v_config_3138_,
                                                v___x_3385_,
                                            );
                                            crate::leanh::lean_inc(v_a_3140_);
                                            crate::leanh::lean_inc_ref(v_a_3139_);
                                            v___x_3387_ = crate::leanh::lean_apply_3(
                                                v___x_5516__overap_3386_,
                                                v_a_3139_,
                                                v_a_3140_,
                                                crate::leanh::lean_box(0),
                                            );
                                            return v___x_3387_;
                                        } else {
                                            v_wds_x3f_3388_ =
                                                l_Lean_Syntax_getArg(v___x_3381_, v___x_3307_);
                                            crate::leanh::lean_dec(v___x_3381_);
                                            v___x_3389_ = l_Lake_DSL_declValDo___closed__12;
                                            crate::leanh::lean_inc(v_wds_x3f_3388_);
                                            v___x_3390_ = l_Lean_Syntax_isOfKind(
                                                v_wds_x3f_3388_,
                                                v___x_3389_,
                                            );
                                            if v___x_3390_ == 0 {
                                                crate::leanh::lean_dec(v_wds_x3f_3388_);
                                                crate::leanh::lean_dec(v___x_3372_);
                                                crate::leanh::lean_dec(v_tk_3371_);
                                                crate::leanh::lean_dec(v_ty_3137_);
                                                crate::leanh::lean_dec(v_id_3136_);
                                                crate::leanh::lean_dec(v_tyName_3134_);
                                                v___x_3391_ = crate::leanh::lean_obj_once(
                                                    core::ptr::addr_of_mut!(
                                                        l_Lake_DSL_elabConfig___closed__13
                                                    ),
                                                    core::ptr::addr_of_mut!(
                                                        l_Lake_DSL_elabConfig___closed__13_once
                                                    ),
                                                    _init_l_Lake_DSL_elabConfig___closed__13,
                                                );
                                                v___x_3392_ = crate::leanh::lean_obj_once(
                                                    core::ptr::addr_of_mut!(
                                                        l_Lake_DSL_elabConfig___closed__15
                                                    ),
                                                    core::ptr::addr_of_mut!(
                                                        l_Lake_DSL_elabConfig___closed__15_once
                                                    ),
                                                    _init_l_Lake_DSL_elabConfig___closed__15,
                                                );
                                                v___x_5553__overap_3393_ =
                                                    l_Lean_throwErrorAt___redArg(
                                                        v___x_3300_,
                                                        v___x_3391_,
                                                        v_config_3138_,
                                                        v___x_3392_,
                                                    );
                                                crate::leanh::lean_inc(v_a_3140_);
                                                crate::leanh::lean_inc_ref(v_a_3139_);
                                                v___x_3394_ = crate::leanh::lean_apply_3(
                                                    v___x_5553__overap_3393_,
                                                    v_a_3139_,
                                                    v_a_3140_,
                                                    crate::leanh::lean_box(0),
                                                );
                                                return v___x_3394_;
                                            } else {
                                                crate::leanh::lean_dec_ref_known(v___x_3300_, 2);
                                                v___x_3395_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3395_,
                                                    0,
                                                    v_wds_x3f_3388_,
                                                );
                                                v_wds_x3f_3374_ = v___x_3395_;
                                                v___y_3375_ = v_a_3139_;
                                                v___y_3376_ = v_a_3140_;
                                                state = 15;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v___x_3381_);
                                        crate::leanh::lean_dec_ref_known(v___x_3300_, 2);
                                        v___x_3396_ = crate::leanh::lean_box(0);
                                        v_wds_x3f_3374_ = v___x_3396_;
                                        v___y_3375_ = v_a_3139_;
                                        v___y_3376_ = v_a_3140_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3308_);
                        crate::leanh::lean_dec_ref_known(v___x_3300_, 2);
                        v___x_3397_ = crate::leanh::lean_box(2);
                        v___x_3398_ = l_Lake_DSL_expandAttrs___closed__5;
                        v___x_3399_ = crate::leanh::lean_box(0);
                        v_whereInfo_3254_ = v___x_3397_;
                        v_fs_3255_ = v___x_3398_;
                        v_wds_x3f_3256_ = v___x_3399_;
                        v___y_3257_ = v_a_3139_;
                        v___y_3258_ = v_a_3140_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3151_ = l_Lake_DSL_elabConfig___closed__0;
                crate::leanh::lean_inc_ref_n(v___y_3148_, 5);
                crate::leanh::lean_inc_ref_n(v___y_3143_, 6);
                crate::leanh::lean_inc_ref_n(v___y_3150_, 6);
                v___x_3152_ =
                    l_Lean_Name_mkStr4(v___y_3150_, v___y_3143_, v___y_3148_, v___x_3151_);
                v___x_3153_ = l_Lake_DSL_elabConfig___closed__1;
                v___x_3154_ =
                    l_Lean_Name_mkStr4(v___y_3150_, v___y_3143_, v___y_3148_, v___x_3153_);
                v___x_3155_ = l_Lake_DSL_expandOptSimpleBinder___closed__28;
                v___x_3156_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5_once), _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5);
                crate::leanh::lean_inc_n(v___y_3147_, 8);
                v___x_3157_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3157_, 0, v___y_3147_);
                crate::leanh::lean_ctor_set(v___x_3157_, 1, v___x_3155_);
                crate::leanh::lean_ctor_set(v___x_3157_, 2, v___x_3156_);
                crate::leanh::lean_inc_ref_n(v___x_3157_, 8);
                v___x_3158_ = l_Lean_Syntax_node7(
                    v___y_3147_,
                    v___x_3154_,
                    v___x_3157_,
                    v___x_3157_,
                    v___x_3157_,
                    v___x_3157_,
                    v___x_3157_,
                    v___x_3157_,
                    v___x_3157_,
                );
                v___x_3159_ = l_Lake_DSL_elabConfig___closed__2;
                v___x_3160_ =
                    l_Lean_Name_mkStr4(v___y_3150_, v___y_3143_, v___y_3148_, v___x_3159_);
                v___x_3161_ = l_Lake_DSL_elabConfig___closed__3;
                v___x_3162_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3162_, 0, v___y_3147_);
                crate::leanh::lean_ctor_set(v___x_3162_, 1, v___x_3161_);
                v___x_3163_ = l_Lake_DSL_elabConfig___closed__4;
                v___x_3164_ =
                    l_Lean_Name_mkStr4(v___y_3150_, v___y_3143_, v___y_3148_, v___x_3163_);
                v___x_3165_ = l_Lake_DSL_expandAttrs___closed__5;
                crate::leanh::lean_inc_n(v___y_3146_, 2);
                v___x_3166_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3166_, 0, v___y_3146_);
                crate::leanh::lean_ctor_set(v___x_3166_, 1, v___x_3155_);
                crate::leanh::lean_ctor_set(v___x_3166_, 2, v___x_3165_);
                v___x_3167_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3168_ = lean_mk_empty_array_with_capacity(v___x_3167_);
                v___x_3169_ = lean_array_push(v___x_3168_, v_id_3136_);
                v___x_3170_ = lean_array_push(v___x_3169_, v___x_3166_);
                v___x_3171_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3171_, 0, v___y_3146_);
                crate::leanh::lean_ctor_set(v___x_3171_, 1, v___x_3164_);
                crate::leanh::lean_ctor_set(v___x_3171_, 2, v___x_3170_);
                v___x_3172_ = l_Lake_DSL_elabConfig___closed__5;
                v___x_3173_ =
                    l_Lean_Name_mkStr4(v___y_3150_, v___y_3143_, v___y_3148_, v___x_3172_);
                v___x_3174_ = l_Lake_DSL_expandAttrs___closed__2;
                v___x_3175_ = l_Lake_DSL_simpleDeclSig___closed__2;
                v___x_3176_ =
                    l_Lean_Name_mkStr4(v___y_3150_, v___y_3143_, v___x_3174_, v___x_3175_);
                v___x_3177_ = l_Lake_DSL_expandOptSimpleBinder___closed__26;
                v___x_3178_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3178_, 0, v___y_3147_);
                crate::leanh::lean_ctor_set(v___x_3178_, 1, v___x_3177_);
                v___x_3179_ =
                    l_Lean_Syntax_node2(v___y_3147_, v___x_3176_, v___x_3178_, v_ty_3137_);
                v___x_3180_ = l_Lean_Syntax_node1(v___y_3147_, v___x_3155_, v___x_3179_);
                v___x_3181_ =
                    l_Lean_Syntax_node2(v___y_3147_, v___x_3173_, v___x_3157_, v___x_3180_);
                v___x_3182_ = l_Lean_Syntax_node5(
                    v___y_3147_,
                    v___x_3160_,
                    v___x_3162_,
                    v___x_3171_,
                    v___x_3181_,
                    v___y_3149_,
                    v___x_3157_,
                );
                v___x_3183_ =
                    l_Lean_Syntax_node2(v___y_3147_, v___x_3152_, v___x_3158_, v___x_3182_);
                crate::leanh::lean_inc(v___x_3183_);
                v___x_3184_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Command_elabCommand___boxed as *mut core::ffi::c_void,
                    4,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_3184_, 0, v___x_3183_);
                v___x_3185_ = l_Lean_Elab_Command_withMacroExpansion___redArg(
                    v_config_3138_,
                    v___x_3183_,
                    v___x_3184_,
                    v___y_3145_,
                    v___y_3144_,
                );
                return v___x_3185_;
            }
            2 => {
                v___x_3196_ = l_Lean_Elab_Command_getRef___redArg(v___y_3190_);
                if crate::leanh::lean_obj_tag(v___x_3196_) == 0 {
                    v_a_3197_ = crate::leanh::lean_ctor_get(v___x_3196_, 0);
                    crate::leanh::lean_inc(v_a_3197_);
                    crate::leanh::lean_dec_ref_known(v___x_3196_, 1);
                    v___x_3198_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3190_);
                    if crate::leanh::lean_obj_tag(v___x_3198_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3198_, 1);
                        v___x_3199_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___closed__7_once),
                            _init_l_Lake_DSL_elabConfig___closed__7,
                        );
                        v_toApplicative_3200_ = crate::leanh::lean_ctor_get(v___x_3199_, 0);
                        v_toFunctor_3201_ = crate::leanh::lean_ctor_get(v_toApplicative_3200_, 0);
                        v_toSeq_3202_ = crate::leanh::lean_ctor_get(v_toApplicative_3200_, 2);
                        v_toSeqLeft_3203_ = crate::leanh::lean_ctor_get(v_toApplicative_3200_, 3);
                        v_toSeqRight_3204_ = crate::leanh::lean_ctor_get(v_toApplicative_3200_, 4);
                        v___f_3205_ = l_Lake_DSL_elabConfig___closed__8;
                        v___f_3206_ = l_Lake_DSL_elabConfig___closed__9;
                        crate::leanh::lean_inc_ref_n(v_toFunctor_3201_, 2);
                        v___f_3207_ = crate::leanh::lean_alloc_closure(
                            l_ReaderT_instFunctorOfMonad___redArg___lam__0
                                as *mut core::ffi::c_void,
                            6,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_3207_, 0, v_toFunctor_3201_);
                        v___f_3208_ = crate::leanh::lean_alloc_closure(
                            l_ReaderT_instFunctorOfMonad___redArg___lam__1
                                as *mut core::ffi::c_void,
                            6,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_3208_, 0, v_toFunctor_3201_);
                        v___x_3209_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3209_, 0, v___f_3207_);
                        crate::leanh::lean_ctor_set(v___x_3209_, 1, v___f_3208_);
                        crate::leanh::lean_inc(v_toSeqRight_3204_);
                        v___f_3210_ = crate::leanh::lean_alloc_closure(
                            l_ReaderT_instApplicativeOfMonad___redArg___lam__1
                                as *mut core::ffi::c_void,
                            6,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_3210_, 0, v_toSeqRight_3204_);
                        crate::leanh::lean_inc(v_toSeqLeft_3203_);
                        v___f_3211_ = crate::leanh::lean_alloc_closure(
                            l_ReaderT_instApplicativeOfMonad___redArg___lam__3
                                as *mut core::ffi::c_void,
                            6,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_3211_, 0, v_toSeqLeft_3203_);
                        crate::leanh::lean_inc(v_toSeq_3202_);
                        v___f_3212_ = crate::leanh::lean_alloc_closure(
                            l_ReaderT_instApplicativeOfMonad___redArg___lam__4
                                as *mut core::ffi::c_void,
                            6,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_3212_, 0, v_toSeq_3202_);
                        v___x_3213_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3213_, 0, v___x_3209_);
                        crate::leanh::lean_ctor_set(v___x_3213_, 1, v___f_3205_);
                        crate::leanh::lean_ctor_set(v___x_3213_, 2, v___f_3212_);
                        crate::leanh::lean_ctor_set(v___x_3213_, 3, v___f_3211_);
                        crate::leanh::lean_ctor_set(v___x_3213_, 4, v___f_3210_);
                        v___x_3214_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3214_, 0, v___x_3213_);
                        crate::leanh::lean_ctor_set(v___x_3214_, 1, v___f_3206_);
                        v___x_3215_ = l_Lean_Elab_Command_instMonadEnvCommandElabM;
                        v_quotContext_x3f_3216_ = crate::leanh::lean_ctor_get(v___y_3190_, 5);
                        v___x_3217_ = l_Lean_mkOptionalNode(v___y_3195_);
                        v___x_3218_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_3219_ = lean_mk_empty_array_with_capacity(v___x_3218_);
                        v___x_3220_ = lean_array_push(v___x_3219_, v___y_3189_);
                        v___x_3221_ = lean_array_push(v___x_3220_, v___y_3194_);
                        v___x_3222_ = lean_array_push(v___x_3221_, v___x_3217_);
                        v___x_3223_ = crate::leanh::lean_box(2);
                        crate::leanh::lean_inc(v___y_3191_);
                        v___x_3224_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3224_, 0, v___x_3223_);
                        crate::leanh::lean_ctor_set(v___x_3224_, 1, v___y_3191_);
                        crate::leanh::lean_ctor_set(v___x_3224_, 2, v___x_3222_);
                        v___x_3225_ = 0;
                        v___x_3226_ = l_Lean_SourceInfo_fromRef(v_a_3197_, v___x_3225_);
                        crate::leanh::lean_dec(v_a_3197_);
                        if crate::leanh::lean_obj_tag(v_quotContext_x3f_3216_) == 0 {
                            v___x_4252__overap_3227_ =
                                l_Lean_getMainModule___redArg(v___x_3214_, v___x_3215_);
                            crate::leanh::lean_inc(v___y_3188_);
                            crate::leanh::lean_inc_ref(v___y_3190_);
                            v___x_3228_ = crate::leanh::lean_apply_3(
                                v___x_4252__overap_3227_,
                                v___y_3190_,
                                v___y_3188_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_3228_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3228_, 1);
                                v___y_3143_ = v___y_3187_;
                                v___y_3144_ = v___y_3188_;
                                v___y_3145_ = v___y_3190_;
                                v___y_3146_ = v___x_3223_;
                                v___y_3147_ = v___x_3226_;
                                v___y_3148_ = v___y_3192_;
                                v___y_3149_ = v___x_3224_;
                                v___y_3150_ = v___y_3193_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3226_);
                                crate::leanh::lean_dec_ref_known(v___x_3224_, 3);
                                crate::leanh::lean_dec(v_config_3138_);
                                crate::leanh::lean_dec(v_ty_3137_);
                                crate::leanh::lean_dec(v_id_3136_);
                                v_a_3229_ = crate::leanh::lean_ctor_get(v___x_3228_, 0);
                                v_isSharedCheck_3236_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3228_)) as u8;
                                if v_isSharedCheck_3236_ == 0 {
                                    v___x_3231_ = v___x_3228_;
                                    v_isShared_3232_ = v_isSharedCheck_3236_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3229_);
                                    crate::leanh::lean_dec(v___x_3228_);
                                    v___x_3231_ = crate::leanh::lean_box(0);
                                    v_isShared_3232_ = v_isSharedCheck_3236_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_3214_, 2);
                            v___y_3143_ = v___y_3187_;
                            v___y_3144_ = v___y_3188_;
                            v___y_3145_ = v___y_3190_;
                            v___y_3146_ = v___x_3223_;
                            v___y_3147_ = v___x_3226_;
                            v___y_3148_ = v___y_3192_;
                            v___y_3149_ = v___x_3224_;
                            v___y_3150_ = v___y_3193_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3197_);
                        crate::leanh::lean_dec(v___y_3195_);
                        crate::leanh::lean_dec(v___y_3194_);
                        crate::leanh::lean_dec(v___y_3189_);
                        crate::leanh::lean_dec(v_config_3138_);
                        crate::leanh::lean_dec(v_ty_3137_);
                        crate::leanh::lean_dec(v_id_3136_);
                        v_a_3237_ = crate::leanh::lean_ctor_get(v___x_3198_, 0);
                        v_isSharedCheck_3244_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3198_)) as u8;
                        if v_isSharedCheck_3244_ == 0 {
                            v___x_3239_ = v___x_3198_;
                            v_isShared_3240_ = v_isSharedCheck_3244_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3237_);
                            crate::leanh::lean_dec(v___x_3198_);
                            v___x_3239_ = crate::leanh::lean_box(0);
                            v_isShared_3240_ = v_isSharedCheck_3244_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3195_);
                    crate::leanh::lean_dec(v___y_3194_);
                    crate::leanh::lean_dec(v___y_3189_);
                    crate::leanh::lean_dec(v_config_3138_);
                    crate::leanh::lean_dec(v_ty_3137_);
                    crate::leanh::lean_dec(v_id_3136_);
                    v_a_3245_ = crate::leanh::lean_ctor_get(v___x_3196_, 0);
                    v_isSharedCheck_3252_ = (!crate::leanh::lean_is_exclusive(v___x_3196_)) as u8;
                    if v_isSharedCheck_3252_ == 0 {
                        v___x_3247_ = v___x_3196_;
                        v_isShared_3248_ = v_isSharedCheck_3252_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3245_);
                        crate::leanh::lean_dec(v___x_3196_);
                        v___x_3247_ = crate::leanh::lean_box(0);
                        v_isShared_3248_ = v_isSharedCheck_3252_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3232_ == 0 {
                    v___x_3234_ = v___x_3231_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3235_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3229_);
                    v___x_3234_ = v_reuseFailAlloc_3235_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3234_;
            }
            5 => {
                if v_isShared_3240_ == 0 {
                    v___x_3242_ = v___x_3239_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3243_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
                    v___x_3242_ = v_reuseFailAlloc_3243_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3242_;
            }
            7 => {
                if v_isShared_3248_ == 0 {
                    v___x_3250_ = v___x_3247_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3251_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
                    v___x_3250_ = v_reuseFailAlloc_3251_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3250_;
            }
            9 => {
                v_fieldMap_3259_ = crate::leanh::lean_ctor_get(v_info_3135_, 1);
                v___x_3260_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(
                    v_tyName_3134_,
                    v_fieldMap_3259_,
                    v_fs_3255_,
                    v___y_3257_,
                    v___y_3258_,
                );
                crate::leanh::lean_dec_ref(v_fs_3255_);
                if crate::leanh::lean_obj_tag(v___x_3260_) == 0 {
                    v_a_3261_ = crate::leanh::lean_ctor_get(v___x_3260_, 0);
                    crate::leanh::lean_inc(v_a_3261_);
                    crate::leanh::lean_dec_ref_known(v___x_3260_, 1);
                    v___x_3262_ = l_Lake_DSL_elabConfig___closed__10;
                    v_whereTk_3263_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_whereTk_3263_, 0, v_whereInfo_3254_);
                    crate::leanh::lean_ctor_set(v_whereTk_3263_, 1, v___x_3262_);
                    v___x_3264_ = l_Lake_DSL_expandAttrs___closed__0;
                    v___x_3265_ = l_Lake_DSL_expandAttrs___closed__1;
                    v___x_3266_ = l_Lake_DSL_simpleDeclSig___closed__6;
                    v___x_3267_ = l_Lake_DSL_elabConfig___closed__12;
                    if crate::leanh::lean_obj_tag(v_wds_x3f_3256_) == 0 {
                        v___x_3268_ = crate::leanh::lean_box(0);
                        v___y_3187_ = v___x_3265_;
                        v___y_3188_ = v___y_3258_;
                        v___y_3189_ = v_whereTk_3263_;
                        v___y_3190_ = v___y_3257_;
                        v___y_3191_ = v___x_3267_;
                        v___y_3192_ = v___x_3266_;
                        v___y_3193_ = v___x_3264_;
                        v___y_3194_ = v_a_3261_;
                        v___y_3195_ = v___x_3268_;
                        state = 2;
                        continue;
                    } else {
                        v_val_3269_ = crate::leanh::lean_ctor_get(v_wds_x3f_3256_, 0);
                        v_isSharedCheck_3276_ =
                            (!crate::leanh::lean_is_exclusive(v_wds_x3f_3256_)) as u8;
                        if v_isSharedCheck_3276_ == 0 {
                            v___x_3271_ = v_wds_x3f_3256_;
                            v_isShared_3272_ = v_isSharedCheck_3276_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3269_);
                            crate::leanh::lean_dec(v_wds_x3f_3256_);
                            v___x_3271_ = crate::leanh::lean_box(0);
                            v_isShared_3272_ = v_isSharedCheck_3276_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_wds_x3f_3256_);
                    crate::leanh::lean_dec(v_whereInfo_3254_);
                    crate::leanh::lean_dec(v_config_3138_);
                    crate::leanh::lean_dec(v_ty_3137_);
                    crate::leanh::lean_dec(v_id_3136_);
                    v_a_3277_ = crate::leanh::lean_ctor_get(v___x_3260_, 0);
                    v_isSharedCheck_3284_ = (!crate::leanh::lean_is_exclusive(v___x_3260_)) as u8;
                    if v_isSharedCheck_3284_ == 0 {
                        v___x_3279_ = v___x_3260_;
                        v_isShared_3280_ = v_isSharedCheck_3284_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3277_);
                        crate::leanh::lean_dec(v___x_3260_);
                        v___x_3279_ = crate::leanh::lean_box(0);
                        v_isShared_3280_ = v_isSharedCheck_3284_;
                        state = 12;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_3272_ == 0 {
                    v___x_3274_ = v___x_3271_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3275_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_val_3269_);
                    v___x_3274_ = v_reuseFailAlloc_3275_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_3187_ = v___x_3265_;
                v___y_3188_ = v___y_3258_;
                v___y_3189_ = v_whereTk_3263_;
                v___y_3190_ = v___y_3257_;
                v___y_3191_ = v___x_3267_;
                v___y_3192_ = v___x_3266_;
                v___y_3193_ = v___x_3264_;
                v___y_3194_ = v_a_3261_;
                v___y_3195_ = v___x_3274_;
                state = 2;
                continue;
            }
            12 => {
                if v_isShared_3280_ == 0 {
                    v___x_3282_ = v___x_3279_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3283_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
                    v___x_3282_ = v_reuseFailAlloc_3283_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3282_;
            }
            14 => {
                v_fs_3345_ = l_Lean_Syntax_getArgs(v___x_3340_);
                crate::leanh::lean_dec(v___x_3340_);
                v___x_3346_ = l_Lean_Syntax_getHeadInfo(v_tk_3339_);
                crate::leanh::lean_dec(v_tk_3339_);
                v___x_3347_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_3345_);
                crate::leanh::lean_dec_ref(v_fs_3345_);
                v_whereInfo_3254_ = v___x_3346_;
                v_fs_3255_ = v___x_3347_;
                v_wds_x3f_3256_ = v_wds_x3f_3342_;
                v___y_3257_ = v___y_3343_;
                v___y_3258_ = v___y_3344_;
                state = 9;
                continue;
            }
            15 => {
                v_fs_3377_ = l_Lean_Syntax_getArgs(v___x_3372_);
                crate::leanh::lean_dec(v___x_3372_);
                v___x_3378_ = l_Lean_Syntax_getHeadInfo(v_tk_3371_);
                crate::leanh::lean_dec(v_tk_3371_);
                v___x_3379_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_3377_);
                crate::leanh::lean_dec_ref(v_fs_3377_);
                v_whereInfo_3254_ = v___x_3378_;
                v_fs_3255_ = v___x_3379_;
                v_wds_x3f_3256_ = v_wds_x3f_3374_;
                v___y_3257_ = v___y_3375_;
                v___y_3258_ = v___y_3376_;
                state = 9;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_DSL_elabConfig___boxed(
    mut v_tyName_3400_: *mut crate::leanh::LeanObject,
    mut v_info_3401_: *mut crate::leanh::LeanObject,
    mut v_id_3402_: *mut crate::leanh::LeanObject,
    mut v_ty_3403_: *mut crate::leanh::LeanObject,
    mut v_config_3404_: *mut crate::leanh::LeanObject,
    mut v_a_3405_: *mut crate::leanh::LeanObject,
    mut v_a_3406_: *mut crate::leanh::LeanObject,
    mut v_a_3407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3408_ = l_Lake_DSL_elabConfig(
        v_tyName_3400_,
        v_info_3401_,
        v_id_3402_,
        v_ty_3403_,
        v_config_3404_,
        v_a_3405_,
        v_a_3406_,
    );
    crate::leanh::lean_dec(v_a_3406_);
    crate::leanh::lean_dec_ref(v_a_3405_);
    crate::leanh::lean_dec_ref(v_info_3401_);
    return v_res_3408_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_DeclUtil(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_Binder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_MetaClasses(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_DeclUtil(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_DeclUtil(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_Binder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_MetaClasses(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_DeclUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_DeclUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_DSL_DeclUtil(builtin);
}
