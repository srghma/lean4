// Lean compiler output
// Module: Lean.Linter.EnvLinter.Basic
// Imports: Lean.Structure Lean.Elab.InfoTree.Main Lean.ExtraModUses Lean.Linter.EnvLinter.Nolint
use crate::r#gen::Init::Data::List::Basic::{l_List_elem___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_hasMacroScopes, l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_Syntax_getArg, l_Lean_replaceRef,
    l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_instDecidableEqString___boxed,
};
use crate::r#gen::Lean::Attributes::{
    l_Lean_instBEqAttributeKind_beq, l_Lean_registerBuiltinAttribute,
};
use crate::r#gen::Lean::AuxRecursor::{
    l_Lean_belowSuffix, l_Lean_brecOnSuffix, l_Lean_casesOnSuffix, l_Lean_recOnSuffix,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::Data::Name::{
    l_Lean_Name_isAnonymous, l_Lean_Name_isInternal, l_Lean_Name_updatePrefix,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_abortCommandExceptionId;
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    initialize_Lean_Elab_InfoTree_Main, runtime_initialize_Lean_Elab_InfoTree_Main,
};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_SimplePersistentEnvExtension_getState___redArg,
    l_Lean_registerSimplePersistentEnvExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_evalConstCheck___redArg,
    l_Lean_Environment_find_x3f, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_isConstructor, l_Lean_Environment_setExporting,
    l_Lean_EnvironmentHeader_moduleNames, l_Lean_PersistentEnvExtension_addEntry___redArg,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::l_Lean_mkConst;
use crate::r#gen::Lean::ExtraModUses::{
    initialize_Lean_ExtraModUses, runtime_initialize_Lean_ExtraModUses,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Linter::EnvLinter::Nolint::{
    initialize_Lean_Linter_EnvLinter_Nolint, runtime_initialize_Lean_Linter_EnvLinter_Nolint,
};
use crate::r#gen::Lean::LocalContext::l_Lean_LocalContext_empty;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey, l_Lean_Meta_isExprDefEq,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ResolveName::lean_is_reserved_name;
use crate::r#gen::Lean::Structure::{
    initialize_Lean_Structure, l_Lean_isSubobjectField_x3f, runtime_initialize_Lean_Structure,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_get_size, lean_array_mk, lean_mk_empty_array_with_capacity,
    lean_nat_dec_le, lean_nat_dec_lt, lean_string_dec_eq, lean_string_utf8_byte_size,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::MonadEnv::lean_has_compile_error;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [95, 102, 117, 110, 99, 116, 111, 114, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__1_value: LeanStringObject<15> =
    LeanStringObject {
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
            102, 117, 110, 99, 116, 111, 114, 95, 117, 110, 102, 111, 108, 100, 0,
        ],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__2_value: LeanStringObject<7> =
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
        m_data: [109, 117, 116, 117, 97, 108, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__4_value: LeanStringObject<6> =
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
        m_data: [110, 100, 114, 101, 99, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__5_value: LeanStringObject<8> =
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
        m_data: [110, 100, 114, 101, 99, 79, 110, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__6_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            110, 111, 67, 111, 110, 102, 117, 115, 105, 111, 110, 84, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__7_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [110, 111, 67, 111, 110, 102, 117, 115, 105, 111, 110, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__8_value: LeanStringObject<6> =
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
        m_data: [111, 102, 78, 97, 116, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__9_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [116, 111, 67, 116, 111, 114, 73, 100, 120, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__10_value: LeanStringObject<8> =
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
        m_data: [99, 116, 111, 114, 73, 100, 120, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__11_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [99, 116, 111, 114, 69, 108, 105, 109, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__12_value: LeanStringObject<13> =
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
        m_data: [99, 116, 111, 114, 69, 108, 105, 109, 84, 121, 112, 101, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__13_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__12_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__14_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__15_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__16_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__17_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__18_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__19_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__18_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__20_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__19_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__21_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__21_value)
        as *mut LeanObject;
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__25: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__26_value: LeanStringObject<7> =
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
        m_data: [98, 101, 108, 111, 119, 95, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__26_value)
        as *mut LeanObject;
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__27_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__27: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__28_value: LeanStringObject<8> =
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
        m_data: [98, 114, 101, 99, 79, 110, 95, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__28_value)
        as *mut LeanObject;
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__29_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__29: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__30_value: LeanStringObject<6> =
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
        m_data: [105, 110, 106, 69, 113, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__30_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__31_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [105, 110, 106, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__31_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__32_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [115, 105, 122, 101, 79, 102, 95, 115, 112, 101, 99, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__32_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__33_value: LeanStringObject<5> =
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
        m_data: [101, 108, 105, 109, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__33_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__34_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__7_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__34_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__35_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__33_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__34_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__35_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__36_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__32_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__35_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__36_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__37_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__31_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__36_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__37_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__38_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__30_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__37_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__38_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__39_value: LeanStringObject<7> =
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
        m_data: [103, 114, 105, 110, 100, 95, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__39_value)
        as *mut LeanObject;
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__40_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__40: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__41_value: LeanStringObject<8> =
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
        m_data: [117, 110, 115, 97, 102, 101, 95, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__41_value)
        as *mut LeanObject;
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__42_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__42: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__43_value: LeanStringObject<7> =
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
        m_data: [109, 97, 116, 99, 104, 95, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__43_value)
        as *mut LeanObject;
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__44_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__44: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__45_value: LeanStringObject<7> =
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
        m_data: [112, 114, 111, 111, 102, 95, 0],
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__45_value)
        as *mut LeanObject;
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__46_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__46: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [69, 110, 118, 76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value) as *mut LeanObject,5769806948869098747 as *mut LeanObject] };
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value) as *mut LeanObject,10615879079374430252 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 110, 118, 76, 105, 110, 116, 101, 114, 69, 120, 116, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value) as *mut LeanObject,5769806948869098747 as *mut LeanObject] };
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value) as *mut LeanObject,883370146421088886 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value: LeanCtorObject<7> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            98, 117, 105, 108, 116, 105, 110, 95, 101, 110, 118, 95, 108, 105, 110, 116, 101, 114,
            0,
        ],
    };
static mut l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value)
        as *mut LeanObject;
static l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value) as *mut LeanObject,5769806948869098747 as *mut LeanObject] };
pub static l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value: LeanCtorObject<3> =
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
                l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value)
                as *mut LeanObject,
            5765278832254366943 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_builtin__env__linter___closed__2_value: LeanStringObject<8> =
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
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Lean_Linter_EnvLinter_builtin__env__linter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_builtin__env__linter___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__2_value)
                as *mut LeanObject,
            12571085391447129896 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_builtin__env__linter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_builtin__env__linter___closed__4_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_builtin__env__linter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_builtin__env__linter___closed__5_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_EnvLinter_builtin__env__linter___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_builtin__env__linter___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__5_value)
                as *mut LeanObject,
            18170484695678750185 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_builtin__env__linter___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_builtin__env__linter___closed__7_value: LeanStringObject<7> =
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
        m_data: [32, 101, 120, 116, 114, 97, 0],
    };
static mut l_Lean_Linter_EnvLinter_builtin__env__linter___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_builtin__env__linter___closed__8_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__7_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_builtin__env__linter___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_builtin__env__linter___closed__9_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_builtin__env__linter___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_builtin__env__linter___closed__10_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_builtin__env__linter___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_builtin__env__linter___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_EnvLinter_builtin__env__linter___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__11_value)
        as *mut LeanObject;
pub static mut l_Lean_Linter_EnvLinter_builtin__env__linter: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__2_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__4_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__6_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__8_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__10_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__12_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [96, 32, 109, 117, 115, 116, 32, 104, 97, 118, 101, 32, 116, 121, 112, 101, 32, 96, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [96, 44, 32, 103, 111, 116, 32, 96, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut LeanObject,72621647814721793 as *mut LeanObject,65793 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: u64 = 0;
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [32, 98, 117, 116, 32, 105, 115, 32, 111, 110, 108, 121, 32, 109, 97, 114, 107, 101, 100, 32, 96, 109, 101, 116, 97, 96, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 98, 117, 105, 108, 116, 105, 110, 95, 101, 110, 118, 95, 108, 105, 110, 116, 101, 114, 96, 44, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 109, 97, 114, 107, 101, 100, 32, 97, 115, 32, 96, 112, 117, 98, 108, 105, 99, 96, 32, 97, 110, 100, 32, 96, 109, 101, 116, 97, 96, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [32, 98, 117, 116, 32, 105, 115, 32, 111, 110, 108, 121, 32, 109, 97, 114, 107, 101, 100, 32, 96, 112, 117, 98, 108, 105, 99, 96, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<49> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 98, 117, 105, 108, 116, 105, 110, 95, 101, 110, 118, 95, 108, 105, 110, 116, 101, 114, 96, 44, 32, 108, 105, 110, 116, 101, 114, 32, 96, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [96, 32, 104, 97, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 98, 101, 101, 110, 32, 100, 101, 99, 108, 97, 114, 101, 100, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<55> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 98, 117, 105, 108, 116, 105, 110, 95, 101, 110, 118, 95, 108, 105, 110, 116, 101, 114, 96, 44, 32, 109, 117, 115, 116, 32, 98, 101, 32, 103, 108, 111, 98, 97, 108, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value) as *mut LeanObject,4424989899264441540 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value) as *mut LeanObject,17593649045438483967 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [66, 97, 115, 105, 99, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,1532893815891708848 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanClosureObject<7> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*7) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 7, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,1181698850258291849 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value) as *mut LeanObject,855214909233877708 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value) as *mut LeanObject,16185419185597171146 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value) as *mut LeanObject,975467155693742801 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,10499686810115424040 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,15446775771034978777 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value) as *mut LeanObject,14932865160803606460 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value) as *mut LeanObject,9700217546231816890 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value) as *mut LeanObject,8970342832318132865 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject,6081596258135583654 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value) as *mut LeanObject,3443210053205297183 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value: LeanStringObject<62> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [85, 115, 101, 32, 116, 104, 105, 115, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 108, 105, 110, 116, 105, 110, 103, 32, 116, 101, 115, 116, 32, 105, 110, 32, 96, 108, 97, 107, 101, 32, 98, 117, 105, 108, 116, 105, 110, 45, 108, 105, 110, 116, 96, 0]};
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1450_: *mut LeanObject = core::ptr::null_mut();
    v___x_1449_ = lean_alloc_closure(
        l_instDecidableEqString___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_1450_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1450_, 0, v___x_1449_);
    return v___f_1450_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__22() -> *mut LeanObject {
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    v___x_1487_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__21;
    v___x_1488_ = l_Lean_belowSuffix;
    v___x_1489_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1489_, 0, v___x_1488_);
    lean_ctor_set(v___x_1489_, 1, v___x_1487_);
    return v___x_1489_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__23() -> *mut LeanObject {
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    v___x_1490_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__22_once),
        _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__22,
    );
    v___x_1491_ = l_Lean_brecOnSuffix;
    v___x_1492_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1492_, 0, v___x_1491_);
    lean_ctor_set(v___x_1492_, 1, v___x_1490_);
    return v___x_1492_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__24() -> *mut LeanObject {
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    v___x_1493_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__23_once),
        _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__23,
    );
    v___x_1494_ = l_Lean_recOnSuffix;
    v___x_1495_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1495_, 0, v___x_1494_);
    lean_ctor_set(v___x_1495_, 1, v___x_1493_);
    return v___x_1495_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__25() -> *mut LeanObject {
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    v___x_1496_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__24_once),
        _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__24,
    );
    v___x_1497_ = l_Lean_casesOnSuffix;
    v___x_1498_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1498_, 0, v___x_1497_);
    lean_ctor_set(v___x_1498_, 1, v___x_1496_);
    return v___x_1498_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__27() -> *mut LeanObject {
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    v___x_1500_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__26;
    v___x_1501_ = lean_string_utf8_byte_size(v___x_1500_);
    return v___x_1501_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__29() -> *mut LeanObject {
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    v___x_1503_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__28;
    v___x_1504_ = lean_string_utf8_byte_size(v___x_1503_);
    return v___x_1504_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__40() -> *mut LeanObject {
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    v___x_1525_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__39;
    v___x_1526_ = lean_string_utf8_byte_size(v___x_1525_);
    return v___x_1526_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__42() -> *mut LeanObject {
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    v___x_1528_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__41;
    v___x_1529_ = lean_string_utf8_byte_size(v___x_1528_);
    return v___x_1529_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__44() -> *mut LeanObject {
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    v___x_1531_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__43;
    v___x_1532_ = lean_string_utf8_byte_size(v___x_1531_);
    return v___x_1532_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__46() -> *mut LeanObject {
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    v___x_1534_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__45;
    v___x_1535_ = lean_string_utf8_byte_size(v___x_1534_);
    return v___x_1535_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_isAutoDecl___redArg(
    mut v_decl_1536_: *mut LeanObject,
    mut v_a_1537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1539_: u8 = 0;
    let mut v___x_1540_: u8 = 0;
    let mut v___x_1541_: u8 = 0;
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: u8 = 0;
    let mut v_pre_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1548_: u8 = 0;
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1555_: u8 = 0;
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1558_: u8 = 0;
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: u8 = 0;
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: u8 = 0;
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: u8 = 0;
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1587_: u8 = 0;
    let mut v_unused_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1593_: u8 = 0;
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1600_: u8 = 0;
    let mut v___y_1602_: u8 = 0;
    let mut v___f_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: u8 = 0;
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1618_: u8 = 0;
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: u8 = 0;
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: u8 = 0;
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1628_: u8 = 0;
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1633_: u8 = 0;
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: u8 = 0;
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: u8 = 0;
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1644_: u8 = 0;
    let mut v_unused_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: u8 = 0;
    let mut v___f_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: u8 = 0;
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: u8 = 0;
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: u8 = 0;
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: u8 = 0;
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: u8 = 0;
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: u8 = 0;
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: u8 = 0;
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: u8 = 0;
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1691_: u8 = 0;
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1539_ = l_Lean_Name_hasMacroScopes(v_decl_1536_);
                v___x_1540_ = 1;
                if v___x_1539_ == 0 {
                    v___x_1541_ = l_Lean_Name_isInternal(v_decl_1536_);
                    if v___x_1541_ == 0 {
                        v___x_1542_ = lean_st_ref_get(v_a_1537_);
                        v_env_1543_ = lean_ctor_get(v___x_1542_, 0);
                        lean_inc_ref_n(v_env_1543_, 2);
                        lean_dec(v___x_1542_);
                        lean_inc(v_decl_1536_);
                        v___x_1544_ = lean_is_reserved_name(v_env_1543_, v_decl_1536_);
                        if v___x_1544_ == 0 {
                            if lean_obj_tag(v_decl_1536_) == 1 {
                                v_pre_1545_ = lean_ctor_get(v_decl_1536_, 0);
                                lean_inc_n(v_pre_1545_, 2);
                                v_str_1546_ = lean_ctor_get(v_decl_1536_, 1);
                                lean_inc_ref(v_str_1546_);
                                lean_dec_ref_known(v_decl_1536_, 2);
                                v___x_1596_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg(
                                    v_pre_1545_,
                                    v_a_1537_,
                                );
                                v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
                                v_isSharedCheck_1691_ = (!lean_is_exclusive(v___x_1596_)) as u8;
                                if v_isSharedCheck_1691_ == 0 {
                                    v___x_1599_ = v___x_1596_;
                                    v_isShared_1600_ = v_isSharedCheck_1691_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_a_1597_);
                                    lean_dec(v___x_1596_);
                                    v___x_1599_ = lean_box(0);
                                    v_isShared_1600_ = v_isSharedCheck_1691_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_env_1543_);
                                lean_dec(v_decl_1536_);
                                v___x_1692_ = lean_box((v___x_1544_) as usize);
                                v___x_1693_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1693_, 0, v___x_1692_);
                                return v___x_1693_;
                            }
                        } else {
                            lean_dec_ref(v_env_1543_);
                            lean_dec(v_decl_1536_);
                            v___x_1694_ = lean_box((v___x_1540_) as usize);
                            v___x_1695_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1695_, 0, v___x_1694_);
                            return v___x_1695_;
                        }
                    } else {
                        lean_dec(v_decl_1536_);
                        v___x_1696_ = lean_box((v___x_1540_) as usize);
                        v___x_1697_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1697_, 0, v___x_1696_);
                        return v___x_1697_;
                    }
                } else {
                    lean_dec(v_decl_1536_);
                    v___x_1698_ = lean_box((v___x_1540_) as usize);
                    v___x_1699_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1699_, 0, v___x_1698_);
                    return v___x_1699_;
                }
            }
            1 => {
                v___x_1549_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__0;
                v___x_1550_ = l_Lean_Name_str___override(v_pre_1545_, v___x_1549_);
                lean_inc(v___x_1550_);
                lean_inc_ref(v_env_1543_);
                v___x_1551_ = l_Lean_Environment_find_x3f(v_env_1543_, v___x_1550_, v___y_1548_);
                if lean_obj_tag(v___x_1551_) == 1 {
                    v_val_1552_ = lean_ctor_get(v___x_1551_, 0);
                    v_isSharedCheck_1593_ = (!lean_is_exclusive(v___x_1551_)) as u8;
                    if v_isSharedCheck_1593_ == 0 {
                        v___x_1554_ = v___x_1551_;
                        v_isShared_1555_ = v_isSharedCheck_1593_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_1552_);
                        lean_dec(v___x_1551_);
                        v___x_1554_ = lean_box(0);
                        v_isShared_1555_ = v_isSharedCheck_1593_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1551_);
                    lean_dec(v___x_1550_);
                    lean_dec_ref(v_str_1546_);
                    lean_dec_ref(v_env_1543_);
                    v___x_1594_ = lean_box((v___x_1544_) as usize);
                    v___x_1595_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1595_, 0, v___x_1594_);
                    return v___x_1595_;
                }
            }
            2 => {
                if lean_obj_tag(v_val_1552_) == 5 {
                    lean_del_object(v___x_1554_);
                    v_isSharedCheck_1587_ = (!lean_is_exclusive(v_val_1552_)) as u8;
                    if v_isSharedCheck_1587_ == 0 {
                        v_unused_1588_ = lean_ctor_get(v_val_1552_, 0);
                        lean_dec(v_unused_1588_);
                        v___x_1557_ = v_val_1552_;
                        v_isShared_1558_ = v_isSharedCheck_1587_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_val_1552_);
                        v___x_1557_ = lean_box(0);
                        v_isShared_1558_ = v_isSharedCheck_1587_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_val_1552_);
                    lean_dec(v___x_1550_);
                    lean_dec_ref(v_str_1546_);
                    lean_dec_ref(v_env_1543_);
                    v___x_1589_ = lean_box((v___x_1544_) as usize);
                    if v_isShared_1555_ == 0 {
                        lean_ctor_set_tag(v___x_1554_, 0);
                        lean_ctor_set(v___x_1554_, 0, v___x_1589_);
                        v___x_1591_ = v___x_1554_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
                        v___x_1591_ = v_reuseFailAlloc_1592_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1559_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__1;
                v___x_1560_ = lean_string_dec_eq(v_str_1546_, v___x_1559_);
                if v___x_1560_ == 0 {
                    v___x_1561_ = l_Lean_casesOnSuffix;
                    v___x_1562_ = lean_string_dec_eq(v_str_1546_, v___x_1561_);
                    if v___x_1562_ == 0 {
                        v___x_1563_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__2;
                        v___x_1564_ = lean_string_dec_eq(v_str_1546_, v___x_1563_);
                        if v___x_1564_ == 0 {
                            v___x_1565_ = l_Lean_Name_str___override(v___x_1550_, v_str_1546_);
                            v___x_1566_ =
                                l_Lean_Environment_isConstructor(v_env_1543_, v___x_1565_);
                            if v___x_1566_ == 0 {
                                v___x_1567_ = lean_box((v___x_1544_) as usize);
                                if v_isShared_1558_ == 0 {
                                    lean_ctor_set_tag(v___x_1557_, 0);
                                    lean_ctor_set(v___x_1557_, 0, v___x_1567_);
                                    v___x_1569_ = v___x_1557_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
                                    v___x_1569_ = v_reuseFailAlloc_1570_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v___x_1571_ = lean_box((v___x_1540_) as usize);
                                if v_isShared_1558_ == 0 {
                                    lean_ctor_set_tag(v___x_1557_, 0);
                                    lean_ctor_set(v___x_1557_, 0, v___x_1571_);
                                    v___x_1573_ = v___x_1557_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
                                    v___x_1573_ = v_reuseFailAlloc_1574_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_1550_);
                            lean_dec_ref(v_str_1546_);
                            lean_dec_ref(v_env_1543_);
                            v___x_1575_ = lean_box((v___x_1540_) as usize);
                            if v_isShared_1558_ == 0 {
                                lean_ctor_set_tag(v___x_1557_, 0);
                                lean_ctor_set(v___x_1557_, 0, v___x_1575_);
                                v___x_1577_ = v___x_1557_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
                                v___x_1577_ = v_reuseFailAlloc_1578_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_1550_);
                        lean_dec_ref(v_str_1546_);
                        lean_dec_ref(v_env_1543_);
                        v___x_1579_ = lean_box((v___x_1540_) as usize);
                        if v_isShared_1558_ == 0 {
                            lean_ctor_set_tag(v___x_1557_, 0);
                            lean_ctor_set(v___x_1557_, 0, v___x_1579_);
                            v___x_1581_ = v___x_1557_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1579_);
                            v___x_1581_ = v_reuseFailAlloc_1582_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_1550_);
                    lean_dec_ref(v_str_1546_);
                    lean_dec_ref(v_env_1543_);
                    v___x_1583_ = lean_box((v___x_1540_) as usize);
                    if v_isShared_1558_ == 0 {
                        lean_ctor_set_tag(v___x_1557_, 0);
                        lean_ctor_set(v___x_1557_, 0, v___x_1583_);
                        v___x_1585_ = v___x_1557_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
                        v___x_1585_ = v_reuseFailAlloc_1586_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1569_;
            }
            5 => {
                return v___x_1573_;
            }
            6 => {
                return v___x_1577_;
            }
            7 => {
                return v___x_1581_;
            }
            8 => {
                return v___x_1585_;
            }
            9 => {
                return v___x_1591_;
            }
            10 => {
                v___x_1680_ = (lean_unbox(v_a_1597_) as u8);
                lean_dec(v_a_1597_);
                if v___x_1680_ == 0 {
                    v___x_1681_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__45;
                    v___x_1682_ = lean_string_utf8_byte_size(v_str_1546_);
                    v___x_1683_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__46
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__46_once
                        ),
                        _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__46,
                    );
                    v___x_1684_ = lean_nat_dec_le(v___x_1683_, v___x_1682_);
                    if v___x_1684_ == 0 {
                        state = 21;
                        continue;
                    } else {
                        v___x_1685_ = lean_unsigned_to_nat(0);
                        v___x_1686_ = lean_string_memcmp(
                            v_str_1546_,
                            v___x_1681_,
                            v___x_1685_,
                            v___x_1685_,
                            v___x_1683_,
                        );
                        if v___x_1686_ == 0 {
                            state = 21;
                            continue;
                        } else {
                            lean_del_object(v___x_1599_);
                            lean_dec_ref(v_str_1546_);
                            lean_dec(v_pre_1545_);
                            lean_dec_ref(v_env_1543_);
                            v___x_1687_ = lean_box((v___x_1540_) as usize);
                            v___x_1688_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1688_, 0, v___x_1687_);
                            return v___x_1688_;
                        }
                    }
                } else {
                    lean_del_object(v___x_1599_);
                    lean_dec_ref(v_str_1546_);
                    lean_dec(v_pre_1545_);
                    lean_dec_ref(v_env_1543_);
                    v___x_1689_ = lean_box((v___x_1540_) as usize);
                    v___x_1690_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1690_, 0, v___x_1689_);
                    return v___x_1690_;
                }
            }
            11 => {
                v___f_1603_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__3_once
                    ),
                    _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__3,
                );
                v___x_1604_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__25_once
                    ),
                    _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__25,
                );
                lean_inc_ref(v_str_1546_);
                v___x_1605_ = l_List_elem___redArg(v___f_1603_, v_str_1546_, v___x_1604_);
                if v___x_1605_ == 0 {
                    v___x_1606_ = lean_box(0);
                    lean_inc_ref(v_str_1546_);
                    v___x_1607_ = l_Lean_Name_str___override(v___x_1606_, v_str_1546_);
                    lean_inc(v_pre_1545_);
                    lean_inc_ref(v_env_1543_);
                    v___x_1608_ =
                        l_Lean_isSubobjectField_x3f(v_env_1543_, v_pre_1545_, v___x_1607_);
                    if lean_obj_tag(v___x_1608_) == 1 {
                        lean_dec_ref_known(v___x_1608_, 1);
                        lean_dec_ref(v_str_1546_);
                        lean_dec(v_pre_1545_);
                        lean_dec_ref(v_env_1543_);
                        v___x_1609_ = lean_box((v___x_1540_) as usize);
                        if v_isShared_1600_ == 0 {
                            lean_ctor_set(v___x_1599_, 0, v___x_1609_);
                            v___x_1611_ = v___x_1599_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
                            v___x_1611_ = v_reuseFailAlloc_1612_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1608_);
                        lean_del_object(v___x_1599_);
                        v___y_1548_ = v___y_1602_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_str_1546_);
                    lean_dec(v_pre_1545_);
                    lean_dec_ref(v_env_1543_);
                    v___x_1613_ = lean_box((v___x_1540_) as usize);
                    if v_isShared_1600_ == 0 {
                        lean_ctor_set(v___x_1599_, 0, v___x_1613_);
                        v___x_1615_ = v___x_1599_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
                        v___x_1615_ = v_reuseFailAlloc_1616_;
                        state = 13;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_1611_;
            }
            13 => {
                return v___x_1615_;
            }
            14 => {
                v___x_1619_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__26;
                v___x_1620_ = lean_string_utf8_byte_size(v_str_1546_);
                v___x_1621_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__27
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__27_once
                    ),
                    _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__27,
                );
                v___x_1622_ = lean_nat_dec_le(v___x_1621_, v___x_1620_);
                if v___x_1622_ == 0 {
                    v___y_1602_ = v___y_1618_;
                    state = 11;
                    continue;
                } else {
                    v___x_1623_ = lean_unsigned_to_nat(0);
                    v___x_1624_ = lean_string_memcmp(
                        v_str_1546_,
                        v___x_1619_,
                        v___x_1623_,
                        v___x_1623_,
                        v___x_1621_,
                    );
                    if v___x_1624_ == 0 {
                        v___y_1602_ = v___y_1618_;
                        state = 11;
                        continue;
                    } else {
                        lean_del_object(v___x_1599_);
                        lean_dec_ref(v_str_1546_);
                        lean_dec(v_pre_1545_);
                        lean_dec_ref(v_env_1543_);
                        v___x_1625_ = lean_box((v___x_1540_) as usize);
                        v___x_1626_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1626_, 0, v___x_1625_);
                        return v___x_1626_;
                    }
                }
            }
            15 => {
                if v___y_1628_ == 0 {
                    lean_inc(v_pre_1545_);
                    lean_inc_ref(v_env_1543_);
                    v___x_1629_ =
                        l_Lean_Environment_find_x3f(v_env_1543_, v_pre_1545_, v___y_1628_);
                    if lean_obj_tag(v___x_1629_) == 1 {
                        v_val_1630_ = lean_ctor_get(v___x_1629_, 0);
                        lean_inc(v_val_1630_);
                        lean_dec_ref_known(v___x_1629_, 1);
                        if lean_obj_tag(v_val_1630_) == 5 {
                            v_isSharedCheck_1644_ = (!lean_is_exclusive(v_val_1630_)) as u8;
                            if v_isSharedCheck_1644_ == 0 {
                                v_unused_1645_ = lean_ctor_get(v_val_1630_, 0);
                                lean_dec(v_unused_1645_);
                                v___x_1632_ = v_val_1630_;
                                v_isShared_1633_ = v_isSharedCheck_1644_;
                                state = 16;
                                continue;
                            } else {
                                lean_dec(v_val_1630_);
                                v___x_1632_ = lean_box(0);
                                v_isShared_1633_ = v_isSharedCheck_1644_;
                                state = 16;
                                continue;
                            }
                        } else {
                            lean_dec(v_val_1630_);
                            lean_del_object(v___x_1599_);
                            v___y_1548_ = v___y_1628_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1629_);
                        lean_del_object(v___x_1599_);
                        v___y_1548_ = v___y_1628_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1599_);
                    lean_dec_ref(v_str_1546_);
                    lean_dec(v_pre_1545_);
                    lean_dec_ref(v_env_1543_);
                    v___x_1646_ = lean_box((v___x_1540_) as usize);
                    v___x_1647_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1647_, 0, v___x_1646_);
                    return v___x_1647_;
                }
            }
            16 => {
                v___x_1634_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__28;
                v___x_1635_ = lean_string_utf8_byte_size(v_str_1546_);
                v___x_1636_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__29
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__29_once
                    ),
                    _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__29,
                );
                v___x_1637_ = lean_nat_dec_le(v___x_1636_, v___x_1635_);
                if v___x_1637_ == 0 {
                    lean_del_object(v___x_1632_);
                    v___y_1618_ = v___y_1628_;
                    state = 14;
                    continue;
                } else {
                    v___x_1638_ = lean_unsigned_to_nat(0);
                    v___x_1639_ = lean_string_memcmp(
                        v_str_1546_,
                        v___x_1634_,
                        v___x_1638_,
                        v___x_1638_,
                        v___x_1636_,
                    );
                    if v___x_1639_ == 0 {
                        lean_del_object(v___x_1632_);
                        v___y_1618_ = v___y_1628_;
                        state = 14;
                        continue;
                    } else {
                        lean_del_object(v___x_1599_);
                        lean_dec_ref(v_str_1546_);
                        lean_dec(v_pre_1545_);
                        lean_dec_ref(v_env_1543_);
                        v___x_1640_ = lean_box((v___x_1540_) as usize);
                        if v_isShared_1633_ == 0 {
                            lean_ctor_set_tag(v___x_1632_, 0);
                            lean_ctor_set(v___x_1632_, 0, v___x_1640_);
                            v___x_1642_ = v___x_1632_;
                            state = 17;
                            continue;
                        } else {
                            v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
                            v___x_1642_ = v_reuseFailAlloc_1643_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            17 => {
                return v___x_1642_;
            }
            18 => {
                lean_inc(v_pre_1545_);
                lean_inc_ref(v_env_1543_);
                v___x_1649_ = l_Lean_Environment_isConstructor(v_env_1543_, v_pre_1545_);
                if v___x_1649_ == 0 {
                    v___y_1628_ = v___x_1649_;
                    state = 15;
                    continue;
                } else {
                    v___f_1650_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__3_once
                        ),
                        _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__3,
                    );
                    v___x_1651_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__38;
                    lean_inc_ref(v_str_1546_);
                    v___x_1652_ = l_List_elem___redArg(v___f_1650_, v_str_1546_, v___x_1651_);
                    v___y_1628_ = v___x_1652_;
                    state = 15;
                    continue;
                }
            }
            19 => {
                v___x_1654_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__39;
                v___x_1655_ = lean_string_utf8_byte_size(v_str_1546_);
                v___x_1656_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__40
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__40_once
                    ),
                    _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__40,
                );
                v___x_1657_ = lean_nat_dec_le(v___x_1656_, v___x_1655_);
                if v___x_1657_ == 0 {
                    state = 18;
                    continue;
                } else {
                    v___x_1658_ = lean_unsigned_to_nat(0);
                    v___x_1659_ = lean_string_memcmp(
                        v_str_1546_,
                        v___x_1654_,
                        v___x_1658_,
                        v___x_1658_,
                        v___x_1656_,
                    );
                    if v___x_1659_ == 0 {
                        state = 18;
                        continue;
                    } else {
                        lean_del_object(v___x_1599_);
                        lean_dec_ref(v_str_1546_);
                        lean_dec(v_pre_1545_);
                        lean_dec_ref(v_env_1543_);
                        v___x_1660_ = lean_box((v___x_1540_) as usize);
                        v___x_1661_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1661_, 0, v___x_1660_);
                        return v___x_1661_;
                    }
                }
            }
            20 => {
                v___x_1663_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__41;
                v___x_1664_ = lean_string_utf8_byte_size(v_str_1546_);
                v___x_1665_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__42
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__42_once
                    ),
                    _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__42,
                );
                v___x_1666_ = lean_nat_dec_le(v___x_1665_, v___x_1664_);
                if v___x_1666_ == 0 {
                    state = 19;
                    continue;
                } else {
                    v___x_1667_ = lean_unsigned_to_nat(0);
                    v___x_1668_ = lean_string_memcmp(
                        v_str_1546_,
                        v___x_1663_,
                        v___x_1667_,
                        v___x_1667_,
                        v___x_1665_,
                    );
                    if v___x_1668_ == 0 {
                        state = 19;
                        continue;
                    } else {
                        lean_del_object(v___x_1599_);
                        lean_dec_ref(v_str_1546_);
                        lean_dec(v_pre_1545_);
                        lean_dec_ref(v_env_1543_);
                        v___x_1669_ = lean_box((v___x_1540_) as usize);
                        v___x_1670_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1670_, 0, v___x_1669_);
                        return v___x_1670_;
                    }
                }
            }
            21 => {
                v___x_1672_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__43;
                v___x_1673_ = lean_string_utf8_byte_size(v_str_1546_);
                v___x_1674_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__44
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__44_once
                    ),
                    _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__44,
                );
                v___x_1675_ = lean_nat_dec_le(v___x_1674_, v___x_1673_);
                if v___x_1675_ == 0 {
                    state = 20;
                    continue;
                } else {
                    v___x_1676_ = lean_unsigned_to_nat(0);
                    v___x_1677_ = lean_string_memcmp(
                        v_str_1546_,
                        v___x_1672_,
                        v___x_1676_,
                        v___x_1676_,
                        v___x_1674_,
                    );
                    if v___x_1677_ == 0 {
                        state = 20;
                        continue;
                    } else {
                        lean_del_object(v___x_1599_);
                        lean_dec_ref(v_str_1546_);
                        lean_dec(v_pre_1545_);
                        lean_dec_ref(v_env_1543_);
                        v___x_1678_ = lean_box((v___x_1540_) as usize);
                        v___x_1679_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1679_, 0, v___x_1678_);
                        return v___x_1679_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_EnvLinter_isAutoDecl___redArg___boxed(
    mut v_decl_1700_: *mut LeanObject,
    mut v_a_1701_: *mut LeanObject,
    mut v_a_1702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1703_: *mut LeanObject = core::ptr::null_mut();
    v_res_1703_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg(v_decl_1700_, v_a_1701_);
    lean_dec(v_a_1701_);
    return v_res_1703_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_isAutoDecl(
    mut v_decl_1704_: *mut LeanObject,
    mut v_a_1705_: *mut LeanObject,
    mut v_a_1706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    v___x_1708_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg(v_decl_1704_, v_a_1706_);
    return v___x_1708_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_isAutoDecl___boxed(
    mut v_decl_1709_: *mut LeanObject,
    mut v_a_1710_: *mut LeanObject,
    mut v_a_1711_: *mut LeanObject,
    mut v_a_1712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1713_: *mut LeanObject = core::ptr::null_mut();
    v_res_1713_ = l_Lean_Linter_EnvLinter_isAutoDecl(v_decl_1709_, v_a_1710_, v_a_1711_);
    lean_dec(v_a_1711_);
    lean_dec_ref(v_a_1710_);
    return v_res_1713_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    v___x_1714_ = lean_box(0);
    v___x_1715_ = l_Lean_Elab_abortCommandExceptionId;
    v___x_1716_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1716_, 0, v___x_1715_);
    lean_ctor_set(v___x_1716_, 1, v___x_1714_);
    return v___x_1716_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg()
-> *mut LeanObject {
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    v___x_1718_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___closed__0);
    v___x_1719_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1719_, 0, v___x_1718_);
    return v___x_1719_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___boxed(
    mut v___y_1720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1721_: *mut LeanObject = core::ptr::null_mut();
    v_res_1721_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg();
    return v_res_1721_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__0()
-> *mut LeanObject {
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    v___x_1722_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1722_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1()
-> *mut LeanObject {
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    v___x_1723_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__0);
    v___x_1724_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1724_, 0, v___x_1723_);
    return v___x_1724_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2()
-> *mut LeanObject {
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    v___x_1725_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1);
    v___x_1726_ = lean_unsigned_to_nat(0);
    v___x_1727_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1727_, 0, v___x_1726_);
    lean_ctor_set(v___x_1727_, 1, v___x_1726_);
    lean_ctor_set(v___x_1727_, 2, v___x_1726_);
    lean_ctor_set(v___x_1727_, 3, v___x_1726_);
    lean_ctor_set(v___x_1727_, 4, v___x_1725_);
    lean_ctor_set(v___x_1727_, 5, v___x_1725_);
    lean_ctor_set(v___x_1727_, 6, v___x_1725_);
    lean_ctor_set(v___x_1727_, 7, v___x_1725_);
    lean_ctor_set(v___x_1727_, 8, v___x_1725_);
    lean_ctor_set(v___x_1727_, 9, v___x_1725_);
    return v___x_1727_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3()
-> *mut LeanObject {
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    v___x_1728_ = lean_unsigned_to_nat(32);
    v___x_1729_ = lean_mk_empty_array_with_capacity(v___x_1728_);
    v___x_1730_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1730_, 0, v___x_1729_);
    return v___x_1730_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__4()
-> *mut LeanObject {
    let mut v___x_1731_: usize = 0;
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    v___x_1731_ = 5usize;
    v___x_1732_ = lean_unsigned_to_nat(0);
    v___x_1733_ = lean_unsigned_to_nat(32);
    v___x_1734_ = lean_mk_empty_array_with_capacity(v___x_1733_);
    v___x_1735_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3);
    v___x_1736_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1736_, 0, v___x_1735_);
    lean_ctor_set(v___x_1736_, 1, v___x_1734_);
    lean_ctor_set(v___x_1736_, 2, v___x_1732_);
    lean_ctor_set(v___x_1736_, 3, v___x_1732_);
    lean_ctor_set_usize(v___x_1736_, 4, v___x_1731_);
    return v___x_1736_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5()
-> *mut LeanObject {
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    v___x_1737_ = lean_box(1);
    v___x_1738_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__4);
    v___x_1739_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1);
    v___x_1740_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1740_, 0, v___x_1739_);
    lean_ctor_set(v___x_1740_, 1, v___x_1738_);
    lean_ctor_set(v___x_1740_, 2, v___x_1737_);
    return v___x_1740_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3(
    mut v_msgData_1741_: *mut LeanObject,
    mut v___y_1742_: *mut LeanObject,
    mut v___y_1743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    v___x_1745_ = lean_st_ref_get(v___y_1743_);
    v_env_1746_ = lean_ctor_get(v___x_1745_, 0);
    lean_inc_ref(v_env_1746_);
    lean_dec(v___x_1745_);
    v_options_1747_ = lean_ctor_get(v___y_1742_, 2);
    v___x_1748_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2);
    v___x_1749_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5);
    lean_inc_ref(v_options_1747_);
    v___x_1750_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1750_, 0, v_env_1746_);
    lean_ctor_set(v___x_1750_, 1, v___x_1748_);
    lean_ctor_set(v___x_1750_, 2, v___x_1749_);
    lean_ctor_set(v___x_1750_, 3, v_options_1747_);
    v___x_1751_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1751_, 0, v___x_1750_);
    lean_ctor_set(v___x_1751_, 1, v_msgData_1741_);
    v___x_1752_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1752_, 0, v___x_1751_);
    return v___x_1752_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_msgData_1753_: *mut LeanObject,
    mut v___y_1754_: *mut LeanObject,
    mut v___y_1755_: *mut LeanObject,
    mut v___y_1756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1757_: *mut LeanObject = core::ptr::null_mut();
    v_res_1757_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3(v_msgData_1753_, v___y_1754_, v___y_1755_);
    lean_dec(v___y_1755_);
    lean_dec_ref(v___y_1754_);
    return v_res_1757_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(
    mut v_msg_1758_: *mut LeanObject,
    mut v___y_1759_: *mut LeanObject,
    mut v___y_1760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1767_: u8 = 0;
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1762_ = lean_ctor_get(v___y_1759_, 5);
                v___x_1763_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3(v_msg_1758_, v___y_1759_, v___y_1760_);
                v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
                v_isSharedCheck_1772_ = (!lean_is_exclusive(v___x_1763_)) as u8;
                if v_isSharedCheck_1772_ == 0 {
                    v___x_1766_ = v___x_1763_;
                    v_isShared_1767_ = v_isSharedCheck_1772_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1764_);
                    lean_dec(v___x_1763_);
                    v___x_1766_ = lean_box(0);
                    v_isShared_1767_ = v_isSharedCheck_1772_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1762_);
                v___x_1768_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1768_, 0, v_ref_1762_);
                lean_ctor_set(v___x_1768_, 1, v_a_1764_);
                if v_isShared_1767_ == 0 {
                    lean_ctor_set_tag(v___x_1766_, 1);
                    lean_ctor_set(v___x_1766_, 0, v___x_1768_);
                    v___x_1770_ = v___x_1766_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
                    v___x_1770_ = v_reuseFailAlloc_1771_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1770_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_msg_1773_: *mut LeanObject,
    mut v___y_1774_: *mut LeanObject,
    mut v___y_1775_: *mut LeanObject,
    mut v___y_1776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1777_: *mut LeanObject = core::ptr::null_mut();
    v_res_1777_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_1773_, v___y_1774_, v___y_1775_);
    lean_dec(v___y_1775_);
    lean_dec_ref(v___y_1774_);
    return v_res_1777_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg(
    mut v_x_1778_: *mut LeanObject,
    mut v___y_1779_: *mut LeanObject,
    mut v___y_1780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1788_: u8 = 0;
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1792_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1778_) == 0 {
                    v_a_1782_ = lean_ctor_get(v_x_1778_, 0);
                    lean_inc(v_a_1782_);
                    lean_dec_ref_known(v_x_1778_, 1);
                    v___x_1783_ = l_Lean_stringToMessageData(v_a_1782_);
                    v___x_1784_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1783_, v___y_1779_, v___y_1780_);
                    return v___x_1784_;
                } else {
                    v_a_1785_ = lean_ctor_get(v_x_1778_, 0);
                    v_isSharedCheck_1792_ = (!lean_is_exclusive(v_x_1778_)) as u8;
                    if v_isSharedCheck_1792_ == 0 {
                        v___x_1787_ = v_x_1778_;
                        v_isShared_1788_ = v_isSharedCheck_1792_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1785_);
                        lean_dec(v_x_1778_);
                        v___x_1787_ = lean_box(0);
                        v_isShared_1788_ = v_isSharedCheck_1792_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1788_ == 0 {
                    lean_ctor_set_tag(v___x_1787_, 0);
                    v___x_1790_ = v___x_1787_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
                    v___x_1790_ = v_reuseFailAlloc_1791_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1790_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg___boxed(
    mut v_x_1793_: *mut LeanObject,
    mut v___y_1794_: *mut LeanObject,
    mut v___y_1795_: *mut LeanObject,
    mut v___y_1796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1797_: *mut LeanObject = core::ptr::null_mut();
    v_res_1797_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg(v_x_1793_, v___y_1794_, v___y_1795_);
    lean_dec(v___y_1795_);
    lean_dec_ref(v___y_1794_);
    return v_res_1797_;
}
pub unsafe fn l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg(
    mut v_typeName_1798_: *mut LeanObject,
    mut v_constName_1799_: *mut LeanObject,
    mut v___y_1800_: *mut LeanObject,
    mut v___y_1801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: u8 = 0;
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1820_: u8 = 0;
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1803_ = lean_st_ref_get(v___y_1801_);
                v_env_1804_ = lean_ctor_get(v___x_1803_, 0);
                lean_inc_ref(v_env_1804_);
                lean_dec(v___x_1803_);
                lean_inc(v_constName_1799_);
                v___x_1805_ = lean_has_compile_error(v_env_1804_, v_constName_1799_);
                if v___x_1805_ == 0 {
                    v___x_1806_ = lean_st_ref_get(v___y_1801_);
                    v_env_1807_ = lean_ctor_get(v___x_1806_, 0);
                    lean_inc_ref(v_env_1807_);
                    lean_dec(v___x_1806_);
                    v_options_1808_ = lean_ctor_get(v___y_1800_, 2);
                    v___x_1809_ = l_Lean_Environment_evalConstCheck___redArg(
                        v_env_1807_,
                        v_options_1808_,
                        v_typeName_1798_,
                        v_constName_1799_,
                    );
                    v___x_1810_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg(v___x_1809_, v___y_1800_, v___y_1801_);
                    return v___x_1810_;
                } else {
                    v___x_1811_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg();
                    if lean_obj_tag(v___x_1811_) == 0 {
                        lean_dec_ref_known(v___x_1811_, 1);
                        v___x_1812_ = lean_st_ref_get(v___y_1801_);
                        v_env_1813_ = lean_ctor_get(v___x_1812_, 0);
                        lean_inc_ref(v_env_1813_);
                        lean_dec(v___x_1812_);
                        v_options_1814_ = lean_ctor_get(v___y_1800_, 2);
                        v___x_1815_ = l_Lean_Environment_evalConstCheck___redArg(
                            v_env_1813_,
                            v_options_1814_,
                            v_typeName_1798_,
                            v_constName_1799_,
                        );
                        v___x_1816_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg(v___x_1815_, v___y_1800_, v___y_1801_);
                        return v___x_1816_;
                    } else {
                        lean_dec(v_constName_1799_);
                        lean_dec(v_typeName_1798_);
                        v_a_1817_ = lean_ctor_get(v___x_1811_, 0);
                        v_isSharedCheck_1824_ = (!lean_is_exclusive(v___x_1811_)) as u8;
                        if v_isSharedCheck_1824_ == 0 {
                            v___x_1819_ = v___x_1811_;
                            v_isShared_1820_ = v_isSharedCheck_1824_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1817_);
                            lean_dec(v___x_1811_);
                            v___x_1819_ = lean_box(0);
                            v_isShared_1820_ = v_isSharedCheck_1824_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1820_ == 0 {
                    v___x_1822_ = v___x_1819_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
                    v___x_1822_ = v_reuseFailAlloc_1823_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1822_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg___boxed(
    mut v_typeName_1825_: *mut LeanObject,
    mut v_constName_1826_: *mut LeanObject,
    mut v___y_1827_: *mut LeanObject,
    mut v___y_1828_: *mut LeanObject,
    mut v___y_1829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1830_: *mut LeanObject = core::ptr::null_mut();
    v_res_1830_ = l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg(v_typeName_1825_, v_constName_1826_, v___y_1827_, v___y_1828_);
    lean_dec(v___y_1828_);
    lean_dec_ref(v___y_1827_);
    return v_res_1830_;
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1(
    mut v_name_1838_: *mut LeanObject,
    mut v_declName_1839_: *mut LeanObject,
    mut v_a_1840_: *mut LeanObject,
    mut v_a_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1848_: u8 = 0;
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1853_: u8 = 0;
    let mut v_a_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1857_: u8 = 0;
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1843_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3;
                lean_inc(v_declName_1839_);
                v___x_1844_ = l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg(v___x_1843_, v_declName_1839_, v_a_1840_, v_a_1841_);
                if lean_obj_tag(v___x_1844_) == 0 {
                    v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
                    v_isSharedCheck_1853_ = (!lean_is_exclusive(v___x_1844_)) as u8;
                    if v_isSharedCheck_1853_ == 0 {
                        v___x_1847_ = v___x_1844_;
                        v_isShared_1848_ = v_isSharedCheck_1853_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1845_);
                        lean_dec(v___x_1844_);
                        v___x_1847_ = lean_box(0);
                        v_isShared_1848_ = v_isSharedCheck_1853_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_declName_1839_);
                    lean_dec(v_name_1838_);
                    v_a_1854_ = lean_ctor_get(v___x_1844_, 0);
                    v_isSharedCheck_1861_ = (!lean_is_exclusive(v___x_1844_)) as u8;
                    if v_isSharedCheck_1861_ == 0 {
                        v___x_1856_ = v___x_1844_;
                        v_isShared_1857_ = v_isSharedCheck_1861_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1854_);
                        lean_dec(v___x_1844_);
                        v___x_1856_ = lean_box(0);
                        v_isShared_1857_ = v_isSharedCheck_1861_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1849_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1849_, 0, v_a_1845_);
                lean_ctor_set(v___x_1849_, 1, v_name_1838_);
                lean_ctor_set(v___x_1849_, 2, v_declName_1839_);
                if v_isShared_1848_ == 0 {
                    lean_ctor_set(v___x_1847_, 0, v___x_1849_);
                    v___x_1851_ = v___x_1847_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
                    v___x_1851_ = v_reuseFailAlloc_1852_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1851_;
            }
            3 => {
                if v_isShared_1857_ == 0 {
                    v___x_1859_ = v___x_1856_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
                    v___x_1859_ = v_reuseFailAlloc_1860_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___boxed(
    mut v_name_1862_: *mut LeanObject,
    mut v_declName_1863_: *mut LeanObject,
    mut v_a_1864_: *mut LeanObject,
    mut v_a_1865_: *mut LeanObject,
    mut v_a_1866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1867_: *mut LeanObject = core::ptr::null_mut();
    v_res_1867_ =
        l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1(
            v_name_1862_,
            v_declName_1863_,
            v_a_1864_,
            v_a_1865_,
        );
    lean_dec(v_a_1865_);
    lean_dec_ref(v_a_1864_);
    return v_res_1867_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1(
    mut v_00_u03b1_1868_: *mut LeanObject,
    mut v___y_1869_: *mut LeanObject,
    mut v___y_1870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    v___x_1872_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg();
    return v___x_1872_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___boxed(
    mut v_00_u03b1_1873_: *mut LeanObject,
    mut v___y_1874_: *mut LeanObject,
    mut v___y_1875_: *mut LeanObject,
    mut v___y_1876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1877_: *mut LeanObject = core::ptr::null_mut();
    v_res_1877_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1(v_00_u03b1_1873_, v___y_1874_, v___y_1875_);
    lean_dec(v___y_1875_);
    lean_dec_ref(v___y_1874_);
    return v_res_1877_;
}
pub unsafe fn l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0(
    mut v_00_u03b1_1878_: *mut LeanObject,
    mut v_typeName_1879_: *mut LeanObject,
    mut v_constName_1880_: *mut LeanObject,
    mut v___y_1881_: *mut LeanObject,
    mut v___y_1882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    v___x_1884_ = l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg(v_typeName_1879_, v_constName_1880_, v___y_1881_, v___y_1882_);
    return v___x_1884_;
}
pub unsafe fn l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___boxed(
    mut v_00_u03b1_1885_: *mut LeanObject,
    mut v_typeName_1886_: *mut LeanObject,
    mut v_constName_1887_: *mut LeanObject,
    mut v___y_1888_: *mut LeanObject,
    mut v___y_1889_: *mut LeanObject,
    mut v___y_1890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1891_: *mut LeanObject = core::ptr::null_mut();
    v_res_1891_ = l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0(v_00_u03b1_1885_, v_typeName_1886_, v_constName_1887_, v___y_1888_, v___y_1889_);
    lean_dec(v___y_1889_);
    lean_dec_ref(v___y_1888_);
    return v_res_1891_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0(
    mut v_00_u03b1_1892_: *mut LeanObject,
    mut v_x_1893_: *mut LeanObject,
    mut v___y_1894_: *mut LeanObject,
    mut v___y_1895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    v___x_1897_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg(v_x_1893_, v___y_1894_, v___y_1895_);
    return v___x_1897_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___boxed(
    mut v_00_u03b1_1898_: *mut LeanObject,
    mut v_x_1899_: *mut LeanObject,
    mut v___y_1900_: *mut LeanObject,
    mut v___y_1901_: *mut LeanObject,
    mut v___y_1902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1903_: *mut LeanObject = core::ptr::null_mut();
    v_res_1903_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0(v_00_u03b1_1898_, v_x_1899_, v___y_1900_, v___y_1901_);
    lean_dec(v___y_1901_);
    lean_dec_ref(v___y_1900_);
    return v_res_1903_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1904_: *mut LeanObject,
    mut v_msg_1905_: *mut LeanObject,
    mut v___y_1906_: *mut LeanObject,
    mut v___y_1907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    v___x_1909_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_1905_, v___y_1906_, v___y_1907_);
    return v___x_1909_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1910_: *mut LeanObject,
    mut v_msg_1911_: *mut LeanObject,
    mut v___y_1912_: *mut LeanObject,
    mut v___y_1913_: *mut LeanObject,
    mut v___y_1914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1915_: *mut LeanObject = core::ptr::null_mut();
    v_res_1915_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1(v_00_u03b1_1910_, v_msg_1911_, v___y_1912_, v___y_1913_);
    lean_dec(v___y_1913_);
    lean_dec_ref(v___y_1912_);
    return v_res_1915_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_getEnvLinter(
    mut v_name_1916_: *mut LeanObject,
    mut v_declName_1917_: *mut LeanObject,
    mut v_a_1918_: *mut LeanObject,
    mut v_a_1919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    v___x_1921_ =
        l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1(
            v_name_1916_,
            v_declName_1917_,
            v_a_1918_,
            v_a_1919_,
        );
    return v___x_1921_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_getEnvLinter___boxed(
    mut v_name_1922_: *mut LeanObject,
    mut v_declName_1923_: *mut LeanObject,
    mut v_a_1924_: *mut LeanObject,
    mut v_a_1925_: *mut LeanObject,
    mut v_a_1926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1927_: *mut LeanObject = core::ptr::null_mut();
    v_res_1927_ =
        l_Lean_Linter_EnvLinter_getEnvLinter(v_name_1922_, v_declName_1923_, v_a_1924_, v_a_1925_);
    lean_dec(v_a_1925_);
    lean_dec_ref(v_a_1924_);
    return v_res_1927_;
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_(
    mut v_m_1928_: *mut LeanObject,
    mut v_x_1929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1930_ = lean_ctor_get(v_x_1929_, 0);
    v___x_1931_ = lean_box(0);
    lean_inc(v_fst_1930_);
    v___x_1932_ = l_Lean_Name_updatePrefix(v_fst_1930_, v___x_1931_);
    v___x_1933_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v___x_1932_,
        v_x_1929_,
        v_m_1928_,
    );
    return v___x_1933_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0_spec__0(
    mut v_as_1934_: *mut LeanObject,
    mut v_i_1935_: usize,
    mut v_stop_1936_: usize,
    mut v_b_1937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1938_: u8 = 0;
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: usize = 0;
    let mut v___x_1945_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1938_ = lean_usize_dec_eq(v_i_1935_, v_stop_1936_);
                if v___x_1938_ == 0 {
                    v___x_1939_ = lean_array_uget_borrowed(v_as_1934_, v_i_1935_);
                    v_fst_1940_ = lean_ctor_get(v___x_1939_, 0);
                    v___x_1941_ = lean_box(0);
                    lean_inc(v_fst_1940_);
                    v___x_1942_ = l_Lean_Name_updatePrefix(v_fst_1940_, v___x_1941_);
                    lean_inc(v___x_1939_);
                    v___x_1943_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1942_, v___x_1939_, v_b_1937_);
                    v___x_1944_ = 1usize;
                    v___x_1945_ = lean_usize_add(v_i_1935_, v___x_1944_);
                    v_i_1935_ = v___x_1945_;
                    v_b_1937_ = v___x_1943_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1937_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_as_1947_: *mut LeanObject,
    mut v_i_1948_: *mut LeanObject,
    mut v_stop_1949_: *mut LeanObject,
    mut v_b_1950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1951_: usize = 0;
    let mut v_stop_boxed_1952_: usize = 0;
    let mut v_res_1953_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1951_ = lean_unbox_usize(v_i_1948_);
    lean_dec(v_i_1948_);
    v_stop_boxed_1952_ = lean_unbox_usize(v_stop_1949_);
    lean_dec(v_stop_1949_);
    v_res_1953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0_spec__0(v_as_1947_, v_i_boxed_1951_, v_stop_boxed_1952_, v_b_1950_);
    lean_dec_ref(v_as_1947_);
    return v_res_1953_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0(
    mut v_as_1954_: *mut LeanObject,
    mut v_i_1955_: usize,
    mut v_stop_1956_: usize,
    mut v_b_1957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1958_: u8 = 0;
    v___x_1958_ = lean_usize_dec_eq(v_i_1955_, v_stop_1956_);
    if v___x_1958_ == 0 {
        let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_1960_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1964_: usize = 0;
        let mut v___x_1965_: usize = 0;
        let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
        v___x_1959_ = lean_array_uget_borrowed(v_as_1954_, v_i_1955_);
        v_fst_1960_ = lean_ctor_get(v___x_1959_, 0);
        v___x_1961_ = lean_box(0);
        lean_inc(v_fst_1960_);
        v___x_1962_ = l_Lean_Name_updatePrefix(v_fst_1960_, v___x_1961_);
        lean_inc(v___x_1959_);
        v___x_1963_ =
            l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
                v___x_1962_,
                v___x_1959_,
                v_b_1957_,
            );
        v___x_1964_ = 1usize;
        v___x_1965_ = lean_usize_add(v_i_1955_, v___x_1964_);
        v___x_1966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0_spec__0(v_as_1954_, v___x_1965_, v_stop_1956_, v___x_1963_);
        return v___x_1966_;
    } else {
        return v_b_1957_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0___boxed(
    mut v_as_1967_: *mut LeanObject,
    mut v_i_1968_: *mut LeanObject,
    mut v_stop_1969_: *mut LeanObject,
    mut v_b_1970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1971_: usize = 0;
    let mut v_stop_boxed_1972_: usize = 0;
    let mut v_res_1973_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1971_ = lean_unbox_usize(v_i_1968_);
    lean_dec(v_i_1968_);
    v_stop_boxed_1972_ = lean_unbox_usize(v_stop_1969_);
    lean_dec(v_stop_1969_);
    v_res_1973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0(v_as_1967_, v_i_boxed_1971_, v_stop_boxed_1972_, v_b_1970_);
    lean_dec_ref(v_as_1967_);
    return v_res_1973_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__1(
    mut v_as_1974_: *mut LeanObject,
    mut v_i_1975_: usize,
    mut v_stop_1976_: usize,
    mut v_b_1977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: usize = 0;
    let mut v___x_1981_: usize = 0;
    let mut v___x_1983_: u8 = 0;
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: u8 = 0;
    let mut v___x_1988_: u8 = 0;
    let mut v___x_1989_: usize = 0;
    let mut v___x_1990_: usize = 0;
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: usize = 0;
    let mut v___x_1993_: usize = 0;
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1983_ = lean_usize_dec_eq(v_i_1975_, v_stop_1976_);
                if v___x_1983_ == 0 {
                    v___x_1984_ = lean_array_uget_borrowed(v_as_1974_, v_i_1975_);
                    v___x_1985_ = lean_unsigned_to_nat(0);
                    v___x_1986_ = lean_array_get_size(v___x_1984_);
                    v___x_1987_ = lean_nat_dec_lt(v___x_1985_, v___x_1986_);
                    if v___x_1987_ == 0 {
                        v___y_1979_ = v_b_1977_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1988_ = lean_nat_dec_le(v___x_1986_, v___x_1986_);
                        if v___x_1988_ == 0 {
                            if v___x_1987_ == 0 {
                                v___y_1979_ = v_b_1977_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1989_ = 0usize;
                                v___x_1990_ = lean_usize_of_nat(v___x_1986_);
                                v___x_1991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0(v___x_1984_, v___x_1989_, v___x_1990_, v_b_1977_);
                                v___y_1979_ = v___x_1991_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1992_ = 0usize;
                            v___x_1993_ = lean_usize_of_nat(v___x_1986_);
                            v___x_1994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0(v___x_1984_, v___x_1992_, v___x_1993_, v_b_1977_);
                            v___y_1979_ = v___x_1994_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_1977_;
                }
            }
            1 => {
                v___x_1980_ = 1usize;
                v___x_1981_ = lean_usize_add(v_i_1975_, v___x_1980_);
                v_i_1975_ = v___x_1981_;
                v_b_1977_ = v___y_1979_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__1___boxed(
    mut v_as_1995_: *mut LeanObject,
    mut v_i_1996_: *mut LeanObject,
    mut v_stop_1997_: *mut LeanObject,
    mut v_b_1998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1999_: usize = 0;
    let mut v_stop_boxed_2000_: usize = 0;
    let mut v_res_2001_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1999_ = lean_unbox_usize(v_i_1996_);
    lean_dec(v_i_1996_);
    v_stop_boxed_2000_ = lean_unbox_usize(v_stop_1997_);
    lean_dec(v_stop_1997_);
    v_res_2001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__1(v_as_1995_, v_i_boxed_1999_, v_stop_boxed_2000_, v_b_1998_);
    lean_dec_ref(v_as_1995_);
    return v_res_2001_;
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_(
    mut v_nss_2002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: u8 = 0;
    v___x_2003_ = lean_box(1);
    v___x_2004_ = lean_unsigned_to_nat(0);
    v___x_2005_ = lean_array_get_size(v_nss_2002_);
    v___x_2006_ = lean_nat_dec_lt(v___x_2004_, v___x_2005_);
    if v___x_2006_ == 0 {
        return v___x_2003_;
    } else {
        let mut v___x_2007_: u8 = 0;
        v___x_2007_ = lean_nat_dec_le(v___x_2005_, v___x_2005_);
        if v___x_2007_ == 0 {
            if v___x_2006_ == 0 {
                return v___x_2003_;
            } else {
                let mut v___x_2008_: usize = 0;
                let mut v___x_2009_: usize = 0;
                let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
                v___x_2008_ = 0usize;
                v___x_2009_ = lean_usize_of_nat(v___x_2005_);
                v___x_2010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__1(v_nss_2002_, v___x_2008_, v___x_2009_, v___x_2003_);
                return v___x_2010_;
            }
        } else {
            let mut v___x_2011_: usize = 0;
            let mut v___x_2012_: usize = 0;
            let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
            v___x_2011_ = 0usize;
            v___x_2012_ = lean_usize_of_nat(v___x_2005_);
            v___x_2013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__1(v_nss_2002_, v___x_2011_, v___x_2012_, v___x_2003_);
            return v___x_2013_;
        }
    }
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2____boxed(
    mut v_nss_2014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2015_: *mut LeanObject = core::ptr::null_mut();
    v_res_2015_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_(v_nss_2014_);
    lean_dec_ref(v_nss_2014_);
    return v_res_2015_;
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_(
    mut v_es_2016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    v___x_2017_ = lean_array_mk(v_es_2016_);
    return v___x_2017_;
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    v___x_2035_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_;
    v___x_2036_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2035_);
    return v___x_2036_;
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2____boxed(
    mut v_a_2037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2038_: *mut LeanObject = core::ptr::null_mut();
    v_res_2038_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_();
    return v_res_2038_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg(
    mut v_ref_2070_: *mut LeanObject,
    mut v_msg_2071_: *mut LeanObject,
    mut v___y_2072_: *mut LeanObject,
    mut v___y_2073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2087_: u8 = 0;
    let mut v_cancelTk_x3f_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2089_: u8 = 0;
    let mut v_inheritedTraceOptions_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_2075_ = lean_ctor_get(v___y_2072_, 0);
    v_fileMap_2076_ = lean_ctor_get(v___y_2072_, 1);
    v_options_2077_ = lean_ctor_get(v___y_2072_, 2);
    v_currRecDepth_2078_ = lean_ctor_get(v___y_2072_, 3);
    v_maxRecDepth_2079_ = lean_ctor_get(v___y_2072_, 4);
    v_ref_2080_ = lean_ctor_get(v___y_2072_, 5);
    v_currNamespace_2081_ = lean_ctor_get(v___y_2072_, 6);
    v_openDecls_2082_ = lean_ctor_get(v___y_2072_, 7);
    v_initHeartbeats_2083_ = lean_ctor_get(v___y_2072_, 8);
    v_maxHeartbeats_2084_ = lean_ctor_get(v___y_2072_, 9);
    v_quotContext_2085_ = lean_ctor_get(v___y_2072_, 10);
    v_currMacroScope_2086_ = lean_ctor_get(v___y_2072_, 11);
    v_diag_2087_ = lean_ctor_get_uint8(
        v___y_2072_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2088_ = lean_ctor_get(v___y_2072_, 12);
    v_suppressElabErrors_2089_ = lean_ctor_get_uint8(
        v___y_2072_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2090_ = lean_ctor_get(v___y_2072_, 13);
    v_ref_2091_ = l_Lean_replaceRef(v_ref_2070_, v_ref_2080_);
    lean_inc_ref(v_inheritedTraceOptions_2090_);
    lean_inc(v_cancelTk_x3f_2088_);
    lean_inc(v_currMacroScope_2086_);
    lean_inc(v_quotContext_2085_);
    lean_inc(v_maxHeartbeats_2084_);
    lean_inc(v_initHeartbeats_2083_);
    lean_inc(v_openDecls_2082_);
    lean_inc(v_currNamespace_2081_);
    lean_inc(v_maxRecDepth_2079_);
    lean_inc(v_currRecDepth_2078_);
    lean_inc_ref(v_options_2077_);
    lean_inc_ref(v_fileMap_2076_);
    lean_inc_ref(v_fileName_2075_);
    v___x_2092_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_2092_, 0, v_fileName_2075_);
    lean_ctor_set(v___x_2092_, 1, v_fileMap_2076_);
    lean_ctor_set(v___x_2092_, 2, v_options_2077_);
    lean_ctor_set(v___x_2092_, 3, v_currRecDepth_2078_);
    lean_ctor_set(v___x_2092_, 4, v_maxRecDepth_2079_);
    lean_ctor_set(v___x_2092_, 5, v_ref_2091_);
    lean_ctor_set(v___x_2092_, 6, v_currNamespace_2081_);
    lean_ctor_set(v___x_2092_, 7, v_openDecls_2082_);
    lean_ctor_set(v___x_2092_, 8, v_initHeartbeats_2083_);
    lean_ctor_set(v___x_2092_, 9, v_maxHeartbeats_2084_);
    lean_ctor_set(v___x_2092_, 10, v_quotContext_2085_);
    lean_ctor_set(v___x_2092_, 11, v_currMacroScope_2086_);
    lean_ctor_set(v___x_2092_, 12, v_cancelTk_x3f_2088_);
    lean_ctor_set(v___x_2092_, 13, v_inheritedTraceOptions_2090_);
    lean_ctor_set_uint8(
        v___x_2092_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_2087_,
    );
    lean_ctor_set_uint8(
        v___x_2092_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2089_,
    );
    v___x_2093_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_2071_, v___x_2092_, v___y_2073_);
    lean_dec_ref_known(v___x_2092_, 14);
    return v___x_2093_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg___boxed(
    mut v_ref_2094_: *mut LeanObject,
    mut v_msg_2095_: *mut LeanObject,
    mut v___y_2096_: *mut LeanObject,
    mut v___y_2097_: *mut LeanObject,
    mut v___y_2098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2099_: *mut LeanObject = core::ptr::null_mut();
    v_res_2099_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ref_2094_, v_msg_2095_, v___y_2096_, v___y_2097_);
    lean_dec(v___y_2097_);
    lean_dec_ref(v___y_2096_);
    lean_dec(v_ref_2094_);
    return v_res_2099_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    v___x_2101_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__0;
    v___x_2102_ = l_Lean_stringToMessageData(v___x_2101_);
    return v___x_2102_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    v___x_2104_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__2;
    v___x_2105_ = l_Lean_stringToMessageData(v___x_2104_);
    return v___x_2105_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    v___x_2107_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__4;
    v___x_2108_ = l_Lean_stringToMessageData(v___x_2107_);
    return v___x_2108_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    v___x_2110_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__6;
    v___x_2111_ = l_Lean_stringToMessageData(v___x_2110_);
    return v___x_2111_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    v___x_2113_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__8;
    v___x_2114_ = l_Lean_stringToMessageData(v___x_2113_);
    return v___x_2114_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    v___x_2116_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__10;
    v___x_2117_ = l_Lean_stringToMessageData(v___x_2116_);
    return v___x_2117_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    v___x_2119_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__12;
    v___x_2120_ = l_Lean_stringToMessageData(v___x_2119_);
    return v___x_2120_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg(
    mut v_msg_2121_: *mut LeanObject,
    mut v_declHint_2122_: *mut LeanObject,
    mut v___y_2123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: u8 = 0;
    let mut v_isExporting_2128_: u8 = 0;
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: u8 = 0;
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2150_: u8 = 0;
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: u8 = 0;
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2182_: u8 = 0;
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2125_ = lean_st_ref_get(v___y_2123_);
                v_env_2126_ = lean_ctor_get(v___x_2125_, 0);
                lean_inc_ref(v_env_2126_);
                lean_dec(v___x_2125_);
                v___x_2127_ = l_Lean_Name_isAnonymous(v_declHint_2122_);
                if v___x_2127_ == 0 {
                    v_isExporting_2128_ = lean_ctor_get_uint8(
                        v_env_2126_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2128_ == 0 {
                        lean_dec_ref(v_env_2126_);
                        lean_dec(v_declHint_2122_);
                        v___x_2129_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2129_, 0, v_msg_2121_);
                        return v___x_2129_;
                    } else {
                        lean_inc_ref(v_env_2126_);
                        v___x_2130_ = l_Lean_Environment_setExporting(v_env_2126_, v___x_2127_);
                        lean_inc(v_declHint_2122_);
                        lean_inc_ref(v___x_2130_);
                        v___x_2131_ = l_Lean_Environment_contains(
                            v___x_2130_,
                            v_declHint_2122_,
                            v_isExporting_2128_,
                        );
                        if v___x_2131_ == 0 {
                            lean_dec_ref(v___x_2130_);
                            lean_dec_ref(v_env_2126_);
                            lean_dec(v_declHint_2122_);
                            v___x_2132_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_2132_, 0, v_msg_2121_);
                            return v___x_2132_;
                        } else {
                            v___x_2133_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2);
                            v___x_2134_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5);
                            v___x_2135_ = l_Lean_Options_empty;
                            v___x_2136_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_2136_, 0, v___x_2130_);
                            lean_ctor_set(v___x_2136_, 1, v___x_2133_);
                            lean_ctor_set(v___x_2136_, 2, v___x_2134_);
                            lean_ctor_set(v___x_2136_, 3, v___x_2135_);
                            lean_inc(v_declHint_2122_);
                            v___x_2137_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2122_, v___x_2127_);
                            v_c_2138_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_2138_, 0, v___x_2136_);
                            lean_ctor_set(v_c_2138_, 1, v___x_2137_);
                            v___x_2139_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2126_,
                                v_declHint_2122_,
                            );
                            if lean_obj_tag(v___x_2139_) == 0 {
                                lean_dec_ref(v_env_2126_);
                                lean_dec(v_declHint_2122_);
                                v___x_2140_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1);
                                v___x_2141_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2141_, 0, v___x_2140_);
                                lean_ctor_set(v___x_2141_, 1, v_c_2138_);
                                v___x_2142_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3);
                                v___x_2143_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2143_, 0, v___x_2141_);
                                lean_ctor_set(v___x_2143_, 1, v___x_2142_);
                                v___x_2144_ = l_Lean_MessageData_note(v___x_2143_);
                                v___x_2145_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2145_, 0, v_msg_2121_);
                                lean_ctor_set(v___x_2145_, 1, v___x_2144_);
                                v___x_2146_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_2146_, 0, v___x_2145_);
                                return v___x_2146_;
                            } else {
                                v_val_2147_ = lean_ctor_get(v___x_2139_, 0);
                                v_isSharedCheck_2182_ = (!lean_is_exclusive(v___x_2139_)) as u8;
                                if v_isSharedCheck_2182_ == 0 {
                                    v___x_2149_ = v___x_2139_;
                                    v_isShared_2150_ = v_isSharedCheck_2182_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_2147_);
                                    lean_dec(v___x_2139_);
                                    v___x_2149_ = lean_box(0);
                                    v_isShared_2150_ = v_isSharedCheck_2182_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_2126_);
                    lean_dec(v_declHint_2122_);
                    v___x_2183_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2183_, 0, v_msg_2121_);
                    return v___x_2183_;
                }
            }
            1 => {
                v___x_2151_ = lean_box(0);
                v___x_2152_ = l_Lean_Environment_header(v_env_2126_);
                lean_dec_ref(v_env_2126_);
                v___x_2153_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2152_);
                v_mod_2154_ = lean_array_get(v___x_2151_, v___x_2153_, v_val_2147_);
                lean_dec(v_val_2147_);
                lean_dec_ref(v___x_2153_);
                v___x_2155_ = l_Lean_isPrivateName(v_declHint_2122_);
                lean_dec(v_declHint_2122_);
                if v___x_2155_ == 0 {
                    v___x_2156_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5);
                    v___x_2157_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2157_, 0, v___x_2156_);
                    lean_ctor_set(v___x_2157_, 1, v_c_2138_);
                    v___x_2158_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7);
                    v___x_2159_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2159_, 0, v___x_2157_);
                    lean_ctor_set(v___x_2159_, 1, v___x_2158_);
                    v___x_2160_ = l_Lean_MessageData_ofName(v_mod_2154_);
                    v___x_2161_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2161_, 0, v___x_2159_);
                    lean_ctor_set(v___x_2161_, 1, v___x_2160_);
                    v___x_2162_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9);
                    v___x_2163_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2163_, 0, v___x_2161_);
                    lean_ctor_set(v___x_2163_, 1, v___x_2162_);
                    v___x_2164_ = l_Lean_MessageData_note(v___x_2163_);
                    v___x_2165_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2165_, 0, v_msg_2121_);
                    lean_ctor_set(v___x_2165_, 1, v___x_2164_);
                    if v_isShared_2150_ == 0 {
                        lean_ctor_set_tag(v___x_2149_, 0);
                        lean_ctor_set(v___x_2149_, 0, v___x_2165_);
                        v___x_2167_ = v___x_2149_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
                        v___x_2167_ = v_reuseFailAlloc_2168_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2169_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1);
                    v___x_2170_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2170_, 0, v___x_2169_);
                    lean_ctor_set(v___x_2170_, 1, v_c_2138_);
                    v___x_2171_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11);
                    v___x_2172_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2172_, 0, v___x_2170_);
                    lean_ctor_set(v___x_2172_, 1, v___x_2171_);
                    v___x_2173_ = l_Lean_MessageData_ofName(v_mod_2154_);
                    v___x_2174_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2174_, 0, v___x_2172_);
                    lean_ctor_set(v___x_2174_, 1, v___x_2173_);
                    v___x_2175_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13);
                    v___x_2176_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2176_, 0, v___x_2174_);
                    lean_ctor_set(v___x_2176_, 1, v___x_2175_);
                    v___x_2177_ = l_Lean_MessageData_note(v___x_2176_);
                    v___x_2178_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2178_, 0, v_msg_2121_);
                    lean_ctor_set(v___x_2178_, 1, v___x_2177_);
                    if v_isShared_2150_ == 0 {
                        lean_ctor_set_tag(v___x_2149_, 0);
                        lean_ctor_set(v___x_2149_, 0, v___x_2178_);
                        v___x_2180_ = v___x_2149_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
                        v___x_2180_ = v_reuseFailAlloc_2181_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2167_;
            }
            3 => {
                return v___x_2180_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___boxed(
    mut v_msg_2184_: *mut LeanObject,
    mut v_declHint_2185_: *mut LeanObject,
    mut v___y_2186_: *mut LeanObject,
    mut v___y_2187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2188_: *mut LeanObject = core::ptr::null_mut();
    v_res_2188_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg(v_msg_2184_, v_declHint_2185_, v___y_2186_);
    lean_dec(v___y_2186_);
    return v_res_2188_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7(
    mut v_msg_2189_: *mut LeanObject,
    mut v_declHint_2190_: *mut LeanObject,
    mut v___y_2191_: *mut LeanObject,
    mut v___y_2192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2198_: u8 = 0;
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2204_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2194_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg(v_msg_2189_, v_declHint_2190_, v___y_2192_);
                v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
                v_isSharedCheck_2204_ = (!lean_is_exclusive(v___x_2194_)) as u8;
                if v_isSharedCheck_2204_ == 0 {
                    v___x_2197_ = v___x_2194_;
                    v_isShared_2198_ = v_isSharedCheck_2204_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2195_);
                    lean_dec(v___x_2194_);
                    v___x_2197_ = lean_box(0);
                    v_isShared_2198_ = v_isSharedCheck_2204_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2199_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2200_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_2200_, 0, v___x_2199_);
                lean_ctor_set(v___x_2200_, 1, v_a_2195_);
                if v_isShared_2198_ == 0 {
                    lean_ctor_set(v___x_2197_, 0, v___x_2200_);
                    v___x_2202_ = v___x_2197_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
                    v___x_2202_ = v_reuseFailAlloc_2203_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7___boxed(
    mut v_msg_2205_: *mut LeanObject,
    mut v_declHint_2206_: *mut LeanObject,
    mut v___y_2207_: *mut LeanObject,
    mut v___y_2208_: *mut LeanObject,
    mut v___y_2209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2210_: *mut LeanObject = core::ptr::null_mut();
    v_res_2210_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7(v_msg_2205_, v_declHint_2206_, v___y_2207_, v___y_2208_);
    lean_dec(v___y_2208_);
    lean_dec_ref(v___y_2207_);
    return v_res_2210_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_ref_2211_: *mut LeanObject,
    mut v_msg_2212_: *mut LeanObject,
    mut v_declHint_2213_: *mut LeanObject,
    mut v___y_2214_: *mut LeanObject,
    mut v___y_2215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    v___x_2217_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7(v_msg_2212_, v_declHint_2213_, v___y_2214_, v___y_2215_);
    v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
    lean_inc(v_a_2218_);
    lean_dec_ref(v___x_2217_);
    v___x_2219_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ref_2211_, v_a_2218_, v___y_2214_, v___y_2215_);
    return v___x_2219_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_ref_2220_: *mut LeanObject,
    mut v_msg_2221_: *mut LeanObject,
    mut v_declHint_2222_: *mut LeanObject,
    mut v___y_2223_: *mut LeanObject,
    mut v___y_2224_: *mut LeanObject,
    mut v___y_2225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2226_: *mut LeanObject = core::ptr::null_mut();
    v_res_2226_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2220_, v_msg_2221_, v_declHint_2222_, v___y_2223_, v___y_2224_);
    lean_dec(v___y_2224_);
    lean_dec_ref(v___y_2223_);
    lean_dec(v_ref_2220_);
    return v_res_2226_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    v___x_2228_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_2229_ = l_Lean_stringToMessageData(v___x_2228_);
    return v___x_2229_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    v___x_2231_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_2232_ = l_Lean_stringToMessageData(v___x_2231_);
    return v___x_2232_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(
    mut v_ref_2233_: *mut LeanObject,
    mut v_constName_2234_: *mut LeanObject,
    mut v___y_2235_: *mut LeanObject,
    mut v___y_2236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: u8 = 0;
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    v___x_2238_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_2239_ = 0;
    lean_inc(v_constName_2234_);
    v___x_2240_ = l_Lean_MessageData_ofConstName(v_constName_2234_, v___x_2239_);
    v___x_2241_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2241_, 0, v___x_2238_);
    lean_ctor_set(v___x_2241_, 1, v___x_2240_);
    v___x_2242_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_2243_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2243_, 0, v___x_2241_);
    lean_ctor_set(v___x_2243_, 1, v___x_2242_);
    v___x_2244_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2233_, v___x_2243_, v_constName_2234_, v___y_2235_, v___y_2236_);
    return v___x_2244_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_2245_: *mut LeanObject,
    mut v_constName_2246_: *mut LeanObject,
    mut v___y_2247_: *mut LeanObject,
    mut v___y_2248_: *mut LeanObject,
    mut v___y_2249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2250_: *mut LeanObject = core::ptr::null_mut();
    v_res_2250_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_2245_, v_constName_2246_, v___y_2247_, v___y_2248_);
    lean_dec(v___y_2248_);
    lean_dec_ref(v___y_2247_);
    lean_dec(v_ref_2245_);
    return v_res_2250_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_constName_2251_: *mut LeanObject,
    mut v___y_2252_: *mut LeanObject,
    mut v___y_2253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    v_ref_2255_ = lean_ctor_get(v___y_2252_, 5);
    v___x_2256_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_2255_, v_constName_2251_, v___y_2252_, v___y_2253_);
    return v___x_2256_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_constName_2257_: *mut LeanObject,
    mut v___y_2258_: *mut LeanObject,
    mut v___y_2259_: *mut LeanObject,
    mut v___y_2260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2261_: *mut LeanObject = core::ptr::null_mut();
    v_res_2261_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_2257_, v___y_2258_, v___y_2259_);
    lean_dec(v___y_2259_);
    lean_dec_ref(v___y_2258_);
    return v_res_2261_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0(
    mut v_constName_2262_: *mut LeanObject,
    mut v___y_2263_: *mut LeanObject,
    mut v___y_2264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: u8 = 0;
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2278_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2266_ = lean_st_ref_get(v___y_2264_);
                v_env_2267_ = lean_ctor_get(v___x_2266_, 0);
                lean_inc_ref(v_env_2267_);
                lean_dec(v___x_2266_);
                v___x_2268_ = 0;
                lean_inc(v_constName_2262_);
                v___x_2269_ =
                    l_Lean_Environment_find_x3f(v_env_2267_, v_constName_2262_, v___x_2268_);
                if lean_obj_tag(v___x_2269_) == 0 {
                    v___x_2270_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_2262_, v___y_2263_, v___y_2264_);
                    return v___x_2270_;
                } else {
                    lean_dec(v_constName_2262_);
                    v_val_2271_ = lean_ctor_get(v___x_2269_, 0);
                    v_isSharedCheck_2278_ = (!lean_is_exclusive(v___x_2269_)) as u8;
                    if v_isSharedCheck_2278_ == 0 {
                        v___x_2273_ = v___x_2269_;
                        v_isShared_2274_ = v_isSharedCheck_2278_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2271_);
                        lean_dec(v___x_2269_);
                        v___x_2273_ = lean_box(0);
                        v_isShared_2274_ = v_isSharedCheck_2278_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2274_ == 0 {
                    lean_ctor_set_tag(v___x_2273_, 0);
                    v___x_2276_ = v___x_2273_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_val_2271_);
                    v___x_2276_ = v_reuseFailAlloc_2277_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2276_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0___boxed(
    mut v_constName_2279_: *mut LeanObject,
    mut v___y_2280_: *mut LeanObject,
    mut v___y_2281_: *mut LeanObject,
    mut v___y_2282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2283_: *mut LeanObject = core::ptr::null_mut();
    v_res_2283_ = l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0(v_constName_2279_, v___y_2280_, v___y_2281_);
    lean_dec(v___y_2281_);
    lean_dec_ref(v___y_2280_);
    return v_res_2283_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2_spec__5(
    mut v_a_2284_: *mut LeanObject,
    mut v_a_2285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2291_: u8 = 0;
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2284_) == 0 {
                    v___x_2286_ = l_List_reverse___redArg(v_a_2285_);
                    return v___x_2286_;
                } else {
                    v_head_2287_ = lean_ctor_get(v_a_2284_, 0);
                    v_tail_2288_ = lean_ctor_get(v_a_2284_, 1);
                    v_isSharedCheck_2297_ = (!lean_is_exclusive(v_a_2284_)) as u8;
                    if v_isSharedCheck_2297_ == 0 {
                        v___x_2290_ = v_a_2284_;
                        v_isShared_2291_ = v_isSharedCheck_2297_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2288_);
                        lean_inc(v_head_2287_);
                        lean_dec(v_a_2284_);
                        v___x_2290_ = lean_box(0);
                        v_isShared_2291_ = v_isSharedCheck_2297_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2292_ = l_Lean_mkLevelParam(v_head_2287_);
                if v_isShared_2291_ == 0 {
                    lean_ctor_set(v___x_2290_, 1, v_a_2285_);
                    lean_ctor_set(v___x_2290_, 0, v___x_2292_);
                    v___x_2294_ = v___x_2290_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2292_);
                    lean_ctor_set(v_reuseFailAlloc_2296_, 1, v_a_2285_);
                    v___x_2294_ = v_reuseFailAlloc_2296_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2284_ = v_tail_2288_;
                v_a_2285_ = v___x_2294_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2_spec__4(
    mut v_constName_2298_: *mut LeanObject,
    mut v___y_2299_: *mut LeanObject,
    mut v___y_2300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: u8 = 0;
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2310_: u8 = 0;
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2314_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2302_ = lean_st_ref_get(v___y_2300_);
                v_env_2303_ = lean_ctor_get(v___x_2302_, 0);
                lean_inc_ref(v_env_2303_);
                lean_dec(v___x_2302_);
                v___x_2304_ = 0;
                lean_inc(v_constName_2298_);
                v___x_2305_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_2303_,
                    v_constName_2298_,
                    v___x_2304_,
                );
                if lean_obj_tag(v___x_2305_) == 0 {
                    v___x_2306_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_2298_, v___y_2299_, v___y_2300_);
                    return v___x_2306_;
                } else {
                    lean_dec(v_constName_2298_);
                    v_val_2307_ = lean_ctor_get(v___x_2305_, 0);
                    v_isSharedCheck_2314_ = (!lean_is_exclusive(v___x_2305_)) as u8;
                    if v_isSharedCheck_2314_ == 0 {
                        v___x_2309_ = v___x_2305_;
                        v_isShared_2310_ = v_isSharedCheck_2314_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2307_);
                        lean_dec(v___x_2305_);
                        v___x_2309_ = lean_box(0);
                        v_isShared_2310_ = v_isSharedCheck_2314_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2310_ == 0 {
                    lean_ctor_set_tag(v___x_2309_, 0);
                    v___x_2312_ = v___x_2309_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_val_2307_);
                    v___x_2312_ = v_reuseFailAlloc_2313_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2312_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(
    mut v_constName_2315_: *mut LeanObject,
    mut v___y_2316_: *mut LeanObject,
    mut v___y_2317_: *mut LeanObject,
    mut v___y_2318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2319_: *mut LeanObject = core::ptr::null_mut();
    v_res_2319_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_constName_2315_, v___y_2316_, v___y_2317_);
    lean_dec(v___y_2317_);
    lean_dec_ref(v___y_2316_);
    return v_res_2319_;
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2(
    mut v_constName_2320_: *mut LeanObject,
    mut v___y_2321_: *mut LeanObject,
    mut v___y_2322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2328_: u8 = 0;
    let mut v_levelParams_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2336_: u8 = 0;
    let mut v_a_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2340_: u8 = 0;
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2344_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_constName_2320_);
                v___x_2324_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_constName_2320_, v___y_2321_, v___y_2322_);
                if lean_obj_tag(v___x_2324_) == 0 {
                    v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
                    v_isSharedCheck_2336_ = (!lean_is_exclusive(v___x_2324_)) as u8;
                    if v_isSharedCheck_2336_ == 0 {
                        v___x_2327_ = v___x_2324_;
                        v_isShared_2328_ = v_isSharedCheck_2336_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2325_);
                        lean_dec(v___x_2324_);
                        v___x_2327_ = lean_box(0);
                        v_isShared_2328_ = v_isSharedCheck_2336_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_constName_2320_);
                    v_a_2337_ = lean_ctor_get(v___x_2324_, 0);
                    v_isSharedCheck_2344_ = (!lean_is_exclusive(v___x_2324_)) as u8;
                    if v_isSharedCheck_2344_ == 0 {
                        v___x_2339_ = v___x_2324_;
                        v_isShared_2340_ = v_isSharedCheck_2344_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2337_);
                        lean_dec(v___x_2324_);
                        v___x_2339_ = lean_box(0);
                        v_isShared_2340_ = v_isSharedCheck_2344_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_2329_ = lean_ctor_get(v_a_2325_, 1);
                lean_inc(v_levelParams_2329_);
                lean_dec(v_a_2325_);
                v___x_2330_ = lean_box(0);
                v___x_2331_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_levelParams_2329_, v___x_2330_);
                v___x_2332_ = l_Lean_mkConst(v_constName_2320_, v___x_2331_);
                if v_isShared_2328_ == 0 {
                    lean_ctor_set(v___x_2327_, 0, v___x_2332_);
                    v___x_2334_ = v___x_2327_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
                    v___x_2334_ = v_reuseFailAlloc_2335_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2334_;
            }
            3 => {
                if v_isShared_2340_ == 0 {
                    v___x_2342_ = v___x_2339_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
                    v___x_2342_ = v_reuseFailAlloc_2343_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2342_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_constName_2345_: *mut LeanObject,
    mut v___y_2346_: *mut LeanObject,
    mut v___y_2347_: *mut LeanObject,
    mut v___y_2348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2349_: *mut LeanObject = core::ptr::null_mut();
    v_res_2349_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2(v_constName_2345_, v___y_2346_, v___y_2347_);
    lean_dec(v___y_2347_);
    lean_dec_ref(v___y_2346_);
    return v_res_2349_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(
    mut v_t_2350_: *mut LeanObject,
    mut v___y_2351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_2355_: u8 = 0;
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2370_: u8 = 0;
    let mut v_enabled_2371_: u8 = 0;
    let mut v_assignment_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2377_: u8 = 0;
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2388_: u8 = 0;
    let mut v_isSharedCheck_2389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2353_ = lean_st_ref_get(v___y_2351_);
                v_infoState_2354_ = lean_ctor_get(v___x_2353_, 7);
                lean_inc_ref(v_infoState_2354_);
                lean_dec(v___x_2353_);
                v_enabled_2355_ = lean_ctor_get_uint8(
                    v_infoState_2354_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_2354_);
                if v_enabled_2355_ == 0 {
                    lean_dec_ref(v_t_2350_);
                    v___x_2356_ = lean_box(0);
                    v___x_2357_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2357_, 0, v___x_2356_);
                    return v___x_2357_;
                } else {
                    v___x_2358_ = lean_st_ref_take(v___y_2351_);
                    v_infoState_2359_ = lean_ctor_get(v___x_2358_, 7);
                    v_env_2360_ = lean_ctor_get(v___x_2358_, 0);
                    v_nextMacroScope_2361_ = lean_ctor_get(v___x_2358_, 1);
                    v_ngen_2362_ = lean_ctor_get(v___x_2358_, 2);
                    v_auxDeclNGen_2363_ = lean_ctor_get(v___x_2358_, 3);
                    v_traceState_2364_ = lean_ctor_get(v___x_2358_, 4);
                    v_cache_2365_ = lean_ctor_get(v___x_2358_, 5);
                    v_messages_2366_ = lean_ctor_get(v___x_2358_, 6);
                    v_snapshotTasks_2367_ = lean_ctor_get(v___x_2358_, 8);
                    v_isSharedCheck_2389_ = (!lean_is_exclusive(v___x_2358_)) as u8;
                    if v_isSharedCheck_2389_ == 0 {
                        v___x_2369_ = v___x_2358_;
                        v_isShared_2370_ = v_isSharedCheck_2389_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_2367_);
                        lean_inc(v_infoState_2359_);
                        lean_inc(v_messages_2366_);
                        lean_inc(v_cache_2365_);
                        lean_inc(v_traceState_2364_);
                        lean_inc(v_auxDeclNGen_2363_);
                        lean_inc(v_ngen_2362_);
                        lean_inc(v_nextMacroScope_2361_);
                        lean_inc(v_env_2360_);
                        lean_dec(v___x_2358_);
                        v___x_2369_ = lean_box(0);
                        v_isShared_2370_ = v_isSharedCheck_2389_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_enabled_2371_ = lean_ctor_get_uint8(
                    v_infoState_2359_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_2372_ = lean_ctor_get(v_infoState_2359_, 0);
                v_lazyAssignment_2373_ = lean_ctor_get(v_infoState_2359_, 1);
                v_trees_2374_ = lean_ctor_get(v_infoState_2359_, 2);
                v_isSharedCheck_2388_ = (!lean_is_exclusive(v_infoState_2359_)) as u8;
                if v_isSharedCheck_2388_ == 0 {
                    v___x_2376_ = v_infoState_2359_;
                    v_isShared_2377_ = v_isSharedCheck_2388_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_trees_2374_);
                    lean_inc(v_lazyAssignment_2373_);
                    lean_inc(v_assignment_2372_);
                    lean_dec(v_infoState_2359_);
                    v___x_2376_ = lean_box(0);
                    v_isShared_2377_ = v_isSharedCheck_2388_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2378_ = l_Lean_PersistentArray_push___redArg(v_trees_2374_, v_t_2350_);
                if v_isShared_2377_ == 0 {
                    lean_ctor_set(v___x_2376_, 2, v___x_2378_);
                    v___x_2380_ = v___x_2376_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_assignment_2372_);
                    lean_ctor_set(v_reuseFailAlloc_2387_, 1, v_lazyAssignment_2373_);
                    lean_ctor_set(v_reuseFailAlloc_2387_, 2, v___x_2378_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2387_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_2371_,
                    );
                    v___x_2380_ = v_reuseFailAlloc_2387_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2370_ == 0 {
                    lean_ctor_set(v___x_2369_, 7, v___x_2380_);
                    v___x_2382_ = v___x_2369_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_env_2360_);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_nextMacroScope_2361_);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 2, v_ngen_2362_);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 3, v_auxDeclNGen_2363_);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 4, v_traceState_2364_);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 5, v_cache_2365_);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 6, v_messages_2366_);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 7, v___x_2380_);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 8, v_snapshotTasks_2367_);
                    v___x_2382_ = v_reuseFailAlloc_2386_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2383_ = lean_st_ref_set(v___y_2351_, v___x_2382_);
                v___x_2384_ = lean_box(0);
                v___x_2385_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2385_, 0, v___x_2384_);
                return v___x_2385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg___boxed(
    mut v_t_2390_: *mut LeanObject,
    mut v___y_2391_: *mut LeanObject,
    mut v___y_2392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2393_: *mut LeanObject = core::ptr::null_mut();
    v_res_2393_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(v_t_2390_, v___y_2391_);
    lean_dec(v___y_2391_);
    return v_res_2393_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__0()
-> *mut LeanObject {
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    v___x_2394_ = lean_unsigned_to_nat(32);
    v___x_2395_ = lean_mk_empty_array_with_capacity(v___x_2394_);
    v___x_2396_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2396_, 0, v___x_2395_);
    return v___x_2396_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__1()
-> *mut LeanObject {
    let mut v___x_2397_: usize = 0;
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    v___x_2397_ = 5usize;
    v___x_2398_ = lean_unsigned_to_nat(0);
    v___x_2399_ = lean_unsigned_to_nat(32);
    v___x_2400_ = lean_mk_empty_array_with_capacity(v___x_2399_);
    v___x_2401_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__0_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__0);
    v___x_2402_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2402_, 0, v___x_2401_);
    lean_ctor_set(v___x_2402_, 1, v___x_2400_);
    lean_ctor_set(v___x_2402_, 2, v___x_2398_);
    lean_ctor_set(v___x_2402_, 3, v___x_2398_);
    lean_ctor_set_usize(v___x_2402_, 4, v___x_2397_);
    return v___x_2402_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3(
    mut v_t_2403_: *mut LeanObject,
    mut v___y_2404_: *mut LeanObject,
    mut v___y_2405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_2409_: u8 = 0;
    v___x_2407_ = lean_st_ref_get(v___y_2405_);
    v_infoState_2408_ = lean_ctor_get(v___x_2407_, 7);
    lean_inc_ref(v_infoState_2408_);
    lean_dec(v___x_2407_);
    v_enabled_2409_ = lean_ctor_get_uint8(
        v_infoState_2408_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    lean_dec_ref(v_infoState_2408_);
    if v_enabled_2409_ == 0 {
        let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_t_2403_);
        v___x_2410_ = lean_box(0);
        v___x_2411_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2411_, 0, v___x_2410_);
        return v___x_2411_;
    } else {
        let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
        v___x_2412_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__1_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__1);
        v___x_2413_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2413_, 0, v_t_2403_);
        lean_ctor_set(v___x_2413_, 1, v___x_2412_);
        v___x_2414_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(v___x_2413_, v___y_2405_);
        return v___x_2414_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___boxed(
    mut v_t_2415_: *mut LeanObject,
    mut v___y_2416_: *mut LeanObject,
    mut v___y_2417_: *mut LeanObject,
    mut v___y_2418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2419_: *mut LeanObject = core::ptr::null_mut();
    v_res_2419_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3(v_t_2415_, v___y_2416_, v___y_2417_);
    lean_dec(v___y_2417_);
    lean_dec_ref(v___y_2416_);
    return v_res_2419_;
}
pub unsafe fn l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1(
    mut v_stx_2420_: *mut LeanObject,
    mut v_n_2421_: *mut LeanObject,
    mut v_expectedType_x3f_2422_: *mut LeanObject,
    mut v___y_2423_: *mut LeanObject,
    mut v___y_2424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: u8 = 0;
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2438_: u8 = 0;
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2442_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2426_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2(v_n_2421_, v___y_2423_, v___y_2424_);
                if lean_obj_tag(v___x_2426_) == 0 {
                    v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
                    lean_inc(v_a_2427_);
                    lean_dec_ref_known(v___x_2426_, 1);
                    v___x_2428_ = lean_box(0);
                    v___x_2429_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2429_, 0, v___x_2428_);
                    lean_ctor_set(v___x_2429_, 1, v_stx_2420_);
                    v___x_2430_ = l_Lean_LocalContext_empty;
                    v___x_2431_ = 0;
                    v___x_2432_ = lean_alloc_ctor(0, 4, (2) as u32);
                    lean_ctor_set(v___x_2432_, 0, v___x_2429_);
                    lean_ctor_set(v___x_2432_, 1, v___x_2430_);
                    lean_ctor_set(v___x_2432_, 2, v_expectedType_x3f_2422_);
                    lean_ctor_set(v___x_2432_, 3, v_a_2427_);
                    lean_ctor_set_uint8(
                        v___x_2432_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v___x_2431_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2432_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                        v___x_2431_,
                    );
                    v___x_2433_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2433_, 0, v___x_2432_);
                    v___x_2434_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3(v___x_2433_, v___y_2423_, v___y_2424_);
                    return v___x_2434_;
                } else {
                    lean_dec(v_expectedType_x3f_2422_);
                    lean_dec(v_stx_2420_);
                    v_a_2435_ = lean_ctor_get(v___x_2426_, 0);
                    v_isSharedCheck_2442_ = (!lean_is_exclusive(v___x_2426_)) as u8;
                    if v_isSharedCheck_2442_ == 0 {
                        v___x_2437_ = v___x_2426_;
                        v_isShared_2438_ = v_isSharedCheck_2442_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2435_);
                        lean_dec(v___x_2426_);
                        v___x_2437_ = lean_box(0);
                        v_isShared_2438_ = v_isSharedCheck_2442_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2438_ == 0 {
                    v___x_2440_ = v___x_2437_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
                    v___x_2440_ = v_reuseFailAlloc_2441_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2440_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1___boxed(
    mut v_stx_2443_: *mut LeanObject,
    mut v_n_2444_: *mut LeanObject,
    mut v_expectedType_x3f_2445_: *mut LeanObject,
    mut v___y_2446_: *mut LeanObject,
    mut v___y_2447_: *mut LeanObject,
    mut v___y_2448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2449_: *mut LeanObject = core::ptr::null_mut();
    v_res_2449_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1(v_stx_2443_, v_n_2444_, v_expectedType_x3f_2445_, v___y_2446_, v___y_2447_);
    lean_dec(v___y_2447_);
    lean_dec_ref(v___y_2446_);
    return v_res_2449_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    v___x_2450_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2450_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    v___x_2451_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
    v___x_2452_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2452_, 0, v___x_2451_);
    return v___x_2452_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    v___x_2453_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
    v___x_2454_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2454_, 0, v___x_2453_);
    lean_ctor_set(v___x_2454_, 1, v___x_2453_);
    return v___x_2454_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    v___x_2456_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
    v___x_2457_ = l_Lean_stringToMessageData(v___x_2456_);
    return v___x_2457_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    v___x_2459_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
    v___x_2460_ = l_Lean_stringToMessageData(v___x_2459_);
    return v___x_2460_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> u64 {
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: u64 = 0;
    v___x_2467_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
    v___x_2468_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2467_);
    return v___x_2468_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2469_: u64 = 0;
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    v___x_2469_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
    v___x_2470_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
    v___x_2471_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_2471_, 0, v___x_2470_);
    lean_ctor_set_uint64(
        v___x_2471_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2469_,
    );
    return v___x_2471_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    v___x_2472_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2472_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    v___x_2473_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
    v___x_2474_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2474_, 0, v___x_2473_);
    return v___x_2474_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    v___x_2475_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
    v___x_2476_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_2476_, 0, v___x_2475_);
    lean_ctor_set(v___x_2476_, 1, v___x_2475_);
    lean_ctor_set(v___x_2476_, 2, v___x_2475_);
    lean_ctor_set(v___x_2476_, 3, v___x_2475_);
    lean_ctor_set(v___x_2476_, 4, v___x_2475_);
    lean_ctor_set(v___x_2476_, 5, v___x_2475_);
    return v___x_2476_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    v___x_2477_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
    v___x_2478_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2478_, 0, v___x_2477_);
    lean_ctor_set(v___x_2478_, 1, v___x_2477_);
    lean_ctor_set(v___x_2478_, 2, v___x_2477_);
    lean_ctor_set(v___x_2478_, 3, v___x_2477_);
    lean_ctor_set(v___x_2478_, 4, v___x_2477_);
    return v___x_2478_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    v___x_2482_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
    v___x_2483_ = l_Lean_stringToMessageData(v___x_2482_);
    return v___x_2483_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    v___x_2485_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
    v___x_2486_ = l_Lean_stringToMessageData(v___x_2485_);
    return v___x_2486_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    v___x_2489_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
    v___x_2490_ = l_Lean_stringToMessageData(v___x_2489_);
    return v___x_2490_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    v___x_2492_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
    v___x_2493_ = l_Lean_stringToMessageData(v___x_2492_);
    return v___x_2493_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    v___x_2495_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
    v___x_2496_ = l_Lean_stringToMessageData(v___x_2495_);
    return v___x_2496_;
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(
    mut v___x_2497_: *mut LeanObject,
    mut v___x_2498_: *mut LeanObject,
    mut v___x_2499_: *mut LeanObject,
    mut v___x_2500_: *mut LeanObject,
    mut v___x_2501_: *mut LeanObject,
    mut v___x_2502_: *mut LeanObject,
    mut v___x_2503_: *mut LeanObject,
    mut v_decl_2504_: *mut LeanObject,
    mut v_stx_2505_: *mut LeanObject,
    mut v_kind_2506_: u8,
    mut v___y_2507_: *mut LeanObject,
    mut v___y_2508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dflt_2512_: u8 = 0;
    let mut v___y_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2526_: u8 = 0;
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2540_: u8 = 0;
    let mut v_unused_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2544_: u8 = 0;
    let mut v___y_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2548_: u8 = 0;
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: u8 = 0;
    let mut v___x_2569_: u8 = 0;
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: usize = 0;
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: u8 = 0;
    let mut v_a_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: u8 = 0;
    let mut v_a_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2599_: u8 = 0;
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2603_: u8 = 0;
    let mut v_a_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2607_: u8 = 0;
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2611_: u8 = 0;
    let mut v___y_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2624_: u8 = 0;
    let mut v___y_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2633_: u8 = 0;
    let mut v___y_2634_: u8 = 0;
    let mut v___y_2635_: u8 = 0;
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2646_: u8 = 0;
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: u8 = 0;
    let mut v___y_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: u8 = 0;
    let mut v___x_2654_: u8 = 0;
    let mut v___x_2655_: u8 = 0;
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shortName_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2669_: u8 = 0;
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2680_: u8 = 0;
    let mut v_unused_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: u8 = 0;
    let mut v___x_2683_: u8 = 0;
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2510_ = lean_unsigned_to_nat(1);
                v___x_2511_ = l_Lean_Syntax_getArg(v_stx_2505_, v___x_2510_);
                v_dflt_2512_ = l_Lean_Syntax_isNone(v___x_2511_);
                lean_dec(v___x_2511_);
                v___x_2682_ = 0;
                v___x_2683_ = l_Lean_instBEqAttributeKind_beq(v_kind_2506_, v___x_2682_);
                if v___x_2683_ == 0 {
                    lean_dec(v_stx_2505_);
                    lean_dec(v_decl_2504_);
                    lean_dec(v___x_2503_);
                    lean_dec(v___x_2502_);
                    lean_dec(v___x_2501_);
                    lean_dec_ref(v___x_2500_);
                    lean_dec_ref(v___x_2499_);
                    lean_dec_ref(v___x_2498_);
                    lean_dec(v___x_2497_);
                    v___x_2684_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
                    v___x_2685_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_2684_, v___y_2507_, v___y_2508_);
                    return v___x_2685_;
                } else {
                    state = 15;
                    continue;
                }
            }
            1 => {
                v___x_2515_ = lean_st_ref_take(v___y_2514_);
                v_env_2516_ = lean_ctor_get(v___x_2515_, 0);
                v_nextMacroScope_2517_ = lean_ctor_get(v___x_2515_, 1);
                v_ngen_2518_ = lean_ctor_get(v___x_2515_, 2);
                v_auxDeclNGen_2519_ = lean_ctor_get(v___x_2515_, 3);
                v_traceState_2520_ = lean_ctor_get(v___x_2515_, 4);
                v_messages_2521_ = lean_ctor_get(v___x_2515_, 6);
                v_infoState_2522_ = lean_ctor_get(v___x_2515_, 7);
                v_snapshotTasks_2523_ = lean_ctor_get(v___x_2515_, 8);
                v_isSharedCheck_2540_ = (!lean_is_exclusive(v___x_2515_)) as u8;
                if v_isSharedCheck_2540_ == 0 {
                    v_unused_2541_ = lean_ctor_get(v___x_2515_, 5);
                    lean_dec(v_unused_2541_);
                    v___x_2525_ = v___x_2515_;
                    v_isShared_2526_ = v_isSharedCheck_2540_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2523_);
                    lean_inc(v_infoState_2522_);
                    lean_inc(v_messages_2521_);
                    lean_inc(v_traceState_2520_);
                    lean_inc(v_auxDeclNGen_2519_);
                    lean_inc(v_ngen_2518_);
                    lean_inc(v_nextMacroScope_2517_);
                    lean_inc(v_env_2516_);
                    lean_dec(v___x_2515_);
                    v___x_2525_ = lean_box(0);
                    v_isShared_2526_ = v_isSharedCheck_2540_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2527_ = l_Lean_Linter_EnvLinter_envLinterExt;
                v_toEnvExtension_2528_ = lean_ctor_get(v___x_2527_, 0);
                v_asyncMode_2529_ = lean_ctor_get(v_toEnvExtension_2528_, 2);
                v___x_2530_ = lean_box((v_dflt_2512_) as usize);
                v___x_2531_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2531_, 0, v_decl_2504_);
                lean_ctor_set(v___x_2531_, 1, v___x_2530_);
                v___x_2532_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_2527_,
                    v_env_2516_,
                    v___x_2531_,
                    v_asyncMode_2529_,
                    v___x_2497_,
                );
                v___x_2533_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
                if v_isShared_2526_ == 0 {
                    lean_ctor_set(v___x_2525_, 5, v___x_2533_);
                    lean_ctor_set(v___x_2525_, 0, v___x_2532_);
                    v___x_2535_ = v___x_2525_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2532_);
                    lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_nextMacroScope_2517_);
                    lean_ctor_set(v_reuseFailAlloc_2539_, 2, v_ngen_2518_);
                    lean_ctor_set(v_reuseFailAlloc_2539_, 3, v_auxDeclNGen_2519_);
                    lean_ctor_set(v_reuseFailAlloc_2539_, 4, v_traceState_2520_);
                    lean_ctor_set(v_reuseFailAlloc_2539_, 5, v___x_2533_);
                    lean_ctor_set(v_reuseFailAlloc_2539_, 6, v_messages_2521_);
                    lean_ctor_set(v_reuseFailAlloc_2539_, 7, v_infoState_2522_);
                    lean_ctor_set(v_reuseFailAlloc_2539_, 8, v_snapshotTasks_2523_);
                    v___x_2535_ = v_reuseFailAlloc_2539_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2536_ = lean_st_ref_set(v___y_2514_, v___x_2535_);
                v___x_2537_ = lean_box(0);
                v___x_2538_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2538_, 0, v___x_2537_);
                return v___x_2538_;
            }
            4 => {
                if v_a_2548_ == 0 {
                    lean_dec(v___x_2497_);
                    v___x_2549_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3);
                    v___x_2550_ = l_Lean_MessageData_ofConstName(v_decl_2504_, v___y_2544_);
                    v___x_2551_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2551_, 0, v___x_2549_);
                    lean_ctor_set(v___x_2551_, 1, v___x_2550_);
                    v___x_2552_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
                    v___x_2553_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2553_, 0, v___x_2551_);
                    lean_ctor_set(v___x_2553_, 1, v___x_2552_);
                    v___x_2554_ = l_Lean_MessageData_ofConstName(v___y_2547_, v___y_2544_);
                    v___x_2555_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2555_, 0, v___x_2553_);
                    lean_ctor_set(v___x_2555_, 1, v___x_2554_);
                    v___x_2556_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
                    v___x_2557_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2557_, 0, v___x_2555_);
                    lean_ctor_set(v___x_2557_, 1, v___x_2556_);
                    v___x_2558_ = l_Lean_MessageData_ofExpr(v___y_2543_);
                    v___x_2559_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2559_, 0, v___x_2557_);
                    lean_ctor_set(v___x_2559_, 1, v___x_2558_);
                    v___x_2560_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2560_, 0, v___x_2559_);
                    lean_ctor_set(v___x_2560_, 1, v___x_2549_);
                    v___x_2561_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_2560_, v___y_2545_, v___y_2546_);
                    return v___x_2561_;
                } else {
                    lean_dec(v___y_2547_);
                    lean_dec_ref(v___y_2543_);
                    v___y_2514_ = v___y_2546_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                lean_inc(v_decl_2504_);
                v___x_2565_ = l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0(v_decl_2504_, v___y_2563_, v___y_2564_);
                if lean_obj_tag(v___x_2565_) == 0 {
                    v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
                    lean_inc(v_a_2566_);
                    lean_dec_ref_known(v___x_2565_, 1);
                    lean_inc_ref(v___x_2500_);
                    v___x_2567_ =
                        l_Lean_Name_mkStr4(v___x_2498_, v___x_2499_, v___x_2500_, v___x_2500_);
                    v___x_2568_ = 0;
                    v___x_2569_ = 1;
                    v___x_2570_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
                    v___x_2571_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
                    v___x_2572_ = lean_unsigned_to_nat(32);
                    v___x_2573_ = lean_mk_empty_array_with_capacity(v___x_2572_);
                    v___x_2574_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3);
                    v___x_2575_ = 5usize;
                    lean_inc_n(v___x_2501_, 6);
                    v___x_2576_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                    lean_ctor_set(v___x_2576_, 0, v___x_2574_);
                    lean_ctor_set(v___x_2576_, 1, v___x_2573_);
                    lean_ctor_set(v___x_2576_, 2, v___x_2501_);
                    lean_ctor_set(v___x_2576_, 3, v___x_2501_);
                    lean_ctor_set_usize(v___x_2576_, 4, v___x_2575_);
                    v___x_2577_ = lean_box(1);
                    lean_inc_ref(v___x_2576_);
                    v___x_2578_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_2578_, 0, v___x_2571_);
                    lean_ctor_set(v___x_2578_, 1, v___x_2576_);
                    lean_ctor_set(v___x_2578_, 2, v___x_2577_);
                    v___x_2579_ = lean_mk_empty_array_with_capacity(v___x_2501_);
                    v___x_2580_ = lean_box(0);
                    lean_inc(v___x_2502_);
                    v___x_2581_ = lean_alloc_ctor(0, 7, (4) as u32);
                    lean_ctor_set(v___x_2581_, 0, v___x_2570_);
                    lean_ctor_set(v___x_2581_, 1, v___x_2502_);
                    lean_ctor_set(v___x_2581_, 2, v___x_2578_);
                    lean_ctor_set(v___x_2581_, 3, v___x_2579_);
                    lean_ctor_set(v___x_2581_, 4, v___x_2580_);
                    lean_ctor_set(v___x_2581_, 5, v___x_2501_);
                    lean_ctor_set(v___x_2581_, 6, v___x_2580_);
                    lean_ctor_set_uint8(
                        v___x_2581_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v___x_2568_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2581_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                        v___x_2568_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2581_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                        v___x_2568_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2581_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                        v___x_2569_,
                    );
                    v___x_2582_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v___x_2582_, 0, v___x_2501_);
                    lean_ctor_set(v___x_2582_, 1, v___x_2501_);
                    lean_ctor_set(v___x_2582_, 2, v___x_2501_);
                    lean_ctor_set(v___x_2582_, 3, v___x_2501_);
                    lean_ctor_set(v___x_2582_, 4, v___x_2571_);
                    lean_ctor_set(v___x_2582_, 5, v___x_2571_);
                    lean_ctor_set(v___x_2582_, 6, v___x_2571_);
                    lean_ctor_set(v___x_2582_, 7, v___x_2571_);
                    lean_ctor_set(v___x_2582_, 8, v___x_2571_);
                    lean_ctor_set(v___x_2582_, 9, v___x_2571_);
                    v___x_2583_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
                    v___x_2584_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
                    v___x_2585_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_2585_, 0, v___x_2582_);
                    lean_ctor_set(v___x_2585_, 1, v___x_2583_);
                    lean_ctor_set(v___x_2585_, 2, v___x_2502_);
                    lean_ctor_set(v___x_2585_, 3, v___x_2576_);
                    lean_ctor_set(v___x_2585_, 4, v___x_2584_);
                    v___x_2586_ = lean_st_mk_ref(v___x_2585_);
                    v___x_2587_ = l_Lean_ConstantInfo_type(v_a_2566_);
                    lean_dec(v_a_2566_);
                    v___x_2588_ = lean_box(0);
                    lean_inc(v___x_2567_);
                    v___x_2589_ = l_Lean_mkConst(v___x_2567_, v___x_2588_);
                    lean_inc_ref(v___x_2587_);
                    v___x_2590_ = l_Lean_Meta_isExprDefEq(
                        v___x_2587_,
                        v___x_2589_,
                        v___x_2581_,
                        v___x_2586_,
                        v___y_2563_,
                        v___y_2564_,
                    );
                    lean_dec_ref_known(v___x_2581_, 7);
                    if lean_obj_tag(v___x_2590_) == 0 {
                        v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
                        lean_inc(v_a_2591_);
                        lean_dec_ref_known(v___x_2590_, 1);
                        v___x_2592_ = lean_st_ref_get(v___x_2586_);
                        lean_dec(v___x_2586_);
                        lean_dec(v___x_2592_);
                        v___x_2593_ = (lean_unbox(v_a_2591_) as u8);
                        lean_dec(v_a_2591_);
                        v___y_2543_ = v___x_2587_;
                        v___y_2544_ = v___x_2568_;
                        v___y_2545_ = v___y_2563_;
                        v___y_2546_ = v___y_2564_;
                        v___y_2547_ = v___x_2567_;
                        v_a_2548_ = v___x_2593_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_2586_);
                        if lean_obj_tag(v___x_2590_) == 0 {
                            v_a_2594_ = lean_ctor_get(v___x_2590_, 0);
                            lean_inc(v_a_2594_);
                            lean_dec_ref_known(v___x_2590_, 1);
                            v___x_2595_ = (lean_unbox(v_a_2594_) as u8);
                            lean_dec(v_a_2594_);
                            v___y_2543_ = v___x_2587_;
                            v___y_2544_ = v___x_2568_;
                            v___y_2545_ = v___y_2563_;
                            v___y_2546_ = v___y_2564_;
                            v___y_2547_ = v___x_2567_;
                            v_a_2548_ = v___x_2595_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec_ref(v___x_2587_);
                            lean_dec(v___x_2567_);
                            lean_dec(v_decl_2504_);
                            lean_dec(v___x_2497_);
                            v_a_2596_ = lean_ctor_get(v___x_2590_, 0);
                            v_isSharedCheck_2603_ = (!lean_is_exclusive(v___x_2590_)) as u8;
                            if v_isSharedCheck_2603_ == 0 {
                                v___x_2598_ = v___x_2590_;
                                v_isShared_2599_ = v_isSharedCheck_2603_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_2596_);
                                lean_dec(v___x_2590_);
                                v___x_2598_ = lean_box(0);
                                v_isShared_2599_ = v_isSharedCheck_2603_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_decl_2504_);
                    lean_dec(v___x_2502_);
                    lean_dec(v___x_2501_);
                    lean_dec_ref(v___x_2500_);
                    lean_dec_ref(v___x_2499_);
                    lean_dec_ref(v___x_2498_);
                    lean_dec(v___x_2497_);
                    v_a_2604_ = lean_ctor_get(v___x_2565_, 0);
                    v_isSharedCheck_2611_ = (!lean_is_exclusive(v___x_2565_)) as u8;
                    if v_isSharedCheck_2611_ == 0 {
                        v___x_2606_ = v___x_2565_;
                        v_isShared_2607_ = v_isSharedCheck_2611_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2604_);
                        lean_dec(v___x_2565_);
                        v___x_2606_ = lean_box(0);
                        v_isShared_2607_ = v_isSharedCheck_2611_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_2599_ == 0 {
                    v___x_2601_ = v___x_2598_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
                    v___x_2601_ = v_reuseFailAlloc_2602_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2601_;
            }
            8 => {
                if v_isShared_2607_ == 0 {
                    v___x_2609_ = v___x_2606_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
                    v___x_2609_ = v_reuseFailAlloc_2610_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2609_;
            }
            10 => {
                lean_inc_ref(v___y_2616_);
                v___x_2617_ = l_Lean_stringToMessageData(v___y_2616_);
                v___x_2618_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2618_, 0, v___y_2613_);
                lean_ctor_set(v___x_2618_, 1, v___x_2617_);
                v___x_2619_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_2618_, v___y_2614_, v___y_2615_);
                return v___x_2619_;
            }
            11 => {
                lean_inc_ref(v___y_2625_);
                v___x_2626_ = l_Lean_stringToMessageData(v___y_2625_);
                v___x_2627_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2627_, 0, v___y_2622_);
                lean_ctor_set(v___x_2627_, 1, v___x_2626_);
                if v___y_2624_ == 0 {
                    v___x_2628_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
                    v___y_2613_ = v___x_2627_;
                    v___y_2614_ = v___y_2621_;
                    v___y_2615_ = v___y_2623_;
                    v___y_2616_ = v___x_2628_;
                    state = 10;
                    continue;
                } else {
                    v___x_2629_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
                    v___y_2613_ = v___x_2627_;
                    v___y_2614_ = v___y_2621_;
                    v___y_2615_ = v___y_2623_;
                    v___y_2616_ = v___x_2629_;
                    state = 10;
                    continue;
                }
            }
            12 => {
                v___x_2636_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
                v___x_2637_ = l_Lean_MessageData_ofConstName(v_decl_2504_, v___y_2635_);
                v___x_2638_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2638_, 0, v___x_2636_);
                lean_ctor_set(v___x_2638_, 1, v___x_2637_);
                v___x_2639_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
                v___x_2640_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2640_, 0, v___x_2638_);
                lean_ctor_set(v___x_2640_, 1, v___x_2639_);
                if v___y_2633_ == 0 {
                    v___x_2641_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
                    v___y_2621_ = v___y_2631_;
                    v___y_2622_ = v___x_2640_;
                    v___y_2623_ = v___y_2632_;
                    v___y_2624_ = v___y_2634_;
                    v___y_2625_ = v___x_2641_;
                    state = 11;
                    continue;
                } else {
                    v___x_2642_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
                    v___y_2621_ = v___y_2631_;
                    v___y_2622_ = v___x_2640_;
                    v___y_2623_ = v___y_2632_;
                    v___y_2624_ = v___y_2634_;
                    v___y_2625_ = v___x_2642_;
                    state = 11;
                    continue;
                }
            }
            13 => {
                v___x_2647_ = lean_st_ref_get(v___y_2645_);
                v_env_2648_ = lean_ctor_get(v___x_2647_, 0);
                lean_inc_ref(v_env_2648_);
                lean_dec(v___x_2647_);
                lean_inc(v_decl_2504_);
                v___x_2649_ = l_Lean_isMarkedMeta(v_env_2648_, v_decl_2504_);
                if v___y_2646_ == 0 {
                    lean_dec(v___x_2502_);
                    lean_dec(v___x_2501_);
                    lean_dec_ref(v___x_2500_);
                    lean_dec_ref(v___x_2499_);
                    lean_dec_ref(v___x_2498_);
                    lean_dec(v___x_2497_);
                    v___y_2631_ = v___y_2644_;
                    v___y_2632_ = v___y_2645_;
                    v___y_2633_ = v___y_2646_;
                    v___y_2634_ = v___x_2649_;
                    v___y_2635_ = v___y_2646_;
                    state = 12;
                    continue;
                } else {
                    if v___x_2649_ == 0 {
                        lean_dec(v___x_2502_);
                        lean_dec(v___x_2501_);
                        lean_dec_ref(v___x_2500_);
                        lean_dec_ref(v___x_2499_);
                        lean_dec_ref(v___x_2498_);
                        lean_dec(v___x_2497_);
                        v___y_2631_ = v___y_2644_;
                        v___y_2632_ = v___y_2645_;
                        v___y_2633_ = v___y_2646_;
                        v___y_2634_ = v___x_2649_;
                        v___y_2635_ = v___x_2649_;
                        state = 12;
                        continue;
                    } else {
                        v___y_2563_ = v___y_2644_;
                        v___y_2564_ = v___y_2645_;
                        state = 5;
                        continue;
                    }
                }
            }
            14 => {
                v___x_2653_ = l_Lean_isPrivateName(v_decl_2504_);
                if v___x_2653_ == 0 {
                    v___x_2654_ = 1;
                    v___y_2644_ = v___y_2651_;
                    v___y_2645_ = v___y_2652_;
                    v___y_2646_ = v___x_2654_;
                    state = 13;
                    continue;
                } else {
                    v___x_2655_ = 0;
                    v___y_2644_ = v___y_2651_;
                    v___y_2645_ = v___y_2652_;
                    v___y_2646_ = v___x_2655_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                v___x_2657_ = lean_st_ref_get(v___y_2508_);
                v_env_2658_ = lean_ctor_get(v___x_2657_, 0);
                lean_inc_ref(v_env_2658_);
                lean_dec(v___x_2657_);
                v___x_2659_ = l_Lean_Linter_EnvLinter_envLinterExt;
                v_toEnvExtension_2660_ = lean_ctor_get(v___x_2659_, 0);
                v_asyncMode_2661_ = lean_ctor_get(v_toEnvExtension_2660_, 2);
                lean_inc_n(v___x_2497_, 2);
                lean_inc(v_decl_2504_);
                v_shortName_2662_ = l_Lean_Name_updatePrefix(v_decl_2504_, v___x_2497_);
                v___x_2663_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_2503_,
                    v___x_2659_,
                    v_env_2658_,
                    v_asyncMode_2661_,
                    v___x_2497_,
                );
                v___x_2664_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2663_, v_shortName_2662_);
                lean_dec(v___x_2663_);
                if lean_obj_tag(v___x_2664_) == 1 {
                    lean_dec(v_decl_2504_);
                    lean_dec(v___x_2502_);
                    lean_dec(v___x_2501_);
                    lean_dec_ref(v___x_2500_);
                    lean_dec_ref(v___x_2499_);
                    lean_dec_ref(v___x_2498_);
                    lean_dec(v___x_2497_);
                    v_val_2665_ = lean_ctor_get(v___x_2664_, 0);
                    lean_inc(v_val_2665_);
                    lean_dec_ref_known(v___x_2664_, 1);
                    v_fst_2666_ = lean_ctor_get(v_val_2665_, 0);
                    v_isSharedCheck_2680_ = (!lean_is_exclusive(v_val_2665_)) as u8;
                    if v_isSharedCheck_2680_ == 0 {
                        v_unused_2681_ = lean_ctor_get(v_val_2665_, 1);
                        lean_dec(v_unused_2681_);
                        v___x_2668_ = v_val_2665_;
                        v_isShared_2669_ = v_isSharedCheck_2680_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_fst_2666_);
                        lean_dec(v_val_2665_);
                        v___x_2668_ = lean_box(0);
                        v_isShared_2669_ = v_isSharedCheck_2680_;
                        state = 16;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2664_);
                    lean_dec(v_shortName_2662_);
                    lean_dec(v_stx_2505_);
                    v___y_2651_ = v___y_2507_;
                    v___y_2652_ = v___y_2508_;
                    state = 14;
                    continue;
                }
            }
            16 => {
                v___x_2670_ = lean_box(0);
                v___x_2671_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1(v_stx_2505_, v_fst_2666_, v___x_2670_, v___y_2507_, v___y_2508_);
                if lean_obj_tag(v___x_2671_) == 0 {
                    lean_dec_ref_known(v___x_2671_, 1);
                    v___x_2672_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
                    v___x_2673_ = l_Lean_MessageData_ofName(v_shortName_2662_);
                    if v_isShared_2669_ == 0 {
                        lean_ctor_set_tag(v___x_2668_, 7);
                        lean_ctor_set(v___x_2668_, 1, v___x_2673_);
                        lean_ctor_set(v___x_2668_, 0, v___x_2672_);
                        v___x_2675_ = v___x_2668_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_2679_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2672_);
                        lean_ctor_set(v_reuseFailAlloc_2679_, 1, v___x_2673_);
                        v___x_2675_ = v_reuseFailAlloc_2679_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2668_);
                    lean_dec(v_shortName_2662_);
                    return v___x_2671_;
                }
            }
            17 => {
                v___x_2676_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
                v___x_2677_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2677_, 0, v___x_2675_);
                lean_ctor_set(v___x_2677_, 1, v___x_2676_);
                v___x_2678_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_2677_, v___y_2507_, v___y_2508_);
                return v___x_2678_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2____boxed(
    mut v___x_2686_: *mut LeanObject,
    mut v___x_2687_: *mut LeanObject,
    mut v___x_2688_: *mut LeanObject,
    mut v___x_2689_: *mut LeanObject,
    mut v___x_2690_: *mut LeanObject,
    mut v___x_2691_: *mut LeanObject,
    mut v___x_2692_: *mut LeanObject,
    mut v_decl_2693_: *mut LeanObject,
    mut v_stx_2694_: *mut LeanObject,
    mut v_kind_2695_: *mut LeanObject,
    mut v___y_2696_: *mut LeanObject,
    mut v___y_2697_: *mut LeanObject,
    mut v___y_2698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_2699_: u8 = 0;
    let mut v_res_2700_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_2699_ = (lean_unbox(v_kind_2695_) as u8);
    v_res_2700_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(v___x_2686_, v___x_2687_, v___x_2688_, v___x_2689_, v___x_2690_, v___x_2691_, v___x_2692_, v_decl_2693_, v_stx_2694_, v_kind_boxed_2699_, v___y_2696_, v___y_2697_);
    lean_dec(v___y_2697_);
    lean_dec_ref(v___y_2696_);
    return v_res_2700_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    v___x_2702_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
    v___x_2703_ = l_Lean_stringToMessageData(v___x_2702_);
    return v___x_2703_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    v___x_2705_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
    v___x_2706_ = l_Lean_stringToMessageData(v___x_2705_);
    return v___x_2706_;
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(
    mut v___x_2707_: *mut LeanObject,
    mut v_decl_2708_: *mut LeanObject,
    mut v___y_2709_: *mut LeanObject,
    mut v___y_2710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    v___x_2712_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
    v___x_2713_ = l_Lean_MessageData_ofName(v___x_2707_);
    v___x_2714_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2714_, 0, v___x_2712_);
    lean_ctor_set(v___x_2714_, 1, v___x_2713_);
    v___x_2715_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
    v___x_2716_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2716_, 0, v___x_2714_);
    lean_ctor_set(v___x_2716_, 1, v___x_2715_);
    v___x_2717_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_2716_, v___y_2709_, v___y_2710_);
    return v___x_2717_;
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2____boxed(
    mut v___x_2718_: *mut LeanObject,
    mut v_decl_2719_: *mut LeanObject,
    mut v___y_2720_: *mut LeanObject,
    mut v___y_2721_: *mut LeanObject,
    mut v___y_2722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2723_: *mut LeanObject = core::ptr::null_mut();
    v_res_2723_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(v___x_2718_, v_decl_2719_, v___y_2720_, v___y_2721_);
    lean_dec(v___y_2721_);
    lean_dec_ref(v___y_2720_);
    lean_dec(v_decl_2719_);
    return v_res_2723_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    v___x_2780_ = lean_unsigned_to_nat(3913590394);
    v___x_2781_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
    v___x_2782_ = l_Lean_Name_num___override(v___x_2781_, v___x_2780_);
    return v___x_2782_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    v___x_2784_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
    v___x_2785_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
    v___x_2786_ = l_Lean_Name_str___override(v___x_2785_, v___x_2784_);
    return v___x_2786_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    v___x_2788_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
    v___x_2789_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
    v___x_2790_ = l_Lean_Name_str___override(v___x_2789_, v___x_2788_);
    return v___x_2790_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    v___x_2791_ = lean_unsigned_to_nat(2);
    v___x_2792_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
    v___x_2793_ = l_Lean_Name_num___override(v___x_2792_, v___x_2791_);
    return v___x_2793_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2799_: u8 = 0;
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    v___x_2799_ = 0;
    v___x_2800_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
    v___x_2801_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
    v___x_2802_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
    v___x_2803_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_2803_, 0, v___x_2802_);
    lean_ctor_set(v___x_2803_, 1, v___x_2801_);
    lean_ctor_set(v___x_2803_, 2, v___x_2800_);
    lean_ctor_set_uint8(
        v___x_2803_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_2799_,
    );
    return v___x_2803_;
}
pub unsafe fn _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    v___f_2804_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
    v___f_2805_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
    v___x_2806_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
    v___x_2807_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2807_, 0, v___x_2806_);
    lean_ctor_set(v___x_2807_, 1, v___f_2805_);
    lean_ctor_set(v___x_2807_, 2, v___f_2804_);
    return v___x_2807_;
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    v___x_2809_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
    v___x_2810_ = l_Lean_registerBuiltinAttribute(v___x_2809_);
    return v___x_2810_;
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2____boxed(
    mut v_a_2811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2812_: *mut LeanObject = core::ptr::null_mut();
    v_res_2812_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_();
    return v_res_2812_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b1_2813_: *mut LeanObject,
    mut v_constName_2814_: *mut LeanObject,
    mut v___y_2815_: *mut LeanObject,
    mut v___y_2816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    v___x_2818_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_2814_, v___y_2815_, v___y_2816_);
    return v___x_2818_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b1_2819_: *mut LeanObject,
    mut v_constName_2820_: *mut LeanObject,
    mut v___y_2821_: *mut LeanObject,
    mut v___y_2822_: *mut LeanObject,
    mut v___y_2823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2824_: *mut LeanObject = core::ptr::null_mut();
    v_res_2824_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b1_2819_, v_constName_2820_, v___y_2821_, v___y_2822_);
    lean_dec(v___y_2822_);
    lean_dec_ref(v___y_2821_);
    return v_res_2824_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7(
    mut v_t_2825_: *mut LeanObject,
    mut v___y_2826_: *mut LeanObject,
    mut v___y_2827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    v___x_2829_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(v_t_2825_, v___y_2827_);
    return v___x_2829_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7___boxed(
    mut v_t_2830_: *mut LeanObject,
    mut v___y_2831_: *mut LeanObject,
    mut v___y_2832_: *mut LeanObject,
    mut v___y_2833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2834_: *mut LeanObject = core::ptr::null_mut();
    v_res_2834_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7(v_t_2830_, v___y_2831_, v___y_2832_);
    lean_dec(v___y_2832_);
    lean_dec_ref(v___y_2831_);
    return v_res_2834_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_00_u03b1_2835_: *mut LeanObject,
    mut v_ref_2836_: *mut LeanObject,
    mut v_constName_2837_: *mut LeanObject,
    mut v___y_2838_: *mut LeanObject,
    mut v___y_2839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    v___x_2841_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_2836_, v_constName_2837_, v___y_2838_, v___y_2839_);
    return v___x_2841_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_2842_: *mut LeanObject,
    mut v_ref_2843_: *mut LeanObject,
    mut v_constName_2844_: *mut LeanObject,
    mut v___y_2845_: *mut LeanObject,
    mut v___y_2846_: *mut LeanObject,
    mut v___y_2847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2848_: *mut LeanObject = core::ptr::null_mut();
    v_res_2848_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b1_2842_, v_ref_2843_, v_constName_2844_, v___y_2845_, v___y_2846_);
    lean_dec(v___y_2846_);
    lean_dec_ref(v___y_2845_);
    lean_dec(v_ref_2843_);
    return v_res_2848_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b1_2849_: *mut LeanObject,
    mut v_ref_2850_: *mut LeanObject,
    mut v_msg_2851_: *mut LeanObject,
    mut v_declHint_2852_: *mut LeanObject,
    mut v___y_2853_: *mut LeanObject,
    mut v___y_2854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    v___x_2856_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2850_, v_msg_2851_, v_declHint_2852_, v___y_2853_, v___y_2854_);
    return v___x_2856_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b1_2857_: *mut LeanObject,
    mut v_ref_2858_: *mut LeanObject,
    mut v_msg_2859_: *mut LeanObject,
    mut v_declHint_2860_: *mut LeanObject,
    mut v___y_2861_: *mut LeanObject,
    mut v___y_2862_: *mut LeanObject,
    mut v___y_2863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2864_: *mut LeanObject = core::ptr::null_mut();
    v_res_2864_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2857_, v_ref_2858_, v_msg_2859_, v_declHint_2860_, v___y_2861_, v___y_2862_);
    lean_dec(v___y_2862_);
    lean_dec_ref(v___y_2861_);
    lean_dec(v_ref_2858_);
    return v_res_2864_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10(
    mut v_msg_2865_: *mut LeanObject,
    mut v_declHint_2866_: *mut LeanObject,
    mut v___y_2867_: *mut LeanObject,
    mut v___y_2868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    v___x_2870_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg(v_msg_2865_, v_declHint_2866_, v___y_2868_);
    return v___x_2870_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___boxed(
    mut v_msg_2871_: *mut LeanObject,
    mut v_declHint_2872_: *mut LeanObject,
    mut v___y_2873_: *mut LeanObject,
    mut v___y_2874_: *mut LeanObject,
    mut v___y_2875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2876_: *mut LeanObject = core::ptr::null_mut();
    v_res_2876_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10(v_msg_2871_, v_declHint_2872_, v___y_2873_, v___y_2874_);
    lean_dec(v___y_2874_);
    lean_dec_ref(v___y_2873_);
    return v_res_2876_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8(
    mut v_00_u03b1_2877_: *mut LeanObject,
    mut v_ref_2878_: *mut LeanObject,
    mut v_msg_2879_: *mut LeanObject,
    mut v___y_2880_: *mut LeanObject,
    mut v___y_2881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    v___x_2883_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ref_2878_, v_msg_2879_, v___y_2880_, v___y_2881_);
    return v___x_2883_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___boxed(
    mut v_00_u03b1_2884_: *mut LeanObject,
    mut v_ref_2885_: *mut LeanObject,
    mut v_msg_2886_: *mut LeanObject,
    mut v___y_2887_: *mut LeanObject,
    mut v___y_2888_: *mut LeanObject,
    mut v___y_2889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2890_: *mut LeanObject = core::ptr::null_mut();
    v_res_2890_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8(v_00_u03b1_2884_, v_ref_2885_, v_msg_2886_, v___y_2887_, v___y_2888_);
    lean_dec(v___y_2888_);
    lean_dec_ref(v___y_2887_);
    lean_dec(v_ref_2885_);
    return v_res_2890_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_EnvLinter_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Structure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ExtraModUses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_EnvLinter_Nolint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_EnvLinter_envLinterExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Linter_EnvLinter_envLinterExt);
    lean_dec_ref(res);
    res = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_EnvLinter_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_EnvLinter_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Structure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_InfoTree_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_ExtraModUses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Linter_EnvLinter_Nolint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_EnvLinter_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_EnvLinter_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Linter_EnvLinter_Basic(builtin);
}
