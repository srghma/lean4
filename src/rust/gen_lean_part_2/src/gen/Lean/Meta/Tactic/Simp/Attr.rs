// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Attr
// Imports: Lean.Meta.Tactic.Simp.Simproc
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq,
    lean_task_get_own, lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getKind, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_mkAtom, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Attributes::{
    l_Lean_Attribute_add, l_Lean_Attribute_erase, l_Lean_getAttrParamOptPrio,
    l_Lean_registerBuiltinAttribute,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findAsync_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_instBEqConstantKind_beq,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName, l_Lean_MessageLog_add,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey;
use crate::r#gen::Lean::Meta::Eqns::l_Lean_Meta_getEqnsFor_x3f;
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpCongrTheorems::l_Lean_Meta_getSimpCongrTheorems___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::{
    l_Lean_Meta_Origin_converse, l_Lean_Meta_Origin_key, l_Lean_Meta_Simp_ignoreEquations,
    l_Lean_Meta_Simp_unfoldEvenWithEqns___redArg, l_Lean_Meta_SimpExtension_getTheorems___redArg,
    l_Lean_Meta_SimpTheorems_eraseCore, l_Lean_Meta_SimpTheorems_isDeclToUnfold,
    l_Lean_Meta_SimpTheorems_isLemma, l_Lean_Meta_addSimpTheorem,
    l_Lean_Meta_instInhabitedSimpTheorems_default, l_Lean_Meta_mkSimpExt,
    l_Lean_Meta_simpExtensionMapRef,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    initialize_Lean_Meta_Tactic_Simp_Simproc, l_Lean_Meta_Simp_isBuiltinSimproc___redArg,
    l_Lean_Meta_Simp_isSimproc___redArg, l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName,
    runtime_initialize_Lean_Meta_Tactic_Simp_Simproc,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::l_Lean_Meta_Simp_mkContext___redArg;
use crate::r#gen::Lean::OriginalConstKind::l_Lean_getOriginalConstKind_x3f;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ScopedEnvExtension::{
    l_Lean_ScopedEnvExtension_addCore___redArg, l_Lean_ScopedEnvExtension_getState___redArg,
    l_Lean_ScopedEnvExtension_modifyState___redArg,
};
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_addDeclToUnfold___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_Meta_addDeclToUnfold___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_addDeclToUnfold___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_addDeclToUnfold___closed__1_value: leanh::LeanStringObject<26> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 23,
        m_data: [
            73, 110, 118, 97, 108, 105, 100, 32, 96, 226, 134, 144, 96, 32, 109, 111, 100, 105,
            102, 105, 101, 114, 58, 32, 96, 0,
        ],
    };
static mut l_Lean_Meta_addDeclToUnfold___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_addDeclToUnfold___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_addDeclToUnfold___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_addDeclToUnfold___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_addDeclToUnfold___closed__3_value: leanh::LeanStringObject<39> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 39,
        m_capacity: 39,
        m_length: 38,
        m_data: [
            96, 32, 105, 115, 32, 97, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32,
            110, 97, 109, 101, 32, 116, 111, 32, 98, 101, 32, 117, 110, 102, 111, 108, 100, 101,
            100, 0,
        ],
    };
static mut l_Lean_Meta_addDeclToUnfold___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_addDeclToUnfold___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_addDeclToUnfold___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_addDeclToUnfold___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_addDeclToUnfold___closed__5_value: leanh::LeanStringObject<119> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 119,
        m_capacity: 119,
        m_length: 118,
        m_data: [
            84, 104, 101, 32, 115, 105, 109, 112, 108, 105, 102, 105, 101, 114, 32, 119, 105, 108,
            108, 32, 97, 117, 116, 111, 109, 97, 116, 105, 99, 97, 108, 108, 121, 32, 117, 110,
            102, 111, 108, 100, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 115, 32, 109,
            97, 114, 107, 101, 100, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 96, 91, 115,
            105, 109, 112, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 44, 32, 98, 117,
            116, 32, 105, 116, 32, 119, 105, 108, 108, 32, 110, 111, 116, 32, 34, 114, 101, 102,
            111, 108, 100, 34, 32, 116, 104, 101, 109, 0,
        ],
    };
static mut l_Lean_Meta_addDeclToUnfold___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_addDeclToUnfold___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_addDeclToUnfold___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_addDeclToUnfold___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_addDeclToUnfold___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_addDeclToUnfold___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkSimpAttr___auto__1___closed__1_value: leanh::LeanStringObject<7> =
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
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkSimpAttr___auto__1___closed__2_value: leanh::LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkSimpAttr___auto__1___closed__3_value: leanh::LeanStringObject<10> =
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
        m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_mkSimpAttr___auto__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_mkSimpAttr___auto__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_mkSimpAttr___auto__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkSimpAttr___auto__1___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__3_value)
                as *mut leanh::LeanObject,
            8504843326314613972 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkSimpAttr___auto__1___closed__5_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkSimpAttr___auto__1___closed__6_value: leanh::LeanStringObject<19> =
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
            116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_mkSimpAttr___auto__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_mkSimpAttr___auto__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_mkSimpAttr___auto__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkSimpAttr___auto__1___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__6_value)
                as *mut leanh::LeanObject,
            17228437386856258271 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkSimpAttr___auto__1___closed__8_value: leanh::LeanStringObject<5> =
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
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkSimpAttr___auto__1___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__8_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkSimpAttr___auto__1___closed__10_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [101, 120, 97, 99, 116, 0],
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__10_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_mkSimpAttr___auto__1___closed__11_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_mkSimpAttr___auto__1___closed__11_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__11_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_mkSimpAttr___auto__1___closed__11_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__11_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkSimpAttr___auto__1___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__11_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__10_value)
                as *mut leanh::LeanObject,
            14997215300048349804 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkSimpAttr___auto__1___closed__14_value: leanh::LeanStringObject<5> =
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
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkSimpAttr___auto__1___closed__15_value: leanh::LeanStringObject<9> =
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
        m_data: [100, 101, 99, 108, 78, 97, 109, 101, 0],
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__15_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_mkSimpAttr___auto__1___closed__16_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_mkSimpAttr___auto__1___closed__16_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__16_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_mkSimpAttr___auto__1___closed__16_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__16_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__14_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkSimpAttr___auto__1___closed__16_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__16_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__15_value)
                as *mut leanh::LeanObject,
            7677164612348466033 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkSimpAttr___auto__1___closed__17_value: leanh::LeanStringObject<11> =
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
        m_data: [100, 101, 99, 108, 95, 110, 97, 109, 101, 37, 0],
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__27_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__27: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___auto__1___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_mkSimpAttr___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkSimpAttr___lam__0___closed__0_value: leanh::LeanStringObject<33> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            67, 97, 110, 110, 111, 116, 32, 97, 100, 100, 32, 96, 115, 105, 109, 112, 96, 32, 97,
            116, 116, 114, 105, 98, 117, 116, 101, 32, 116, 111, 32, 96, 0,
        ],
    };
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkSimpAttr___lam__0___closed__2_value: leanh::LeanStringObject<56> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 56,
        m_capacity: 56,
        m_length: 55,
        m_data: [
            96, 58, 32, 73, 116, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 112, 114, 111, 112,
            111, 115, 105, 116, 105, 111, 110, 32, 110, 111, 114, 32, 97, 32, 100, 101, 102, 105,
            110, 105, 116, 105, 111, 110, 32, 40, 116, 111, 32, 117, 110, 102, 111, 108, 100, 41,
            0,
        ],
    };
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkSimpAttr___lam__0___closed__4_value: leanh::LeanStringObject<165> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 165,
        m_capacity: 165,
        m_length: 164,
        m_data: [
            84, 104, 101, 32, 96, 91, 115, 105, 109, 112, 93, 96, 32, 97, 116, 116, 114, 105, 98,
            117, 116, 101, 32, 99, 97, 110, 32, 98, 101, 32, 97, 100, 100, 101, 100, 32, 116, 111,
            32, 108, 101, 109, 109, 97, 115, 32, 116, 104, 97, 116, 32, 115, 104, 111, 117, 108,
            100, 32, 98, 101, 32, 97, 117, 116, 111, 109, 97, 116, 105, 99, 97, 108, 108, 121, 32,
            117, 115, 101, 100, 32, 98, 121, 32, 116, 104, 101, 32, 115, 105, 109, 112, 108, 105,
            102, 105, 101, 114, 32, 97, 110, 100, 32, 116, 111, 32, 100, 101, 102, 105, 110, 105,
            116, 105, 111, 110, 115, 32, 116, 104, 97, 116, 32, 116, 104, 101, 32, 115, 105, 109,
            112, 108, 105, 102, 105, 101, 114, 32, 115, 104, 111, 117, 108, 100, 32, 97, 117, 116,
            111, 109, 97, 116, 105, 99, 97, 108, 108, 121, 32, 117, 110, 102, 111, 108, 100, 0,
        ],
    };
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkSimpAttr___lam__0___closed__10_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___lam__0___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkSimpAttr___lam__0___closed__15_value: leanh::LeanStringObject<9> =
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
        m_data: [115, 105, 109, 112, 80, 111, 115, 116, 0],
    };
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___lam__0___closed__15_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_mkSimpAttr___lam__0___closed__16_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_mkSimpAttr___lam__0___closed__16_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___lam__0___closed__16_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_mkSimpAttr___lam__0___closed__16_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___lam__0___closed__16_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkSimpAttr___lam__0___closed__16_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___lam__0___closed__16_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___lam__0___closed__15_value)
                as *mut leanh::LeanObject,
            11666232682930756134 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkSimpAttr___lam__0___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___lam__0___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0: u64 = 0;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__1_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__2_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__3_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__4_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__5_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__6_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__0_value: leanh::LeanStringObject<39> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 116, 104, 101, 32, 96, 91, 115, 105, 109, 112, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_registerSimpAttr___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13994041031692860867 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [115, 105, 109, 112, 108, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 116, 104, 101, 111, 114, 101, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 105, 109, 112, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9819975200604861073 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_simpExtension: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 101, 118, 97, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10924716299523037131 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [115, 121, 109, 98, 111, 108, 105, 99, 32, 101, 118, 97, 108, 117, 97, 116, 111, 114, 32, 116, 104, 101, 111, 114, 101, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [115, 101, 118, 97, 108, 83, 105, 109, 112, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6211195208831797169 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_sevalSimpExtension: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Context_mkDefault___redArg___closed__0_value:
    leanh::LeanCtorObject<7> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 32) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((100000 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((2 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        72058697861300480 as *mut leanh::LeanObject,
        1103806595073 as *mut leanh::LeanObject,
        72340172838076672 as *mut leanh::LeanObject,
        257 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Context_mkDefault___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Context_mkDefault___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Meta_addDeclToUnfold_spec__0(
    mut v_x_1781_: *mut leanh::LeanObject,
    mut v_x_1782_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_1781_) == 0 {
        if leanh::lean_obj_tag(v_x_1782_) == 0 {
            let mut v___x_1783_: u8 = 0;
            v___x_1783_ = 1;
            return v___x_1783_;
        } else {
            let mut v___x_1784_: u8 = 0;
            v___x_1784_ = 0;
            return v___x_1784_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_1782_) == 0 {
            let mut v___x_1785_: u8 = 0;
            v___x_1785_ = 0;
            return v___x_1785_;
        } else {
            let mut v_val_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1788_: u8 = 0;
            let mut v___x_1789_: u8 = 0;
            let mut v___x_1790_: u8 = 0;
            v_val_1786_ = leanh::lean_ctor_get(v_x_1781_, 0);
            v_val_1787_ = leanh::lean_ctor_get(v_x_1782_, 0);
            v___x_1788_ = (leanh::lean_unbox(v_val_1786_) as u8);
            v___x_1789_ = (leanh::lean_unbox(v_val_1787_) as u8);
            v___x_1790_ = l_Lean_instBEqConstantKind_beq(v___x_1788_, v___x_1789_);
            return v___x_1790_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Meta_addDeclToUnfold_spec__0___boxed(
    mut v_x_1791_: *mut leanh::LeanObject,
    mut v_x_1792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1793_: u8 = 0;
    let mut v_r_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1793_ =
        l_Option_instBEq_beq___at___00Lean_Meta_addDeclToUnfold_spec__0(v_x_1791_, v_x_1792_);
    leanh::lean_dec(v_x_1792_);
    leanh::lean_dec(v_x_1791_);
    v_r_1794_ = leanh::lean_box((v_res_1793_) as usize);
    return v_r_1794_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1795_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1795_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1796_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0);
    v___x_1797_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1797_, 0, v___x_1796_);
    return v___x_1797_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1798_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1);
    v___x_1799_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1799_, 0, v___x_1798_);
    leanh::lean_ctor_set(v___x_1799_, 1, v___x_1798_);
    return v___x_1799_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1800_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1);
    v___x_1801_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_1801_, 0, v___x_1800_);
    leanh::lean_ctor_set(v___x_1801_, 1, v___x_1800_);
    leanh::lean_ctor_set(v___x_1801_, 2, v___x_1800_);
    leanh::lean_ctor_set(v___x_1801_, 3, v___x_1800_);
    leanh::lean_ctor_set(v___x_1801_, 4, v___x_1800_);
    leanh::lean_ctor_set(v___x_1801_, 5, v___x_1800_);
    return v___x_1801_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(
    mut v_ext_1802_: *mut leanh::LeanObject,
    mut v_b_1803_: *mut leanh::LeanObject,
    mut v_kind_1804_: u8,
    mut v___y_1805_: *mut leanh::LeanObject,
    mut v___y_1806_: *mut leanh::LeanObject,
    mut v___y_1807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_currNamespace_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1821_: u8 = 0;
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1834_: u8 = 0;
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1842_: u8 = 0;
    let mut v_unused_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1845_: u8 = 0;
    let mut v_unused_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_1809_ = leanh::lean_ctor_get(v___y_1806_, 6);
                v___x_1810_ = lean_st_ref_take(v___y_1807_);
                v_env_1811_ = leanh::lean_ctor_get(v___x_1810_, 0);
                v_nextMacroScope_1812_ = leanh::lean_ctor_get(v___x_1810_, 1);
                v_ngen_1813_ = leanh::lean_ctor_get(v___x_1810_, 2);
                v_auxDeclNGen_1814_ = leanh::lean_ctor_get(v___x_1810_, 3);
                v_traceState_1815_ = leanh::lean_ctor_get(v___x_1810_, 4);
                v_messages_1816_ = leanh::lean_ctor_get(v___x_1810_, 6);
                v_infoState_1817_ = leanh::lean_ctor_get(v___x_1810_, 7);
                v_snapshotTasks_1818_ = leanh::lean_ctor_get(v___x_1810_, 8);
                v_isSharedCheck_1845_ = (!leanh::lean_is_exclusive(v___x_1810_)) as u8;
                if v_isSharedCheck_1845_ == 0 {
                    v_unused_1846_ = leanh::lean_ctor_get(v___x_1810_, 5);
                    leanh::lean_dec(v_unused_1846_);
                    v___x_1820_ = v___x_1810_;
                    v_isShared_1821_ = v_isSharedCheck_1845_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1818_);
                    leanh::lean_inc(v_infoState_1817_);
                    leanh::lean_inc(v_messages_1816_);
                    leanh::lean_inc(v_traceState_1815_);
                    leanh::lean_inc(v_auxDeclNGen_1814_);
                    leanh::lean_inc(v_ngen_1813_);
                    leanh::lean_inc(v_nextMacroScope_1812_);
                    leanh::lean_inc(v_env_1811_);
                    leanh::lean_dec(v___x_1810_);
                    v___x_1820_ = leanh::lean_box(0);
                    v_isShared_1821_ = v_isSharedCheck_1845_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_currNamespace_1809_);
                v___x_1822_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_1811_,
                    v_ext_1802_,
                    v_b_1803_,
                    v_kind_1804_,
                    v_currNamespace_1809_,
                );
                v___x_1823_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2);
                if v_isShared_1821_ == 0 {
                    leanh::lean_ctor_set(v___x_1820_, 5, v___x_1823_);
                    leanh::lean_ctor_set(v___x_1820_, 0, v___x_1822_);
                    v___x_1825_ = v___x_1820_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1844_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1822_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_nextMacroScope_1812_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 2, v_ngen_1813_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 3, v_auxDeclNGen_1814_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 4, v_traceState_1815_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 5, v___x_1823_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 6, v_messages_1816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 7, v_infoState_1817_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 8, v_snapshotTasks_1818_);
                    v___x_1825_ = v_reuseFailAlloc_1844_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1826_ = lean_st_ref_set(v___y_1807_, v___x_1825_);
                v___x_1827_ = lean_st_ref_take(v___y_1805_);
                v_mctx_1828_ = leanh::lean_ctor_get(v___x_1827_, 0);
                v_zetaDeltaFVarIds_1829_ = leanh::lean_ctor_get(v___x_1827_, 2);
                v_postponed_1830_ = leanh::lean_ctor_get(v___x_1827_, 3);
                v_diag_1831_ = leanh::lean_ctor_get(v___x_1827_, 4);
                v_isSharedCheck_1842_ = (!leanh::lean_is_exclusive(v___x_1827_)) as u8;
                if v_isSharedCheck_1842_ == 0 {
                    v_unused_1843_ = leanh::lean_ctor_get(v___x_1827_, 1);
                    leanh::lean_dec(v_unused_1843_);
                    v___x_1833_ = v___x_1827_;
                    v_isShared_1834_ = v_isSharedCheck_1842_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1831_);
                    leanh::lean_inc(v_postponed_1830_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1829_);
                    leanh::lean_inc(v_mctx_1828_);
                    leanh::lean_dec(v___x_1827_);
                    v___x_1833_ = leanh::lean_box(0);
                    v_isShared_1834_ = v_isSharedCheck_1842_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1835_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3);
                if v_isShared_1834_ == 0 {
                    leanh::lean_ctor_set(v___x_1833_, 1, v___x_1835_);
                    v___x_1837_ = v___x_1833_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1841_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_mctx_1828_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 1, v___x_1835_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1841_,
                        2,
                        v_zetaDeltaFVarIds_1829_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_postponed_1830_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 4, v_diag_1831_);
                    v___x_1837_ = v_reuseFailAlloc_1841_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1838_ = lean_st_ref_set(v___y_1805_, v___x_1837_);
                v___x_1839_ = leanh::lean_box(0);
                v___x_1840_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1840_, 0, v___x_1839_);
                return v___x_1840_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___boxed(
    mut v_ext_1847_: *mut leanh::LeanObject,
    mut v_b_1848_: *mut leanh::LeanObject,
    mut v_kind_1849_: *mut leanh::LeanObject,
    mut v___y_1850_: *mut leanh::LeanObject,
    mut v___y_1851_: *mut leanh::LeanObject,
    mut v___y_1852_: *mut leanh::LeanObject,
    mut v___y_1853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_1854_: u8 = 0;
    let mut v_res_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_1854_ = (leanh::lean_unbox(v_kind_1849_) as u8);
    v_res_1855_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(
        v_ext_1847_,
        v_b_1848_,
        v_kind_boxed_1854_,
        v___y_1850_,
        v___y_1851_,
        v___y_1852_,
    );
    leanh::lean_dec(v___y_1852_);
    leanh::lean_dec_ref(v___y_1851_);
    leanh::lean_dec(v___y_1850_);
    return v_res_1855_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2(
    mut v_00_u03b1_1856_: *mut leanh::LeanObject,
    mut v_00_u03b2_1857_: *mut leanh::LeanObject,
    mut v_00_u03c3_1858_: *mut leanh::LeanObject,
    mut v_ext_1859_: *mut leanh::LeanObject,
    mut v_b_1860_: *mut leanh::LeanObject,
    mut v_kind_1861_: u8,
    mut v___y_1862_: *mut leanh::LeanObject,
    mut v___y_1863_: *mut leanh::LeanObject,
    mut v___y_1864_: *mut leanh::LeanObject,
    mut v___y_1865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1867_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(
        v_ext_1859_,
        v_b_1860_,
        v_kind_1861_,
        v___y_1863_,
        v___y_1864_,
        v___y_1865_,
    );
    return v___x_1867_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___boxed(
    mut v_00_u03b1_1868_: *mut leanh::LeanObject,
    mut v_00_u03b2_1869_: *mut leanh::LeanObject,
    mut v_00_u03c3_1870_: *mut leanh::LeanObject,
    mut v_ext_1871_: *mut leanh::LeanObject,
    mut v_b_1872_: *mut leanh::LeanObject,
    mut v_kind_1873_: *mut leanh::LeanObject,
    mut v___y_1874_: *mut leanh::LeanObject,
    mut v___y_1875_: *mut leanh::LeanObject,
    mut v___y_1876_: *mut leanh::LeanObject,
    mut v___y_1877_: *mut leanh::LeanObject,
    mut v___y_1878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_1879_: u8 = 0;
    let mut v_res_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_1879_ = (leanh::lean_unbox(v_kind_1873_) as u8);
    v_res_1880_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2(
        v_00_u03b1_1868_,
        v_00_u03b2_1869_,
        v_00_u03c3_1870_,
        v_ext_1871_,
        v_b_1872_,
        v_kind_boxed_1879_,
        v___y_1874_,
        v___y_1875_,
        v___y_1876_,
        v___y_1877_,
    );
    leanh::lean_dec(v___y_1877_);
    leanh::lean_dec_ref(v___y_1876_);
    leanh::lean_dec(v___y_1875_);
    leanh::lean_dec_ref(v___y_1874_);
    return v_res_1880_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__3(
    mut v_msgData_1881_: *mut leanh::LeanObject,
    mut v___y_1882_: *mut leanh::LeanObject,
    mut v___y_1883_: *mut leanh::LeanObject,
    mut v___y_1884_: *mut leanh::LeanObject,
    mut v___y_1885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1887_ = lean_st_ref_get(v___y_1885_);
    v_env_1888_ = leanh::lean_ctor_get(v___x_1887_, 0);
    leanh::lean_inc_ref(v_env_1888_);
    leanh::lean_dec(v___x_1887_);
    v___x_1889_ = lean_st_ref_get(v___y_1883_);
    v_mctx_1890_ = leanh::lean_ctor_get(v___x_1889_, 0);
    leanh::lean_inc_ref(v_mctx_1890_);
    leanh::lean_dec(v___x_1889_);
    v_lctx_1891_ = leanh::lean_ctor_get(v___y_1882_, 2);
    v_options_1892_ = leanh::lean_ctor_get(v___y_1884_, 2);
    leanh::lean_inc_ref(v_options_1892_);
    leanh::lean_inc_ref(v_lctx_1891_);
    v___x_1893_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1893_, 0, v_env_1888_);
    leanh::lean_ctor_set(v___x_1893_, 1, v_mctx_1890_);
    leanh::lean_ctor_set(v___x_1893_, 2, v_lctx_1891_);
    leanh::lean_ctor_set(v___x_1893_, 3, v_options_1892_);
    v___x_1894_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1894_, 0, v___x_1893_);
    leanh::lean_ctor_set(v___x_1894_, 1, v_msgData_1881_);
    v___x_1895_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1895_, 0, v___x_1894_);
    return v___x_1895_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__3___boxed(
    mut v_msgData_1896_: *mut leanh::LeanObject,
    mut v___y_1897_: *mut leanh::LeanObject,
    mut v___y_1898_: *mut leanh::LeanObject,
    mut v___y_1899_: *mut leanh::LeanObject,
    mut v___y_1900_: *mut leanh::LeanObject,
    mut v___y_1901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1902_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__3(v_msgData_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
    leanh::lean_dec(v___y_1900_);
    leanh::lean_dec_ref(v___y_1899_);
    leanh::lean_dec(v___y_1898_);
    leanh::lean_dec_ref(v___y_1897_);
    return v_res_1902_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(
    mut v_msg_1903_: *mut leanh::LeanObject,
    mut v___y_1904_: *mut leanh::LeanObject,
    mut v___y_1905_: *mut leanh::LeanObject,
    mut v___y_1906_: *mut leanh::LeanObject,
    mut v___y_1907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1914_: u8 = 0;
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1909_ = leanh::lean_ctor_get(v___y_1906_, 5);
                v___x_1910_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__3(v_msg_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
                v_a_1911_ = leanh::lean_ctor_get(v___x_1910_, 0);
                v_isSharedCheck_1919_ = (!leanh::lean_is_exclusive(v___x_1910_)) as u8;
                if v_isSharedCheck_1919_ == 0 {
                    v___x_1913_ = v___x_1910_;
                    v_isShared_1914_ = v_isSharedCheck_1919_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1911_);
                    leanh::lean_dec(v___x_1910_);
                    v___x_1913_ = leanh::lean_box(0);
                    v_isShared_1914_ = v_isSharedCheck_1919_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1909_);
                v___x_1915_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1915_, 0, v_ref_1909_);
                leanh::lean_ctor_set(v___x_1915_, 1, v_a_1911_);
                if v_isShared_1914_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1913_, 1);
                    leanh::lean_ctor_set(v___x_1913_, 0, v___x_1915_);
                    v___x_1917_ = v___x_1913_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1918_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1915_);
                    v___x_1917_ = v_reuseFailAlloc_1918_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg___boxed(
    mut v_msg_1920_: *mut leanh::LeanObject,
    mut v___y_1921_: *mut leanh::LeanObject,
    mut v___y_1922_: *mut leanh::LeanObject,
    mut v___y_1923_: *mut leanh::LeanObject,
    mut v___y_1924_: *mut leanh::LeanObject,
    mut v___y_1925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1926_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(
        v_msg_1920_,
        v___y_1921_,
        v___y_1922_,
        v___y_1923_,
        v___y_1924_,
    );
    leanh::lean_dec(v___y_1924_);
    leanh::lean_dec_ref(v___y_1923_);
    leanh::lean_dec(v___y_1922_);
    leanh::lean_dec_ref(v___y_1921_);
    return v_res_1926_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1(
    mut v_ext_1927_: *mut leanh::LeanObject,
    mut v_post_1928_: u8,
    mut v_a_1929_: u8,
    mut v_attrKind_1930_: u8,
    mut v_prio_1931_: *mut leanh::LeanObject,
    mut v_as_1932_: *mut leanh::LeanObject,
    mut v_sz_1933_: usize,
    mut v_i_1934_: usize,
    mut v_b_1935_: *mut leanh::LeanObject,
    mut v___y_1936_: *mut leanh::LeanObject,
    mut v___y_1937_: *mut leanh::LeanObject,
    mut v___y_1938_: *mut leanh::LeanObject,
    mut v___y_1939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1941_: u8 = 0;
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: usize = 0;
    let mut v___x_1947_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1941_ = lean_usize_dec_lt(v_i_1934_, v_sz_1933_);
                if v___x_1941_ == 0 {
                    leanh::lean_dec(v_prio_1931_);
                    leanh::lean_dec_ref(v_ext_1927_);
                    v___x_1942_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1942_, 0, v_b_1935_);
                    return v___x_1942_;
                } else {
                    v_a_1943_ = lean_array_uget_borrowed(v_as_1932_, v_i_1934_);
                    leanh::lean_inc(v_prio_1931_);
                    leanh::lean_inc(v_a_1943_);
                    leanh::lean_inc_ref(v_ext_1927_);
                    v___x_1944_ = l_Lean_Meta_addSimpTheorem(
                        v_ext_1927_,
                        v_a_1943_,
                        v_post_1928_,
                        v_a_1929_,
                        v_attrKind_1930_,
                        v_prio_1931_,
                        v___y_1936_,
                        v___y_1937_,
                        v___y_1938_,
                        v___y_1939_,
                    );
                    if leanh::lean_obj_tag(v___x_1944_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1944_, 1);
                        v___x_1945_ = leanh::lean_box(0);
                        v___x_1946_ = 1usize;
                        v___x_1947_ = lean_usize_add(v_i_1934_, v___x_1946_);
                        v_i_1934_ = v___x_1947_;
                        v_b_1935_ = v___x_1945_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_prio_1931_);
                        leanh::lean_dec_ref(v_ext_1927_);
                        return v___x_1944_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1___boxed(
    mut v_ext_1949_: *mut leanh::LeanObject,
    mut v_post_1950_: *mut leanh::LeanObject,
    mut v_a_1951_: *mut leanh::LeanObject,
    mut v_attrKind_1952_: *mut leanh::LeanObject,
    mut v_prio_1953_: *mut leanh::LeanObject,
    mut v_as_1954_: *mut leanh::LeanObject,
    mut v_sz_1955_: *mut leanh::LeanObject,
    mut v_i_1956_: *mut leanh::LeanObject,
    mut v_b_1957_: *mut leanh::LeanObject,
    mut v___y_1958_: *mut leanh::LeanObject,
    mut v___y_1959_: *mut leanh::LeanObject,
    mut v___y_1960_: *mut leanh::LeanObject,
    mut v___y_1961_: *mut leanh::LeanObject,
    mut v___y_1962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_post_boxed_1963_: u8 = 0;
    let mut v_a_4569__boxed_1964_: u8 = 0;
    let mut v_attrKind_boxed_1965_: u8 = 0;
    let mut v_sz_boxed_1966_: usize = 0;
    let mut v_i_boxed_1967_: usize = 0;
    let mut v_res_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_post_boxed_1963_ = (leanh::lean_unbox(v_post_1950_) as u8);
    v_a_4569__boxed_1964_ = (leanh::lean_unbox(v_a_1951_) as u8);
    v_attrKind_boxed_1965_ = (leanh::lean_unbox(v_attrKind_1952_) as u8);
    v_sz_boxed_1966_ = leanh::lean_unbox_usize(v_sz_1955_);
    leanh::lean_dec(v_sz_1955_);
    v_i_boxed_1967_ = leanh::lean_unbox_usize(v_i_1956_);
    leanh::lean_dec(v_i_1956_);
    v_res_1968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1(v_ext_1949_, v_post_boxed_1963_, v_a_4569__boxed_1964_, v_attrKind_boxed_1965_, v_prio_1953_, v_as_1954_, v_sz_boxed_1966_, v_i_boxed_1967_, v_b_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
    leanh::lean_dec(v___y_1961_);
    leanh::lean_dec_ref(v___y_1960_);
    leanh::lean_dec(v___y_1959_);
    leanh::lean_dec_ref(v___y_1958_);
    leanh::lean_dec_ref(v_as_1954_);
    return v_res_1968_;
}
pub unsafe fn _init_l_Lean_Meta_addDeclToUnfold___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1973_ = l_Lean_Meta_addDeclToUnfold___closed__1;
    v___x_1974_ = l_Lean_stringToMessageData(v___x_1973_);
    return v___x_1974_;
}
pub unsafe fn _init_l_Lean_Meta_addDeclToUnfold___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1976_ = l_Lean_Meta_addDeclToUnfold___closed__3;
    v___x_1977_ = l_Lean_stringToMessageData(v___x_1976_);
    return v___x_1977_;
}
pub unsafe fn _init_l_Lean_Meta_addDeclToUnfold___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1979_ = l_Lean_Meta_addDeclToUnfold___closed__5;
    v___x_1980_ = l_Lean_stringToMessageData(v___x_1979_);
    return v___x_1980_;
}
pub unsafe fn _init_l_Lean_Meta_addDeclToUnfold___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1981_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_addDeclToUnfold___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_addDeclToUnfold___closed__6_once),
        _init_l_Lean_Meta_addDeclToUnfold___closed__6,
    );
    v___x_1982_ = l_Lean_MessageData_note(v___x_1981_);
    return v___x_1982_;
}
pub unsafe fn l_Lean_Meta_addDeclToUnfold(
    mut v_ext_1983_: *mut leanh::LeanObject,
    mut v_declName_1984_: *mut leanh::LeanObject,
    mut v_post_1985_: u8,
    mut v_inv_1986_: u8,
    mut v_prio_1987_: *mut leanh::LeanObject,
    mut v_attrKind_1988_: u8,
    mut v_a_1989_: *mut leanh::LeanObject,
    mut v_a_1990_: *mut leanh::LeanObject,
    mut v_a_1991_: *mut leanh::LeanObject,
    mut v_a_1992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: u8 = 0;
    let mut v___y_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2008_: u8 = 0;
    let mut v___x_2009_: u8 = 0;
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2014_: usize = 0;
    let mut v___x_2015_: usize = 0;
    let mut v___x_2016_: u8 = 0;
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2022_: u8 = 0;
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2027_: u8 = 0;
    let mut v___x_2028_: u8 = 0;
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2038_: u8 = 0;
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2043_: u8 = 0;
    let mut v_unused_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2046_: u8 = 0;
    let mut v_isSharedCheck_2047_: u8 = 0;
    let mut v_unused_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2052_: u8 = 0;
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2056_: u8 = 0;
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2067_: u8 = 0;
    let mut v_unused_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2073_: u8 = 0;
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2077_: u8 = 0;
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2083_: u8 = 0;
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2088_: u8 = 0;
    let mut v_unused_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2091_: u8 = 0;
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: u8 = 0;
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2106_: u8 = 0;
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2110_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1994_ = lean_st_ref_get(v_a_1992_);
                v_env_1995_ = leanh::lean_ctor_get(v___x_1994_, 0);
                leanh::lean_inc_ref(v_env_1995_);
                leanh::lean_dec(v___x_1994_);
                leanh::lean_inc(v_declName_1984_);
                v___x_1996_ = l_Lean_getOriginalConstKind_x3f(v_env_1995_, v_declName_1984_);
                v___x_1997_ = l_Lean_Meta_addDeclToUnfold___closed__0;
                v___x_1998_ = l_Option_instBEq_beq___at___00Lean_Meta_addDeclToUnfold_spec__0(
                    v___x_1996_,
                    v___x_1997_,
                );
                leanh::lean_dec(v___x_1996_);
                if v___x_1998_ == 0 {
                    leanh::lean_dec(v_prio_1987_);
                    leanh::lean_dec(v_declName_1984_);
                    leanh::lean_dec_ref(v_ext_1983_);
                    v___x_2092_ = leanh::lean_box((v___x_1998_) as usize);
                    v___x_2093_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2093_, 0, v___x_2092_);
                    return v___x_2093_;
                } else {
                    if v_inv_1986_ == 0 {
                        v___y_2000_ = v_a_1989_;
                        v___y_2001_ = v_a_1990_;
                        v___y_2002_ = v_a_1991_;
                        v___y_2003_ = v_a_1992_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_prio_1987_);
                        leanh::lean_dec_ref(v_ext_1983_);
                        v___x_2094_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_addDeclToUnfold___closed__2),
                            core::ptr::addr_of_mut!(l_Lean_Meta_addDeclToUnfold___closed__2_once),
                            _init_l_Lean_Meta_addDeclToUnfold___closed__2,
                        );
                        v___x_2095_ = 0;
                        v___x_2096_ = l_Lean_MessageData_ofConstName(v_declName_1984_, v___x_2095_);
                        v___x_2097_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2097_, 0, v___x_2094_);
                        leanh::lean_ctor_set(v___x_2097_, 1, v___x_2096_);
                        v___x_2098_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_addDeclToUnfold___closed__4),
                            core::ptr::addr_of_mut!(l_Lean_Meta_addDeclToUnfold___closed__4_once),
                            _init_l_Lean_Meta_addDeclToUnfold___closed__4,
                        );
                        v___x_2099_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2099_, 0, v___x_2097_);
                        leanh::lean_ctor_set(v___x_2099_, 1, v___x_2098_);
                        v___x_2100_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_addDeclToUnfold___closed__7),
                            core::ptr::addr_of_mut!(l_Lean_Meta_addDeclToUnfold___closed__7_once),
                            _init_l_Lean_Meta_addDeclToUnfold___closed__7,
                        );
                        v___x_2101_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2101_, 0, v___x_2099_);
                        leanh::lean_ctor_set(v___x_2101_, 1, v___x_2100_);
                        v___x_2102_ =
                            l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(
                                v___x_2101_,
                                v_a_1989_,
                                v_a_1990_,
                                v_a_1991_,
                                v_a_1992_,
                            );
                        v_a_2103_ = leanh::lean_ctor_get(v___x_2102_, 0);
                        v_isSharedCheck_2110_ =
                            (!leanh::lean_is_exclusive(v___x_2102_)) as u8;
                        if v_isSharedCheck_2110_ == 0 {
                            v___x_2105_ = v___x_2102_;
                            v_isShared_2106_ = v_isSharedCheck_2110_;
                            state = 19;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2103_);
                            leanh::lean_dec(v___x_2102_);
                            v___x_2105_ = leanh::lean_box(0);
                            v_isShared_2106_ = v_isSharedCheck_2110_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_declName_1984_);
                v___x_2004_ =
                    l_Lean_Meta_Simp_ignoreEquations(v_declName_1984_, v___y_2002_, v___y_2003_);
                if leanh::lean_obj_tag(v___x_2004_) == 0 {
                    v_a_2005_ = leanh::lean_ctor_get(v___x_2004_, 0);
                    v_isSharedCheck_2091_ = (!leanh::lean_is_exclusive(v___x_2004_)) as u8;
                    if v_isSharedCheck_2091_ == 0 {
                        v___x_2007_ = v___x_2004_;
                        v_isShared_2008_ = v_isSharedCheck_2091_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2005_);
                        leanh::lean_dec(v___x_2004_);
                        v___x_2007_ = leanh::lean_box(0);
                        v_isShared_2008_ = v_isSharedCheck_2091_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_prio_1987_);
                    leanh::lean_dec(v_declName_1984_);
                    leanh::lean_dec_ref(v_ext_1983_);
                    return v___x_2004_;
                }
            }
            2 => {
                v___x_2009_ = (leanh::lean_unbox(v_a_2005_) as u8);
                if v___x_2009_ == 0 {
                    leanh::lean_inc(v_declName_1984_);
                    v___x_2010_ = l_Lean_Meta_getEqnsFor_x3f(
                        v_declName_1984_,
                        v___y_2000_,
                        v___y_2001_,
                        v___y_2002_,
                        v___y_2003_,
                    );
                    if leanh::lean_obj_tag(v___x_2010_) == 0 {
                        v_a_2011_ = leanh::lean_ctor_get(v___x_2010_, 0);
                        leanh::lean_inc(v_a_2011_);
                        leanh::lean_dec_ref_known(v___x_2010_, 1);
                        if leanh::lean_obj_tag(v_a_2011_) == 1 {
                            leanh::lean_del_object(v___x_2007_);
                            v_val_2012_ = leanh::lean_ctor_get(v_a_2011_, 0);
                            leanh::lean_inc(v_val_2012_);
                            leanh::lean_dec_ref_known(v_a_2011_, 1);
                            v___x_2013_ = leanh::lean_box(0);
                            v_sz_2014_ = lean_array_size(v_val_2012_);
                            v___x_2015_ = 0usize;
                            v___x_2016_ = (leanh::lean_unbox(v_a_2005_) as u8);
                            leanh::lean_dec(v_a_2005_);
                            leanh::lean_inc_ref(v_ext_1983_);
                            v___x_2017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1(v_ext_1983_, v_post_1985_, v___x_2016_, v_attrKind_1988_, v_prio_1987_, v_val_2012_, v_sz_2014_, v___x_2015_, v___x_2013_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
                            if leanh::lean_obj_tag(v___x_2017_) == 0 {
                                leanh::lean_dec_ref_known(v___x_2017_, 1);
                                leanh::lean_inc(v_declName_1984_);
                                v___x_2018_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2018_, 0, v_declName_1984_);
                                leanh::lean_ctor_set(v___x_2018_, 1, v_val_2012_);
                                leanh::lean_inc_ref(v_ext_1983_);
                                v___x_2019_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_1983_, v___x_2018_, v_attrKind_1988_, v___y_2001_, v___y_2002_, v___y_2003_);
                                v_isSharedCheck_2047_ =
                                    (!leanh::lean_is_exclusive(v___x_2019_)) as u8;
                                if v_isSharedCheck_2047_ == 0 {
                                    v_unused_2048_ = leanh::lean_ctor_get(v___x_2019_, 0);
                                    leanh::lean_dec(v_unused_2048_);
                                    v___x_2021_ = v___x_2019_;
                                    v_isShared_2022_ = v_isSharedCheck_2047_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_2019_);
                                    v___x_2021_ = leanh::lean_box(0);
                                    v_isShared_2022_ = v_isSharedCheck_2047_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_val_2012_);
                                leanh::lean_dec(v_declName_1984_);
                                leanh::lean_dec_ref(v_ext_1983_);
                                v_a_2049_ = leanh::lean_ctor_get(v___x_2017_, 0);
                                v_isSharedCheck_2056_ =
                                    (!leanh::lean_is_exclusive(v___x_2017_)) as u8;
                                if v_isSharedCheck_2056_ == 0 {
                                    v___x_2051_ = v___x_2017_;
                                    v_isShared_2052_ = v_isSharedCheck_2056_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2049_);
                                    leanh::lean_dec(v___x_2017_);
                                    v___x_2051_ = leanh::lean_box(0);
                                    v_isShared_2052_ = v_isSharedCheck_2056_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_2011_);
                            leanh::lean_dec(v_a_2005_);
                            leanh::lean_dec(v_prio_1987_);
                            if v_isShared_2008_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_2007_, 1);
                                leanh::lean_ctor_set(v___x_2007_, 0, v_declName_1984_);
                                v___x_2058_ = v___x_2007_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_2069_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2069_,
                                    0,
                                    v_declName_1984_,
                                );
                                v___x_2058_ = v_reuseFailAlloc_2069_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_2007_);
                        leanh::lean_dec(v_a_2005_);
                        leanh::lean_dec(v_prio_1987_);
                        leanh::lean_dec(v_declName_1984_);
                        leanh::lean_dec_ref(v_ext_1983_);
                        v_a_2070_ = leanh::lean_ctor_get(v___x_2010_, 0);
                        v_isSharedCheck_2077_ =
                            (!leanh::lean_is_exclusive(v___x_2010_)) as u8;
                        if v_isSharedCheck_2077_ == 0 {
                            v___x_2072_ = v___x_2010_;
                            v_isShared_2073_ = v_isSharedCheck_2077_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2070_);
                            leanh::lean_dec(v___x_2010_);
                            v___x_2072_ = leanh::lean_box(0);
                            v_isShared_2073_ = v_isSharedCheck_2077_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_2005_);
                    leanh::lean_dec(v_prio_1987_);
                    if v_isShared_2008_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2007_, 1);
                        leanh::lean_ctor_set(v___x_2007_, 0, v_declName_1984_);
                        v___x_2079_ = v___x_2007_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_2090_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_declName_1984_);
                        v___x_2079_ = v_reuseFailAlloc_2090_;
                        state = 16;
                        continue;
                    }
                }
            }
            3 => {
                leanh::lean_inc(v_declName_1984_);
                v___x_2023_ =
                    l_Lean_Meta_Simp_unfoldEvenWithEqns___redArg(v_declName_1984_, v___y_2003_);
                if leanh::lean_obj_tag(v___x_2023_) == 0 {
                    v_a_2024_ = leanh::lean_ctor_get(v___x_2023_, 0);
                    v_isSharedCheck_2046_ = (!leanh::lean_is_exclusive(v___x_2023_)) as u8;
                    if v_isSharedCheck_2046_ == 0 {
                        v___x_2026_ = v___x_2023_;
                        v_isShared_2027_ = v_isSharedCheck_2046_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2024_);
                        leanh::lean_dec(v___x_2023_);
                        v___x_2026_ = leanh::lean_box(0);
                        v_isShared_2027_ = v_isSharedCheck_2046_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2021_);
                    leanh::lean_dec(v_declName_1984_);
                    leanh::lean_dec_ref(v_ext_1983_);
                    return v___x_2023_;
                }
            }
            4 => {
                v___x_2028_ = (leanh::lean_unbox(v_a_2024_) as u8);
                leanh::lean_dec(v_a_2024_);
                if v___x_2028_ == 0 {
                    leanh::lean_del_object(v___x_2021_);
                    leanh::lean_dec(v_declName_1984_);
                    leanh::lean_dec_ref(v_ext_1983_);
                    v___x_2029_ = leanh::lean_box((v___x_1998_) as usize);
                    if v_isShared_2027_ == 0 {
                        leanh::lean_ctor_set(v___x_2026_, 0, v___x_2029_);
                        v___x_2031_ = v___x_2026_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2032_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2029_);
                        v___x_2031_ = v_reuseFailAlloc_2032_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2026_);
                    if v_isShared_2022_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2021_, 1);
                        leanh::lean_ctor_set(v___x_2021_, 0, v_declName_1984_);
                        v___x_2034_ = v___x_2021_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2045_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_declName_1984_);
                        v___x_2034_ = v_reuseFailAlloc_2045_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_2031_;
            }
            6 => {
                v___x_2035_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_1983_, v___x_2034_, v_attrKind_1988_, v___y_2001_, v___y_2002_, v___y_2003_);
                v_isSharedCheck_2043_ = (!leanh::lean_is_exclusive(v___x_2035_)) as u8;
                if v_isSharedCheck_2043_ == 0 {
                    v_unused_2044_ = leanh::lean_ctor_get(v___x_2035_, 0);
                    leanh::lean_dec(v_unused_2044_);
                    v___x_2037_ = v___x_2035_;
                    v_isShared_2038_ = v_isSharedCheck_2043_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2035_);
                    v___x_2037_ = leanh::lean_box(0);
                    v_isShared_2038_ = v_isSharedCheck_2043_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2039_ = leanh::lean_box((v___x_1998_) as usize);
                if v_isShared_2038_ == 0 {
                    leanh::lean_ctor_set(v___x_2037_, 0, v___x_2039_);
                    v___x_2041_ = v___x_2037_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2042_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
                    v___x_2041_ = v_reuseFailAlloc_2042_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2041_;
            }
            9 => {
                if v_isShared_2052_ == 0 {
                    v___x_2054_ = v___x_2051_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2055_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
                    v___x_2054_ = v_reuseFailAlloc_2055_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2054_;
            }
            11 => {
                v___x_2059_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_1983_, v___x_2058_, v_attrKind_1988_, v___y_2001_, v___y_2002_, v___y_2003_);
                v_isSharedCheck_2067_ = (!leanh::lean_is_exclusive(v___x_2059_)) as u8;
                if v_isSharedCheck_2067_ == 0 {
                    v_unused_2068_ = leanh::lean_ctor_get(v___x_2059_, 0);
                    leanh::lean_dec(v_unused_2068_);
                    v___x_2061_ = v___x_2059_;
                    v_isShared_2062_ = v_isSharedCheck_2067_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2059_);
                    v___x_2061_ = leanh::lean_box(0);
                    v_isShared_2062_ = v_isSharedCheck_2067_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2063_ = leanh::lean_box((v___x_1998_) as usize);
                if v_isShared_2062_ == 0 {
                    leanh::lean_ctor_set(v___x_2061_, 0, v___x_2063_);
                    v___x_2065_ = v___x_2061_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2066_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2063_);
                    v___x_2065_ = v_reuseFailAlloc_2066_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2065_;
            }
            14 => {
                if v_isShared_2073_ == 0 {
                    v___x_2075_ = v___x_2072_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2076_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
                    v___x_2075_ = v_reuseFailAlloc_2076_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2075_;
            }
            16 => {
                v___x_2080_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_1983_, v___x_2079_, v_attrKind_1988_, v___y_2001_, v___y_2002_, v___y_2003_);
                v_isSharedCheck_2088_ = (!leanh::lean_is_exclusive(v___x_2080_)) as u8;
                if v_isSharedCheck_2088_ == 0 {
                    v_unused_2089_ = leanh::lean_ctor_get(v___x_2080_, 0);
                    leanh::lean_dec(v_unused_2089_);
                    v___x_2082_ = v___x_2080_;
                    v_isShared_2083_ = v_isSharedCheck_2088_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2080_);
                    v___x_2082_ = leanh::lean_box(0);
                    v_isShared_2083_ = v_isSharedCheck_2088_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_2084_ = leanh::lean_box((v___x_1998_) as usize);
                if v_isShared_2083_ == 0 {
                    leanh::lean_ctor_set(v___x_2082_, 0, v___x_2084_);
                    v___x_2086_ = v___x_2082_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2087_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
                    v___x_2086_ = v_reuseFailAlloc_2087_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2086_;
            }
            19 => {
                if v_isShared_2106_ == 0 {
                    v___x_2108_ = v___x_2105_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2109_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
                    v___x_2108_ = v_reuseFailAlloc_2109_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2108_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_addDeclToUnfold___boxed(
    mut v_ext_2111_: *mut leanh::LeanObject,
    mut v_declName_2112_: *mut leanh::LeanObject,
    mut v_post_2113_: *mut leanh::LeanObject,
    mut v_inv_2114_: *mut leanh::LeanObject,
    mut v_prio_2115_: *mut leanh::LeanObject,
    mut v_attrKind_2116_: *mut leanh::LeanObject,
    mut v_a_2117_: *mut leanh::LeanObject,
    mut v_a_2118_: *mut leanh::LeanObject,
    mut v_a_2119_: *mut leanh::LeanObject,
    mut v_a_2120_: *mut leanh::LeanObject,
    mut v_a_2121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_post_boxed_2122_: u8 = 0;
    let mut v_inv_boxed_2123_: u8 = 0;
    let mut v_attrKind_boxed_2124_: u8 = 0;
    let mut v_res_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_post_boxed_2122_ = (leanh::lean_unbox(v_post_2113_) as u8);
    v_inv_boxed_2123_ = (leanh::lean_unbox(v_inv_2114_) as u8);
    v_attrKind_boxed_2124_ = (leanh::lean_unbox(v_attrKind_2116_) as u8);
    v_res_2125_ = l_Lean_Meta_addDeclToUnfold(
        v_ext_2111_,
        v_declName_2112_,
        v_post_boxed_2122_,
        v_inv_boxed_2123_,
        v_prio_2115_,
        v_attrKind_boxed_2124_,
        v_a_2117_,
        v_a_2118_,
        v_a_2119_,
        v_a_2120_,
    );
    leanh::lean_dec(v_a_2120_);
    leanh::lean_dec_ref(v_a_2119_);
    leanh::lean_dec(v_a_2118_);
    leanh::lean_dec_ref(v_a_2117_);
    return v_res_2125_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3(
    mut v_00_u03b1_2126_: *mut leanh::LeanObject,
    mut v_msg_2127_: *mut leanh::LeanObject,
    mut v___y_2128_: *mut leanh::LeanObject,
    mut v___y_2129_: *mut leanh::LeanObject,
    mut v___y_2130_: *mut leanh::LeanObject,
    mut v___y_2131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2133_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(
        v_msg_2127_,
        v___y_2128_,
        v___y_2129_,
        v___y_2130_,
        v___y_2131_,
    );
    return v___x_2133_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___boxed(
    mut v_00_u03b1_2134_: *mut leanh::LeanObject,
    mut v_msg_2135_: *mut leanh::LeanObject,
    mut v___y_2136_: *mut leanh::LeanObject,
    mut v___y_2137_: *mut leanh::LeanObject,
    mut v___y_2138_: *mut leanh::LeanObject,
    mut v___y_2139_: *mut leanh::LeanObject,
    mut v___y_2140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2141_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3(
        v_00_u03b1_2134_,
        v_msg_2135_,
        v___y_2136_,
        v___y_2137_,
        v___y_2138_,
        v___y_2139_,
    );
    leanh::lean_dec(v___y_2139_);
    leanh::lean_dec_ref(v___y_2138_);
    leanh::lean_dec(v___y_2137_);
    leanh::lean_dec_ref(v___y_2136_);
    return v_res_2141_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__12() -> *mut leanh::LeanObject
{
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2168_ = l_Lean_Meta_mkSimpAttr___auto__1___closed__10;
    v___x_2169_ = l_Lean_mkAtom(v___x_2168_);
    return v___x_2169_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__13() -> *mut leanh::LeanObject
{
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2170_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__12_once),
        _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__12,
    );
    v___x_2171_ = l_Lean_Meta_mkSimpAttr___auto__1___closed__5;
    v___x_2172_ = lean_array_push(v___x_2171_, v___x_2170_);
    return v___x_2172_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__18() -> *mut leanh::LeanObject
{
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2181_ = l_Lean_Meta_mkSimpAttr___auto__1___closed__17;
    v___x_2182_ = l_Lean_mkAtom(v___x_2181_);
    return v___x_2182_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__19() -> *mut leanh::LeanObject
{
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2183_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__18_once),
        _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__18,
    );
    v___x_2184_ = l_Lean_Meta_mkSimpAttr___auto__1___closed__5;
    v___x_2185_ = lean_array_push(v___x_2184_, v___x_2183_);
    return v___x_2185_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__20() -> *mut leanh::LeanObject
{
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2186_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__19_once),
        _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__19,
    );
    v___x_2187_ = l_Lean_Meta_mkSimpAttr___auto__1___closed__16;
    v___x_2188_ = leanh::lean_box(2);
    v___x_2189_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2189_, 0, v___x_2188_);
    leanh::lean_ctor_set(v___x_2189_, 1, v___x_2187_);
    leanh::lean_ctor_set(v___x_2189_, 2, v___x_2186_);
    return v___x_2189_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__21() -> *mut leanh::LeanObject
{
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2190_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__20_once),
        _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__20,
    );
    v___x_2191_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__13_once),
        _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__13,
    );
    v___x_2192_ = lean_array_push(v___x_2191_, v___x_2190_);
    return v___x_2192_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__22() -> *mut leanh::LeanObject
{
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2193_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__21_once),
        _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__21,
    );
    v___x_2194_ = l_Lean_Meta_mkSimpAttr___auto__1___closed__11;
    v___x_2195_ = leanh::lean_box(2);
    v___x_2196_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2196_, 0, v___x_2195_);
    leanh::lean_ctor_set(v___x_2196_, 1, v___x_2194_);
    leanh::lean_ctor_set(v___x_2196_, 2, v___x_2193_);
    return v___x_2196_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__23() -> *mut leanh::LeanObject
{
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2197_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__22_once),
        _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__22,
    );
    v___x_2198_ = l_Lean_Meta_mkSimpAttr___auto__1___closed__5;
    v___x_2199_ = lean_array_push(v___x_2198_, v___x_2197_);
    return v___x_2199_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__24() -> *mut leanh::LeanObject
{
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2200_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__23_once),
        _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__23,
    );
    v___x_2201_ = l_Lean_Meta_mkSimpAttr___auto__1___closed__9;
    v___x_2202_ = leanh::lean_box(2);
    v___x_2203_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2203_, 0, v___x_2202_);
    leanh::lean_ctor_set(v___x_2203_, 1, v___x_2201_);
    leanh::lean_ctor_set(v___x_2203_, 2, v___x_2200_);
    return v___x_2203_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__25() -> *mut leanh::LeanObject
{
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2204_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__24_once),
        _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__24,
    );
    v___x_2205_ = l_Lean_Meta_mkSimpAttr___auto__1___closed__5;
    v___x_2206_ = lean_array_push(v___x_2205_, v___x_2204_);
    return v___x_2206_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__26() -> *mut leanh::LeanObject
{
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2207_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__25_once),
        _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__25,
    );
    v___x_2208_ = l_Lean_Meta_mkSimpAttr___auto__1___closed__7;
    v___x_2209_ = leanh::lean_box(2);
    v___x_2210_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2210_, 0, v___x_2209_);
    leanh::lean_ctor_set(v___x_2210_, 1, v___x_2208_);
    leanh::lean_ctor_set(v___x_2210_, 2, v___x_2207_);
    return v___x_2210_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__27() -> *mut leanh::LeanObject
{
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2211_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__26_once),
        _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__26,
    );
    v___x_2212_ = l_Lean_Meta_mkSimpAttr___auto__1___closed__5;
    v___x_2213_ = lean_array_push(v___x_2212_, v___x_2211_);
    return v___x_2213_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__28() -> *mut leanh::LeanObject
{
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2214_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__27_once),
        _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__27,
    );
    v___x_2215_ = l_Lean_Meta_mkSimpAttr___auto__1___closed__4;
    v___x_2216_ = leanh::lean_box(2);
    v___x_2217_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2217_, 0, v___x_2216_);
    leanh::lean_ctor_set(v___x_2217_, 1, v___x_2215_);
    leanh::lean_ctor_set(v___x_2217_, 2, v___x_2214_);
    return v___x_2217_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2218_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__28_once),
        _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__28,
    );
    return v___x_2218_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2219_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2219_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2220_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0);
    v___x_2221_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2221_, 0, v___x_2220_);
    return v___x_2221_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2222_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1);
    v___x_2223_ = leanh::lean_unsigned_to_nat(0);
    v___x_2224_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2224_, 0, v___x_2223_);
    leanh::lean_ctor_set(v___x_2224_, 1, v___x_2223_);
    leanh::lean_ctor_set(v___x_2224_, 2, v___x_2223_);
    leanh::lean_ctor_set(v___x_2224_, 3, v___x_2223_);
    leanh::lean_ctor_set(v___x_2224_, 4, v___x_2222_);
    leanh::lean_ctor_set(v___x_2224_, 5, v___x_2222_);
    leanh::lean_ctor_set(v___x_2224_, 6, v___x_2222_);
    leanh::lean_ctor_set(v___x_2224_, 7, v___x_2222_);
    leanh::lean_ctor_set(v___x_2224_, 8, v___x_2222_);
    leanh::lean_ctor_set(v___x_2224_, 9, v___x_2222_);
    return v___x_2224_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2225_ = leanh::lean_unsigned_to_nat(32);
    v___x_2226_ = lean_mk_empty_array_with_capacity(v___x_2225_);
    v___x_2227_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2227_, 0, v___x_2226_);
    return v___x_2227_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2228_: usize = 0;
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2228_ = 5usize;
    v___x_2229_ = leanh::lean_unsigned_to_nat(0);
    v___x_2230_ = leanh::lean_unsigned_to_nat(32);
    v___x_2231_ = lean_mk_empty_array_with_capacity(v___x_2230_);
    v___x_2232_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3);
    v___x_2233_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2233_, 0, v___x_2232_);
    leanh::lean_ctor_set(v___x_2233_, 1, v___x_2231_);
    leanh::lean_ctor_set(v___x_2233_, 2, v___x_2229_);
    leanh::lean_ctor_set(v___x_2233_, 3, v___x_2229_);
    leanh::lean_ctor_set_usize(v___x_2233_, 4, v___x_2228_);
    return v___x_2233_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2234_ = leanh::lean_box(1);
    v___x_2235_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4);
    v___x_2236_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1);
    v___x_2237_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2237_, 0, v___x_2236_);
    leanh::lean_ctor_set(v___x_2237_, 1, v___x_2235_);
    leanh::lean_ctor_set(v___x_2237_, 2, v___x_2234_);
    return v___x_2237_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2239_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6;
    v___x_2240_ = l_Lean_stringToMessageData(v___x_2239_);
    return v___x_2240_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2242_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__8;
    v___x_2243_ = l_Lean_stringToMessageData(v___x_2242_);
    return v___x_2243_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2245_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__10;
    v___x_2246_ = l_Lean_stringToMessageData(v___x_2245_);
    return v___x_2246_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2248_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__12;
    v___x_2249_ = l_Lean_stringToMessageData(v___x_2248_);
    return v___x_2249_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2251_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__14;
    v___x_2252_ = l_Lean_stringToMessageData(v___x_2251_);
    return v___x_2252_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2254_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__16;
    v___x_2255_ = l_Lean_stringToMessageData(v___x_2254_);
    return v___x_2255_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2257_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__18;
    v___x_2258_ = l_Lean_stringToMessageData(v___x_2257_);
    return v___x_2258_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg(
    mut v_msg_2259_: *mut leanh::LeanObject,
    mut v_declHint_2260_: *mut leanh::LeanObject,
    mut v___y_2261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: u8 = 0;
    let mut v_isExporting_2266_: u8 = 0;
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: u8 = 0;
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2288_: u8 = 0;
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: u8 = 0;
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2320_: u8 = 0;
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2263_ = lean_st_ref_get(v___y_2261_);
                v_env_2264_ = leanh::lean_ctor_get(v___x_2263_, 0);
                leanh::lean_inc_ref(v_env_2264_);
                leanh::lean_dec(v___x_2263_);
                v___x_2265_ = l_Lean_Name_isAnonymous(v_declHint_2260_);
                if v___x_2265_ == 0 {
                    v_isExporting_2266_ = leanh::lean_ctor_get_uint8(
                        v_env_2264_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2266_ == 0 {
                        leanh::lean_dec_ref(v_env_2264_);
                        leanh::lean_dec(v_declHint_2260_);
                        v___x_2267_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2267_, 0, v_msg_2259_);
                        return v___x_2267_;
                    } else {
                        leanh::lean_inc_ref(v_env_2264_);
                        v___x_2268_ = l_Lean_Environment_setExporting(v_env_2264_, v___x_2265_);
                        leanh::lean_inc(v_declHint_2260_);
                        leanh::lean_inc_ref(v___x_2268_);
                        v___x_2269_ = l_Lean_Environment_contains(
                            v___x_2268_,
                            v_declHint_2260_,
                            v_isExporting_2266_,
                        );
                        if v___x_2269_ == 0 {
                            leanh::lean_dec_ref(v___x_2268_);
                            leanh::lean_dec_ref(v_env_2264_);
                            leanh::lean_dec(v_declHint_2260_);
                            v___x_2270_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2270_, 0, v_msg_2259_);
                            return v___x_2270_;
                        } else {
                            v___x_2271_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2);
                            v___x_2272_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5);
                            v___x_2273_ = l_Lean_Options_empty;
                            v___x_2274_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_2274_, 0, v___x_2268_);
                            leanh::lean_ctor_set(v___x_2274_, 1, v___x_2271_);
                            leanh::lean_ctor_set(v___x_2274_, 2, v___x_2272_);
                            leanh::lean_ctor_set(v___x_2274_, 3, v___x_2273_);
                            leanh::lean_inc(v_declHint_2260_);
                            v___x_2275_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2260_, v___x_2265_);
                            v_c_2276_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_2276_, 0, v___x_2274_);
                            leanh::lean_ctor_set(v_c_2276_, 1, v___x_2275_);
                            v___x_2277_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2264_,
                                v_declHint_2260_,
                            );
                            if leanh::lean_obj_tag(v___x_2277_) == 0 {
                                leanh::lean_dec_ref(v_env_2264_);
                                leanh::lean_dec(v_declHint_2260_);
                                v___x_2278_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7);
                                v___x_2279_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2279_, 0, v___x_2278_);
                                leanh::lean_ctor_set(v___x_2279_, 1, v_c_2276_);
                                v___x_2280_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__9);
                                v___x_2281_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2281_, 0, v___x_2279_);
                                leanh::lean_ctor_set(v___x_2281_, 1, v___x_2280_);
                                v___x_2282_ = l_Lean_MessageData_note(v___x_2281_);
                                v___x_2283_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2283_, 0, v_msg_2259_);
                                leanh::lean_ctor_set(v___x_2283_, 1, v___x_2282_);
                                v___x_2284_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2284_, 0, v___x_2283_);
                                return v___x_2284_;
                            } else {
                                v_val_2285_ = leanh::lean_ctor_get(v___x_2277_, 0);
                                v_isSharedCheck_2320_ =
                                    (!leanh::lean_is_exclusive(v___x_2277_)) as u8;
                                if v_isSharedCheck_2320_ == 0 {
                                    v___x_2287_ = v___x_2277_;
                                    v_isShared_2288_ = v_isSharedCheck_2320_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_2285_);
                                    leanh::lean_dec(v___x_2277_);
                                    v___x_2287_ = leanh::lean_box(0);
                                    v_isShared_2288_ = v_isSharedCheck_2320_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_2264_);
                    leanh::lean_dec(v_declHint_2260_);
                    v___x_2321_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2321_, 0, v_msg_2259_);
                    return v___x_2321_;
                }
            }
            1 => {
                v___x_2289_ = leanh::lean_box(0);
                v___x_2290_ = l_Lean_Environment_header(v_env_2264_);
                leanh::lean_dec_ref(v_env_2264_);
                v___x_2291_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2290_);
                v_mod_2292_ = lean_array_get(v___x_2289_, v___x_2291_, v_val_2285_);
                leanh::lean_dec(v_val_2285_);
                leanh::lean_dec_ref(v___x_2291_);
                v___x_2293_ = l_Lean_isPrivateName(v_declHint_2260_);
                leanh::lean_dec(v_declHint_2260_);
                if v___x_2293_ == 0 {
                    v___x_2294_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__11);
                    v___x_2295_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2295_, 0, v___x_2294_);
                    leanh::lean_ctor_set(v___x_2295_, 1, v_c_2276_);
                    v___x_2296_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__13);
                    v___x_2297_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2297_, 0, v___x_2295_);
                    leanh::lean_ctor_set(v___x_2297_, 1, v___x_2296_);
                    v___x_2298_ = l_Lean_MessageData_ofName(v_mod_2292_);
                    v___x_2299_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2299_, 0, v___x_2297_);
                    leanh::lean_ctor_set(v___x_2299_, 1, v___x_2298_);
                    v___x_2300_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__15);
                    v___x_2301_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2301_, 0, v___x_2299_);
                    leanh::lean_ctor_set(v___x_2301_, 1, v___x_2300_);
                    v___x_2302_ = l_Lean_MessageData_note(v___x_2301_);
                    v___x_2303_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2303_, 0, v_msg_2259_);
                    leanh::lean_ctor_set(v___x_2303_, 1, v___x_2302_);
                    if v_isShared_2288_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2287_, 0);
                        leanh::lean_ctor_set(v___x_2287_, 0, v___x_2303_);
                        v___x_2305_ = v___x_2287_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2306_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
                        v___x_2305_ = v_reuseFailAlloc_2306_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2307_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7);
                    v___x_2308_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2308_, 0, v___x_2307_);
                    leanh::lean_ctor_set(v___x_2308_, 1, v_c_2276_);
                    v___x_2309_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__17);
                    v___x_2310_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2310_, 0, v___x_2308_);
                    leanh::lean_ctor_set(v___x_2310_, 1, v___x_2309_);
                    v___x_2311_ = l_Lean_MessageData_ofName(v_mod_2292_);
                    v___x_2312_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2312_, 0, v___x_2310_);
                    leanh::lean_ctor_set(v___x_2312_, 1, v___x_2311_);
                    v___x_2313_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__19);
                    v___x_2314_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2314_, 0, v___x_2312_);
                    leanh::lean_ctor_set(v___x_2314_, 1, v___x_2313_);
                    v___x_2315_ = l_Lean_MessageData_note(v___x_2314_);
                    v___x_2316_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2316_, 0, v_msg_2259_);
                    leanh::lean_ctor_set(v___x_2316_, 1, v___x_2315_);
                    if v_isShared_2288_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2287_, 0);
                        leanh::lean_ctor_set(v___x_2287_, 0, v___x_2316_);
                        v___x_2318_ = v___x_2287_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2319_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
                        v___x_2318_ = v_reuseFailAlloc_2319_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2305_;
            }
            3 => {
                return v___x_2318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___boxed(
    mut v_msg_2322_: *mut leanh::LeanObject,
    mut v_declHint_2323_: *mut leanh::LeanObject,
    mut v___y_2324_: *mut leanh::LeanObject,
    mut v___y_2325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2326_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg(v_msg_2322_, v_declHint_2323_, v___y_2324_);
    leanh::lean_dec(v___y_2324_);
    return v_res_2326_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6(
    mut v_msg_2327_: *mut leanh::LeanObject,
    mut v_declHint_2328_: *mut leanh::LeanObject,
    mut v___y_2329_: *mut leanh::LeanObject,
    mut v___y_2330_: *mut leanh::LeanObject,
    mut v___y_2331_: *mut leanh::LeanObject,
    mut v___y_2332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2338_: u8 = 0;
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2344_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2334_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg(v_msg_2327_, v_declHint_2328_, v___y_2332_);
                v_a_2335_ = leanh::lean_ctor_get(v___x_2334_, 0);
                v_isSharedCheck_2344_ = (!leanh::lean_is_exclusive(v___x_2334_)) as u8;
                if v_isSharedCheck_2344_ == 0 {
                    v___x_2337_ = v___x_2334_;
                    v_isShared_2338_ = v_isSharedCheck_2344_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2335_);
                    leanh::lean_dec(v___x_2334_);
                    v___x_2337_ = leanh::lean_box(0);
                    v_isShared_2338_ = v_isSharedCheck_2344_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2339_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2340_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2340_, 0, v___x_2339_);
                leanh::lean_ctor_set(v___x_2340_, 1, v_a_2335_);
                if v_isShared_2338_ == 0 {
                    leanh::lean_ctor_set(v___x_2337_, 0, v___x_2340_);
                    v___x_2342_ = v___x_2337_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2343_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2340_);
                    v___x_2342_ = v_reuseFailAlloc_2343_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2342_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(
    mut v_msg_2345_: *mut leanh::LeanObject,
    mut v_declHint_2346_: *mut leanh::LeanObject,
    mut v___y_2347_: *mut leanh::LeanObject,
    mut v___y_2348_: *mut leanh::LeanObject,
    mut v___y_2349_: *mut leanh::LeanObject,
    mut v___y_2350_: *mut leanh::LeanObject,
    mut v___y_2351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2352_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6(v_msg_2345_, v_declHint_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
    leanh::lean_dec(v___y_2350_);
    leanh::lean_dec_ref(v___y_2349_);
    leanh::lean_dec(v___y_2348_);
    leanh::lean_dec_ref(v___y_2347_);
    return v_res_2352_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(
    mut v_ref_2353_: *mut leanh::LeanObject,
    mut v_msg_2354_: *mut leanh::LeanObject,
    mut v___y_2355_: *mut leanh::LeanObject,
    mut v___y_2356_: *mut leanh::LeanObject,
    mut v___y_2357_: *mut leanh::LeanObject,
    mut v___y_2358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2372_: u8 = 0;
    let mut v_cancelTk_x3f_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2374_: u8 = 0;
    let mut v_inheritedTraceOptions_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_2360_ = leanh::lean_ctor_get(v___y_2357_, 0);
    v_fileMap_2361_ = leanh::lean_ctor_get(v___y_2357_, 1);
    v_options_2362_ = leanh::lean_ctor_get(v___y_2357_, 2);
    v_currRecDepth_2363_ = leanh::lean_ctor_get(v___y_2357_, 3);
    v_maxRecDepth_2364_ = leanh::lean_ctor_get(v___y_2357_, 4);
    v_ref_2365_ = leanh::lean_ctor_get(v___y_2357_, 5);
    v_currNamespace_2366_ = leanh::lean_ctor_get(v___y_2357_, 6);
    v_openDecls_2367_ = leanh::lean_ctor_get(v___y_2357_, 7);
    v_initHeartbeats_2368_ = leanh::lean_ctor_get(v___y_2357_, 8);
    v_maxHeartbeats_2369_ = leanh::lean_ctor_get(v___y_2357_, 9);
    v_quotContext_2370_ = leanh::lean_ctor_get(v___y_2357_, 10);
    v_currMacroScope_2371_ = leanh::lean_ctor_get(v___y_2357_, 11);
    v_diag_2372_ = leanh::lean_ctor_get_uint8(
        v___y_2357_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2373_ = leanh::lean_ctor_get(v___y_2357_, 12);
    v_suppressElabErrors_2374_ = leanh::lean_ctor_get_uint8(
        v___y_2357_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2375_ = leanh::lean_ctor_get(v___y_2357_, 13);
    v_ref_2376_ = l_Lean_replaceRef(v_ref_2353_, v_ref_2365_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_2375_);
    leanh::lean_inc(v_cancelTk_x3f_2373_);
    leanh::lean_inc(v_currMacroScope_2371_);
    leanh::lean_inc(v_quotContext_2370_);
    leanh::lean_inc(v_maxHeartbeats_2369_);
    leanh::lean_inc(v_initHeartbeats_2368_);
    leanh::lean_inc(v_openDecls_2367_);
    leanh::lean_inc(v_currNamespace_2366_);
    leanh::lean_inc(v_maxRecDepth_2364_);
    leanh::lean_inc(v_currRecDepth_2363_);
    leanh::lean_inc_ref(v_options_2362_);
    leanh::lean_inc_ref(v_fileMap_2361_);
    leanh::lean_inc_ref(v_fileName_2360_);
    v___x_2377_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_2377_, 0, v_fileName_2360_);
    leanh::lean_ctor_set(v___x_2377_, 1, v_fileMap_2361_);
    leanh::lean_ctor_set(v___x_2377_, 2, v_options_2362_);
    leanh::lean_ctor_set(v___x_2377_, 3, v_currRecDepth_2363_);
    leanh::lean_ctor_set(v___x_2377_, 4, v_maxRecDepth_2364_);
    leanh::lean_ctor_set(v___x_2377_, 5, v_ref_2376_);
    leanh::lean_ctor_set(v___x_2377_, 6, v_currNamespace_2366_);
    leanh::lean_ctor_set(v___x_2377_, 7, v_openDecls_2367_);
    leanh::lean_ctor_set(v___x_2377_, 8, v_initHeartbeats_2368_);
    leanh::lean_ctor_set(v___x_2377_, 9, v_maxHeartbeats_2369_);
    leanh::lean_ctor_set(v___x_2377_, 10, v_quotContext_2370_);
    leanh::lean_ctor_set(v___x_2377_, 11, v_currMacroScope_2371_);
    leanh::lean_ctor_set(v___x_2377_, 12, v_cancelTk_x3f_2373_);
    leanh::lean_ctor_set(v___x_2377_, 13, v_inheritedTraceOptions_2375_);
    leanh::lean_ctor_set_uint8(
        v___x_2377_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_2372_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_2377_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2374_,
    );
    v___x_2378_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(
        v_msg_2354_,
        v___y_2355_,
        v___y_2356_,
        v___x_2377_,
        v___y_2358_,
    );
    leanh::lean_dec_ref_known(v___x_2377_, 14);
    return v___x_2378_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(
    mut v_ref_2379_: *mut leanh::LeanObject,
    mut v_msg_2380_: *mut leanh::LeanObject,
    mut v___y_2381_: *mut leanh::LeanObject,
    mut v___y_2382_: *mut leanh::LeanObject,
    mut v___y_2383_: *mut leanh::LeanObject,
    mut v___y_2384_: *mut leanh::LeanObject,
    mut v___y_2385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2386_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_2379_, v_msg_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
    leanh::lean_dec(v___y_2384_);
    leanh::lean_dec_ref(v___y_2383_);
    leanh::lean_dec(v___y_2382_);
    leanh::lean_dec_ref(v___y_2381_);
    leanh::lean_dec(v_ref_2379_);
    return v_res_2386_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_ref_2387_: *mut leanh::LeanObject,
    mut v_msg_2388_: *mut leanh::LeanObject,
    mut v_declHint_2389_: *mut leanh::LeanObject,
    mut v___y_2390_: *mut leanh::LeanObject,
    mut v___y_2391_: *mut leanh::LeanObject,
    mut v___y_2392_: *mut leanh::LeanObject,
    mut v___y_2393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2395_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6(v_msg_2388_, v_declHint_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
    v_a_2396_ = leanh::lean_ctor_get(v___x_2395_, 0);
    leanh::lean_inc(v_a_2396_);
    leanh::lean_dec_ref(v___x_2395_);
    v___x_2397_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_2387_, v_a_2396_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
    return v___x_2397_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_ref_2398_: *mut leanh::LeanObject,
    mut v_msg_2399_: *mut leanh::LeanObject,
    mut v_declHint_2400_: *mut leanh::LeanObject,
    mut v___y_2401_: *mut leanh::LeanObject,
    mut v___y_2402_: *mut leanh::LeanObject,
    mut v___y_2403_: *mut leanh::LeanObject,
    mut v___y_2404_: *mut leanh::LeanObject,
    mut v___y_2405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2406_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2398_, v_msg_2399_, v_declHint_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
    leanh::lean_dec(v___y_2404_);
    leanh::lean_dec_ref(v___y_2403_);
    leanh::lean_dec(v___y_2402_);
    leanh::lean_dec_ref(v___y_2401_);
    leanh::lean_dec(v_ref_2398_);
    return v_res_2406_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2408_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_2409_ = l_Lean_stringToMessageData(v___x_2408_);
    return v___x_2409_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2411_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_2412_ = l_Lean_stringToMessageData(v___x_2411_);
    return v___x_2412_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(
    mut v_ref_2413_: *mut leanh::LeanObject,
    mut v_constName_2414_: *mut leanh::LeanObject,
    mut v___y_2415_: *mut leanh::LeanObject,
    mut v___y_2416_: *mut leanh::LeanObject,
    mut v___y_2417_: *mut leanh::LeanObject,
    mut v___y_2418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: u8 = 0;
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2420_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_2421_ = 0;
    leanh::lean_inc(v_constName_2414_);
    v___x_2422_ = l_Lean_MessageData_ofConstName(v_constName_2414_, v___x_2421_);
    v___x_2423_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2423_, 0, v___x_2420_);
    leanh::lean_ctor_set(v___x_2423_, 1, v___x_2422_);
    v___x_2424_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_2425_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2425_, 0, v___x_2423_);
    leanh::lean_ctor_set(v___x_2425_, 1, v___x_2424_);
    v___x_2426_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2413_, v___x_2425_, v_constName_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
    return v___x_2426_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_2427_: *mut leanh::LeanObject,
    mut v_constName_2428_: *mut leanh::LeanObject,
    mut v___y_2429_: *mut leanh::LeanObject,
    mut v___y_2430_: *mut leanh::LeanObject,
    mut v___y_2431_: *mut leanh::LeanObject,
    mut v___y_2432_: *mut leanh::LeanObject,
    mut v___y_2433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2434_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_2427_, v_constName_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
    leanh::lean_dec(v___y_2432_);
    leanh::lean_dec_ref(v___y_2431_);
    leanh::lean_dec(v___y_2430_);
    leanh::lean_dec_ref(v___y_2429_);
    leanh::lean_dec(v_ref_2427_);
    return v_res_2434_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(
    mut v_constName_2435_: *mut leanh::LeanObject,
    mut v___y_2436_: *mut leanh::LeanObject,
    mut v___y_2437_: *mut leanh::LeanObject,
    mut v___y_2438_: *mut leanh::LeanObject,
    mut v___y_2439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_2441_ = leanh::lean_ctor_get(v___y_2438_, 5);
    v___x_2442_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_2441_, v_constName_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
    return v___x_2442_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg___boxed(
    mut v_constName_2443_: *mut leanh::LeanObject,
    mut v___y_2444_: *mut leanh::LeanObject,
    mut v___y_2445_: *mut leanh::LeanObject,
    mut v___y_2446_: *mut leanh::LeanObject,
    mut v___y_2447_: *mut leanh::LeanObject,
    mut v___y_2448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2449_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(v_constName_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
    leanh::lean_dec(v___y_2447_);
    leanh::lean_dec_ref(v___y_2446_);
    leanh::lean_dec(v___y_2445_);
    leanh::lean_dec_ref(v___y_2444_);
    return v_res_2449_;
}
pub unsafe fn l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(
    mut v_constName_2450_: *mut leanh::LeanObject,
    mut v_skipRealize_2451_: u8,
    mut v___y_2452_: *mut leanh::LeanObject,
    mut v___y_2453_: *mut leanh::LeanObject,
    mut v___y_2454_: *mut leanh::LeanObject,
    mut v___y_2455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2464_: u8 = 0;
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2457_ = lean_st_ref_get(v___y_2455_);
                v_env_2458_ = leanh::lean_ctor_get(v___x_2457_, 0);
                leanh::lean_inc_ref(v_env_2458_);
                leanh::lean_dec(v___x_2457_);
                leanh::lean_inc(v_constName_2450_);
                v___x_2459_ = l_Lean_Environment_findAsync_x3f(
                    v_env_2458_,
                    v_constName_2450_,
                    v_skipRealize_2451_,
                );
                if leanh::lean_obj_tag(v___x_2459_) == 0 {
                    v___x_2460_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(v_constName_2450_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
                    return v___x_2460_;
                } else {
                    leanh::lean_dec(v_constName_2450_);
                    v_val_2461_ = leanh::lean_ctor_get(v___x_2459_, 0);
                    v_isSharedCheck_2468_ = (!leanh::lean_is_exclusive(v___x_2459_)) as u8;
                    if v_isSharedCheck_2468_ == 0 {
                        v___x_2463_ = v___x_2459_;
                        v_isShared_2464_ = v_isSharedCheck_2468_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2461_);
                        leanh::lean_dec(v___x_2459_);
                        v___x_2463_ = leanh::lean_box(0);
                        v_isShared_2464_ = v_isSharedCheck_2468_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2464_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2463_, 0);
                    v___x_2466_ = v___x_2463_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2467_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_val_2461_);
                    v___x_2466_ = v_reuseFailAlloc_2467_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0___boxed(
    mut v_constName_2469_: *mut leanh::LeanObject,
    mut v_skipRealize_2470_: *mut leanh::LeanObject,
    mut v___y_2471_: *mut leanh::LeanObject,
    mut v___y_2472_: *mut leanh::LeanObject,
    mut v___y_2473_: *mut leanh::LeanObject,
    mut v___y_2474_: *mut leanh::LeanObject,
    mut v___y_2475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipRealize_boxed_2476_: u8 = 0;
    let mut v_res_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_2476_ = (leanh::lean_unbox(v_skipRealize_2470_) as u8);
    v_res_2477_ = l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(
        v_constName_2469_,
        v_skipRealize_boxed_2476_,
        v___y_2471_,
        v___y_2472_,
        v___y_2473_,
        v___y_2474_,
    );
    leanh::lean_dec(v___y_2474_);
    leanh::lean_dec_ref(v___y_2473_);
    leanh::lean_dec(v___y_2472_);
    leanh::lean_dec_ref(v___y_2471_);
    return v_res_2477_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2479_ = l_Lean_Meta_mkSimpAttr___lam__0___closed__0;
    v___x_2480_ = l_Lean_stringToMessageData(v___x_2479_);
    return v___x_2480_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2482_ = l_Lean_Meta_mkSimpAttr___lam__0___closed__2;
    v___x_2483_ = l_Lean_stringToMessageData(v___x_2482_);
    return v___x_2483_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2485_ = l_Lean_Meta_mkSimpAttr___lam__0___closed__4;
    v___x_2486_ = l_Lean_stringToMessageData(v___x_2485_);
    return v___x_2486_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2487_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__5_once),
        _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__5,
    );
    v___x_2488_ = l_Lean_MessageData_note(v___x_2487_);
    return v___x_2488_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2489_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2489_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2490_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__7_once),
        _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__7,
    );
    v___x_2491_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2491_, 0, v___x_2490_);
    return v___x_2491_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2492_ = leanh::lean_box(1);
    v___x_2493_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4);
    v___x_2494_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__8_once),
        _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__8,
    );
    v___x_2495_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2495_, 0, v___x_2494_);
    leanh::lean_ctor_set(v___x_2495_, 1, v___x_2493_);
    leanh::lean_ctor_set(v___x_2495_, 2, v___x_2492_);
    return v___x_2495_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__11() -> *mut leanh::LeanObject
{
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2498_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__8_once),
        _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__8,
    );
    v___x_2499_ = leanh::lean_unsigned_to_nat(0);
    v___x_2500_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2500_, 0, v___x_2499_);
    leanh::lean_ctor_set(v___x_2500_, 1, v___x_2499_);
    leanh::lean_ctor_set(v___x_2500_, 2, v___x_2499_);
    leanh::lean_ctor_set(v___x_2500_, 3, v___x_2499_);
    leanh::lean_ctor_set(v___x_2500_, 4, v___x_2498_);
    leanh::lean_ctor_set(v___x_2500_, 5, v___x_2498_);
    leanh::lean_ctor_set(v___x_2500_, 6, v___x_2498_);
    leanh::lean_ctor_set(v___x_2500_, 7, v___x_2498_);
    leanh::lean_ctor_set(v___x_2500_, 8, v___x_2498_);
    leanh::lean_ctor_set(v___x_2500_, 9, v___x_2498_);
    return v___x_2500_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__12() -> *mut leanh::LeanObject
{
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2501_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__8_once),
        _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__8,
    );
    v___x_2502_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_2502_, 0, v___x_2501_);
    leanh::lean_ctor_set(v___x_2502_, 1, v___x_2501_);
    leanh::lean_ctor_set(v___x_2502_, 2, v___x_2501_);
    leanh::lean_ctor_set(v___x_2502_, 3, v___x_2501_);
    leanh::lean_ctor_set(v___x_2502_, 4, v___x_2501_);
    leanh::lean_ctor_set(v___x_2502_, 5, v___x_2501_);
    return v___x_2502_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__13() -> *mut leanh::LeanObject
{
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2503_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__8_once),
        _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__8,
    );
    v___x_2504_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_2504_, 0, v___x_2503_);
    leanh::lean_ctor_set(v___x_2504_, 1, v___x_2503_);
    leanh::lean_ctor_set(v___x_2504_, 2, v___x_2503_);
    leanh::lean_ctor_set(v___x_2504_, 3, v___x_2503_);
    leanh::lean_ctor_set(v___x_2504_, 4, v___x_2503_);
    return v___x_2504_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__14() -> *mut leanh::LeanObject
{
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2505_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__13_once),
        _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__13,
    );
    v___x_2506_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4);
    v___x_2507_ = leanh::lean_box(1);
    v___x_2508_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__12_once),
        _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__12,
    );
    v___x_2509_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__11_once),
        _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__11,
    );
    v___x_2510_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_2510_, 0, v___x_2509_);
    leanh::lean_ctor_set(v___x_2510_, 1, v___x_2508_);
    leanh::lean_ctor_set(v___x_2510_, 2, v___x_2507_);
    leanh::lean_ctor_set(v___x_2510_, 3, v___x_2506_);
    leanh::lean_ctor_set(v___x_2510_, 4, v___x_2505_);
    return v___x_2510_;
}
pub unsafe fn l_Lean_Meta_mkSimpAttr___lam__0(
    mut v_ext_2517_: *mut leanh::LeanObject,
    mut v_attrName_2518_: *mut leanh::LeanObject,
    mut v_declName_2519_: *mut leanh::LeanObject,
    mut v_stx_2520_: *mut leanh::LeanObject,
    mut v_attrKind_2521_: u8,
    mut v___y_2522_: *mut leanh::LeanObject,
    mut v___y_2523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2535_: u8 = 0;
    let mut v___y_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2538_: u8 = 0;
    let mut v___y_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2541_: u8 = 0;
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sig_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: u8 = 0;
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: u8 = 0;
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2566_: u8 = 0;
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2570_: u8 = 0;
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2575_: u8 = 0;
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2579_: u8 = 0;
    let mut v_a_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2583_: u8 = 0;
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2587_: u8 = 0;
    let mut v___y_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2591_: u8 = 0;
    let mut v___y_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2594_: u8 = 0;
    let mut v___y_2595_: u8 = 0;
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: u8 = 0;
    let mut v___y_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: u8 = 0;
    let mut v___x_2603_: u8 = 0;
    let mut v___x_2604_: u8 = 0;
    let mut v___x_2605_: u8 = 0;
    let mut v___x_2606_: u8 = 0;
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: u8 = 0;
    let mut v___x_2609_: u8 = 0;
    let mut v___x_2610_: u8 = 0;
    let mut v___x_2611_: u8 = 0;
    let mut v___x_2612_: u8 = 0;
    let mut v___x_2613_: u8 = 0;
    let mut v___x_2614_: u64 = 0;
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: u8 = 0;
    let mut v___x_2623_: u8 = 0;
    let mut v___x_2624_: u8 = 0;
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: u8 = 0;
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: u8 = 0;
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: u8 = 0;
    let mut v___x_2638_: u8 = 0;
    let mut v___x_2639_: u8 = 0;
    let mut v_a_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2647_: u8 = 0;
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2653_: u8 = 0;
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2657_: u8 = 0;
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: u8 = 0;
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_2519_);
                v___x_2658_ = l_Lean_Meta_Simp_isSimproc___redArg(v_declName_2519_, v___y_2523_);
                if leanh::lean_obj_tag(v___x_2658_) == 0 {
                    v_a_2659_ = leanh::lean_ctor_get(v___x_2658_, 0);
                    leanh::lean_inc(v_a_2659_);
                    v___x_2660_ = (leanh::lean_unbox(v_a_2659_) as u8);
                    leanh::lean_dec(v_a_2659_);
                    if v___x_2660_ == 0 {
                        leanh::lean_dec_ref_known(v___x_2658_, 1);
                        v___x_2661_ = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(
                            v_declName_2519_,
                            v___y_2523_,
                        );
                        v___y_2600_ = v___x_2661_;
                        state = 11;
                        continue;
                    } else {
                        v___y_2600_ = v___x_2658_;
                        state = 11;
                        continue;
                    }
                } else {
                    v___y_2600_ = v___x_2658_;
                    state = 11;
                    continue;
                }
            }
            1 => {
                v___x_2528_ = lean_st_ref_get(v___y_2527_);
                leanh::lean_dec(v___y_2527_);
                leanh::lean_dec(v___x_2528_);
                v___x_2529_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2529_, 0, v___y_2526_);
                return v___x_2529_;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_2533_) == 0 {
                    leanh::lean_dec_ref_known(v___y_2533_, 1);
                    v___y_2526_ = v___y_2531_;
                    v___y_2527_ = v___y_2532_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___y_2532_);
                    return v___y_2533_;
                }
            }
            3 => {
                v___x_2542_ = leanh::lean_unsigned_to_nat(3);
                v___x_2543_ = l_Lean_Syntax_getArg(v_stx_2520_, v___x_2542_);
                leanh::lean_dec(v_stx_2520_);
                v___x_2544_ = l_Lean_getAttrParamOptPrio(v___x_2543_, v___y_2522_, v___y_2523_);
                if leanh::lean_obj_tag(v___x_2544_) == 0 {
                    v_a_2545_ = leanh::lean_ctor_get(v___x_2544_, 0);
                    leanh::lean_inc(v_a_2545_);
                    leanh::lean_dec_ref_known(v___x_2544_, 1);
                    v_sig_2546_ = leanh::lean_ctor_get(v___y_2537_, 1);
                    leanh::lean_inc_ref(v_sig_2546_);
                    leanh::lean_dec_ref(v___y_2537_);
                    v___x_2547_ = lean_task_get_own(v_sig_2546_);
                    v_type_2548_ = leanh::lean_ctor_get(v___x_2547_, 2);
                    leanh::lean_inc_ref(v_type_2548_);
                    leanh::lean_dec(v___x_2547_);
                    v___x_2549_ = l_Lean_Meta_isProp(
                        v_type_2548_,
                        v___y_2536_,
                        v___y_2540_,
                        v___y_2522_,
                        v___y_2523_,
                    );
                    if leanh::lean_obj_tag(v___x_2549_) == 0 {
                        v_a_2550_ = leanh::lean_ctor_get(v___x_2549_, 0);
                        leanh::lean_inc(v_a_2550_);
                        leanh::lean_dec_ref_known(v___x_2549_, 1);
                        v___x_2551_ = (leanh::lean_unbox(v_a_2550_) as u8);
                        leanh::lean_dec(v_a_2550_);
                        if v___x_2551_ == 0 {
                            leanh::lean_inc(v_declName_2519_);
                            v___x_2552_ = l_Lean_Meta_addDeclToUnfold(
                                v_ext_2517_,
                                v_declName_2519_,
                                v___y_2535_,
                                v___y_2541_,
                                v_a_2545_,
                                v_attrKind_2521_,
                                v___y_2536_,
                                v___y_2540_,
                                v___y_2522_,
                                v___y_2523_,
                            );
                            if leanh::lean_obj_tag(v___x_2552_) == 0 {
                                v_a_2553_ = leanh::lean_ctor_get(v___x_2552_, 0);
                                leanh::lean_inc(v_a_2553_);
                                leanh::lean_dec_ref_known(v___x_2552_, 1);
                                v___x_2554_ = (leanh::lean_unbox(v_a_2553_) as u8);
                                leanh::lean_dec(v_a_2553_);
                                if v___x_2554_ == 0 {
                                    v___x_2555_ = leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_mkSimpAttr___lam__0___closed__1
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_mkSimpAttr___lam__0___closed__1_once
                                        ),
                                        _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__1,
                                    );
                                    v___x_2556_ = l_Lean_MessageData_ofConstName(
                                        v_declName_2519_,
                                        v___y_2538_,
                                    );
                                    v___x_2557_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_2557_, 0, v___x_2555_);
                                    leanh::lean_ctor_set(v___x_2557_, 1, v___x_2556_);
                                    v___x_2558_ = leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_mkSimpAttr___lam__0___closed__3
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_mkSimpAttr___lam__0___closed__3_once
                                        ),
                                        _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__3,
                                    );
                                    v___x_2559_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_2559_, 0, v___x_2557_);
                                    leanh::lean_ctor_set(v___x_2559_, 1, v___x_2558_);
                                    v___x_2560_ = leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_mkSimpAttr___lam__0___closed__6
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_mkSimpAttr___lam__0___closed__6_once
                                        ),
                                        _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__6,
                                    );
                                    v___x_2561_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_2561_, 0, v___x_2559_);
                                    leanh::lean_ctor_set(v___x_2561_, 1, v___x_2560_);
                                    v___x_2562_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v___x_2561_, v___y_2536_, v___y_2540_, v___y_2522_, v___y_2523_);
                                    leanh::lean_dec_ref(v___y_2536_);
                                    v___y_2531_ = v___y_2539_;
                                    v___y_2532_ = v___y_2540_;
                                    v___y_2533_ = v___x_2562_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v___y_2536_);
                                    leanh::lean_dec(v_declName_2519_);
                                    v___y_2526_ = v___y_2539_;
                                    v___y_2527_ = v___y_2540_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___y_2540_);
                                leanh::lean_dec_ref(v___y_2536_);
                                leanh::lean_dec(v_declName_2519_);
                                v_a_2563_ = leanh::lean_ctor_get(v___x_2552_, 0);
                                v_isSharedCheck_2570_ =
                                    (!leanh::lean_is_exclusive(v___x_2552_)) as u8;
                                if v_isSharedCheck_2570_ == 0 {
                                    v___x_2565_ = v___x_2552_;
                                    v_isShared_2566_ = v_isSharedCheck_2570_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2563_);
                                    leanh::lean_dec(v___x_2552_);
                                    v___x_2565_ = leanh::lean_box(0);
                                    v_isShared_2566_ = v_isSharedCheck_2570_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            v___x_2571_ = l_Lean_Meta_addSimpTheorem(
                                v_ext_2517_,
                                v_declName_2519_,
                                v___y_2535_,
                                v___y_2541_,
                                v_attrKind_2521_,
                                v_a_2545_,
                                v___y_2536_,
                                v___y_2540_,
                                v___y_2522_,
                                v___y_2523_,
                            );
                            leanh::lean_dec_ref(v___y_2536_);
                            v___y_2531_ = v___y_2539_;
                            v___y_2532_ = v___y_2540_;
                            v___y_2533_ = v___x_2571_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2545_);
                        leanh::lean_dec(v___y_2540_);
                        leanh::lean_dec_ref(v___y_2536_);
                        leanh::lean_dec(v_declName_2519_);
                        leanh::lean_dec_ref(v_ext_2517_);
                        v_a_2572_ = leanh::lean_ctor_get(v___x_2549_, 0);
                        v_isSharedCheck_2579_ =
                            (!leanh::lean_is_exclusive(v___x_2549_)) as u8;
                        if v_isSharedCheck_2579_ == 0 {
                            v___x_2574_ = v___x_2549_;
                            v_isShared_2575_ = v_isSharedCheck_2579_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2572_);
                            leanh::lean_dec(v___x_2549_);
                            v___x_2574_ = leanh::lean_box(0);
                            v_isShared_2575_ = v_isSharedCheck_2579_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_2540_);
                    leanh::lean_dec_ref(v___y_2537_);
                    leanh::lean_dec_ref(v___y_2536_);
                    leanh::lean_dec(v_declName_2519_);
                    leanh::lean_dec_ref(v_ext_2517_);
                    v_a_2580_ = leanh::lean_ctor_get(v___x_2544_, 0);
                    v_isSharedCheck_2587_ = (!leanh::lean_is_exclusive(v___x_2544_)) as u8;
                    if v_isSharedCheck_2587_ == 0 {
                        v___x_2582_ = v___x_2544_;
                        v_isShared_2583_ = v_isSharedCheck_2587_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2580_);
                        leanh::lean_dec(v___x_2544_);
                        v___x_2582_ = leanh::lean_box(0);
                        v_isShared_2583_ = v_isSharedCheck_2587_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2566_ == 0 {
                    v___x_2568_ = v___x_2565_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2569_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
                    v___x_2568_ = v_reuseFailAlloc_2569_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2568_;
            }
            6 => {
                if v_isShared_2575_ == 0 {
                    v___x_2577_ = v___x_2574_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2578_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
                    v___x_2577_ = v_reuseFailAlloc_2578_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2577_;
            }
            8 => {
                if v_isShared_2583_ == 0 {
                    v___x_2585_ = v___x_2582_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2586_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
                    v___x_2585_ = v_reuseFailAlloc_2586_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2585_;
            }
            10 => {
                v___x_2596_ = leanh::lean_unsigned_to_nat(2);
                v___x_2597_ = l_Lean_Syntax_getArg(v_stx_2520_, v___x_2596_);
                v___x_2598_ = l_Lean_Syntax_isNone(v___x_2597_);
                leanh::lean_dec(v___x_2597_);
                if v___x_2598_ == 0 {
                    v___y_2535_ = v___y_2595_;
                    v___y_2536_ = v___y_2589_;
                    v___y_2537_ = v___y_2590_;
                    v___y_2538_ = v___y_2591_;
                    v___y_2539_ = v___y_2592_;
                    v___y_2540_ = v___y_2593_;
                    v___y_2541_ = v___y_2594_;
                    state = 3;
                    continue;
                } else {
                    v___y_2535_ = v___y_2595_;
                    v___y_2536_ = v___y_2589_;
                    v___y_2537_ = v___y_2590_;
                    v___y_2538_ = v___y_2591_;
                    v___y_2539_ = v___y_2592_;
                    v___y_2540_ = v___y_2593_;
                    v___y_2541_ = v___y_2591_;
                    state = 3;
                    continue;
                }
            }
            11 => {
                if leanh::lean_obj_tag(v___y_2600_) == 0 {
                    v_a_2601_ = leanh::lean_ctor_get(v___y_2600_, 0);
                    leanh::lean_inc(v_a_2601_);
                    leanh::lean_dec_ref_known(v___y_2600_, 1);
                    v___x_2602_ = (leanh::lean_unbox(v_a_2601_) as u8);
                    if v___x_2602_ == 0 {
                        leanh::lean_dec(v_attrName_2518_);
                        v___x_2603_ = 1;
                        v___x_2604_ = 1;
                        v___x_2605_ = 0;
                        v___x_2606_ = 2;
                        v___x_2607_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                        v___x_2608_ = (leanh::lean_unbox(v_a_2601_) as u8);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 0 as u32, v___x_2608_);
                        v___x_2609_ = (leanh::lean_unbox(v_a_2601_) as u8);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 1 as u32, v___x_2609_);
                        v___x_2610_ = (leanh::lean_unbox(v_a_2601_) as u8);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 2 as u32, v___x_2610_);
                        v___x_2611_ = (leanh::lean_unbox(v_a_2601_) as u8);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 3 as u32, v___x_2611_);
                        v___x_2612_ = (leanh::lean_unbox(v_a_2601_) as u8);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 4 as u32, v___x_2612_);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 5 as u32, v___x_2603_);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 6 as u32, v___x_2603_);
                        v___x_2613_ = (leanh::lean_unbox(v_a_2601_) as u8);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 7 as u32, v___x_2613_);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 8 as u32, v___x_2603_);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 9 as u32, v___x_2604_);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 10 as u32, v___x_2605_);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 11 as u32, v___x_2603_);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 12 as u32, v___x_2603_);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 13 as u32, v___x_2603_);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 14 as u32, v___x_2606_);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 15 as u32, v___x_2603_);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 16 as u32, v___x_2603_);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 17 as u32, v___x_2603_);
                        leanh::lean_ctor_set_uint8(v___x_2607_, 18 as u32, v___x_2603_);
                        v___x_2614_ =
                            l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2607_);
                        v___x_2615_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                        leanh::lean_ctor_set(v___x_2615_, 0, v___x_2607_);
                        leanh::lean_ctor_set_uint64(
                            v___x_2615_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_2614_,
                        );
                        v___x_2616_ = leanh::lean_box(1);
                        v___x_2617_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2618_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__9),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_mkSimpAttr___lam__0___closed__9_once
                            ),
                            _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__9,
                        );
                        v___x_2619_ = l_Lean_Meta_mkSimpAttr___lam__0___closed__10;
                        v___x_2620_ = leanh::lean_box(0);
                        v___x_2621_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                        leanh::lean_ctor_set(v___x_2621_, 0, v___x_2615_);
                        leanh::lean_ctor_set(v___x_2621_, 1, v___x_2616_);
                        leanh::lean_ctor_set(v___x_2621_, 2, v___x_2618_);
                        leanh::lean_ctor_set(v___x_2621_, 3, v___x_2619_);
                        leanh::lean_ctor_set(v___x_2621_, 4, v___x_2620_);
                        leanh::lean_ctor_set(v___x_2621_, 5, v___x_2617_);
                        leanh::lean_ctor_set(v___x_2621_, 6, v___x_2620_);
                        v___x_2622_ = (leanh::lean_unbox(v_a_2601_) as u8);
                        leanh::lean_ctor_set_uint8(
                            v___x_2621_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                            v___x_2622_,
                        );
                        v___x_2623_ = (leanh::lean_unbox(v_a_2601_) as u8);
                        leanh::lean_ctor_set_uint8(
                            v___x_2621_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                            v___x_2623_,
                        );
                        v___x_2624_ = (leanh::lean_unbox(v_a_2601_) as u8);
                        leanh::lean_ctor_set_uint8(
                            v___x_2621_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                            v___x_2624_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_2621_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                            v___x_2603_,
                        );
                        v___x_2625_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___lam__0___closed__14),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_mkSimpAttr___lam__0___closed__14_once
                            ),
                            _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__14,
                        );
                        v___x_2626_ = lean_st_mk_ref(v___x_2625_);
                        v___x_2627_ = (leanh::lean_unbox(v_a_2601_) as u8);
                        leanh::lean_inc(v_declName_2519_);
                        v___x_2628_ =
                            l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(
                                v_declName_2519_,
                                v___x_2627_,
                                v___x_2621_,
                                v___x_2626_,
                                v___y_2522_,
                                v___y_2523_,
                            );
                        if leanh::lean_obj_tag(v___x_2628_) == 0 {
                            v_a_2629_ = leanh::lean_ctor_get(v___x_2628_, 0);
                            leanh::lean_inc(v_a_2629_);
                            leanh::lean_dec_ref_known(v___x_2628_, 1);
                            v___x_2630_ = leanh::lean_box(0);
                            v___x_2631_ = leanh::lean_unsigned_to_nat(1);
                            v___x_2632_ = l_Lean_Syntax_getArg(v_stx_2520_, v___x_2631_);
                            v___x_2633_ = l_Lean_Syntax_isNone(v___x_2632_);
                            if v___x_2633_ == 0 {
                                v___x_2634_ = l_Lean_Syntax_getArg(v___x_2632_, v___x_2617_);
                                leanh::lean_dec(v___x_2632_);
                                v___x_2635_ = l_Lean_Syntax_getKind(v___x_2634_);
                                v___x_2636_ = l_Lean_Meta_mkSimpAttr___lam__0___closed__16;
                                v___x_2637_ = lean_name_eq(v___x_2635_, v___x_2636_);
                                leanh::lean_dec(v___x_2635_);
                                v___x_2638_ = (leanh::lean_unbox(v_a_2601_) as u8);
                                leanh::lean_dec(v_a_2601_);
                                v___y_2589_ = v___x_2621_;
                                v___y_2590_ = v_a_2629_;
                                v___y_2591_ = v___x_2638_;
                                v___y_2592_ = v___x_2630_;
                                v___y_2593_ = v___x_2626_;
                                v___y_2594_ = v___x_2603_;
                                v___y_2595_ = v___x_2637_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_2632_);
                                v___x_2639_ = (leanh::lean_unbox(v_a_2601_) as u8);
                                leanh::lean_dec(v_a_2601_);
                                v___y_2589_ = v___x_2621_;
                                v___y_2590_ = v_a_2629_;
                                v___y_2591_ = v___x_2639_;
                                v___y_2592_ = v___x_2630_;
                                v___y_2593_ = v___x_2626_;
                                v___y_2594_ = v___x_2603_;
                                v___y_2595_ = v___x_2603_;
                                state = 10;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_2626_);
                            leanh::lean_dec_ref_known(v___x_2621_, 7);
                            leanh::lean_dec(v_a_2601_);
                            leanh::lean_dec(v_stx_2520_);
                            leanh::lean_dec(v_declName_2519_);
                            leanh::lean_dec_ref(v_ext_2517_);
                            v_a_2640_ = leanh::lean_ctor_get(v___x_2628_, 0);
                            v_isSharedCheck_2647_ =
                                (!leanh::lean_is_exclusive(v___x_2628_)) as u8;
                            if v_isSharedCheck_2647_ == 0 {
                                v___x_2642_ = v___x_2628_;
                                v_isShared_2643_ = v_isSharedCheck_2647_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2640_);
                                leanh::lean_dec(v___x_2628_);
                                v___x_2642_ = leanh::lean_box(0);
                                v_isShared_2643_ = v_isSharedCheck_2647_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_2601_);
                        leanh::lean_dec_ref(v_ext_2517_);
                        v___x_2648_ =
                            l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(v_attrName_2518_);
                        v___x_2649_ = l_Lean_Attribute_add(
                            v_declName_2519_,
                            v___x_2648_,
                            v_stx_2520_,
                            v_attrKind_2521_,
                            v___y_2522_,
                            v___y_2523_,
                        );
                        return v___x_2649_;
                    }
                } else {
                    leanh::lean_dec(v_stx_2520_);
                    leanh::lean_dec(v_declName_2519_);
                    leanh::lean_dec(v_attrName_2518_);
                    leanh::lean_dec_ref(v_ext_2517_);
                    v_a_2650_ = leanh::lean_ctor_get(v___y_2600_, 0);
                    v_isSharedCheck_2657_ = (!leanh::lean_is_exclusive(v___y_2600_)) as u8;
                    if v_isSharedCheck_2657_ == 0 {
                        v___x_2652_ = v___y_2600_;
                        v_isShared_2653_ = v_isSharedCheck_2657_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2650_);
                        leanh::lean_dec(v___y_2600_);
                        v___x_2652_ = leanh::lean_box(0);
                        v_isShared_2653_ = v_isSharedCheck_2657_;
                        state = 14;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_2643_ == 0 {
                    v___x_2645_ = v___x_2642_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2646_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
                    v___x_2645_ = v_reuseFailAlloc_2646_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2645_;
            }
            14 => {
                if v_isShared_2653_ == 0 {
                    v___x_2655_ = v___x_2652_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2656_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
                    v___x_2655_ = v_reuseFailAlloc_2656_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2655_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkSimpAttr___lam__0___boxed(
    mut v_ext_2662_: *mut leanh::LeanObject,
    mut v_attrName_2663_: *mut leanh::LeanObject,
    mut v_declName_2664_: *mut leanh::LeanObject,
    mut v_stx_2665_: *mut leanh::LeanObject,
    mut v_attrKind_2666_: *mut leanh::LeanObject,
    mut v___y_2667_: *mut leanh::LeanObject,
    mut v___y_2668_: *mut leanh::LeanObject,
    mut v___y_2669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_attrKind_boxed_2670_: u8 = 0;
    let mut v_res_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_2670_ = (leanh::lean_unbox(v_attrKind_2666_) as u8);
    v_res_2671_ = l_Lean_Meta_mkSimpAttr___lam__0(
        v_ext_2662_,
        v_attrName_2663_,
        v_declName_2664_,
        v_stx_2665_,
        v_attrKind_boxed_2670_,
        v___y_2667_,
        v___y_2668_,
    );
    leanh::lean_dec(v___y_2668_);
    leanh::lean_dec_ref(v___y_2667_);
    return v_res_2671_;
}
pub unsafe fn l_Lean_Meta_mkSimpAttr___lam__1(
    mut v_a_2672_: *mut leanh::LeanObject,
    mut v_x_2673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_a_2672_);
    return v_a_2672_;
}
pub unsafe fn l_Lean_Meta_mkSimpAttr___lam__1___boxed(
    mut v_a_2674_: *mut leanh::LeanObject,
    mut v_x_2675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2676_ = l_Lean_Meta_mkSimpAttr___lam__1(v_a_2674_, v_x_2675_);
    leanh::lean_dec_ref(v_x_2675_);
    leanh::lean_dec_ref(v_a_2674_);
    return v_res_2676_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(
    mut v_keys_2677_: *mut leanh::LeanObject,
    mut v_i_2678_: *mut leanh::LeanObject,
    mut v_k_2679_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: u8 = 0;
    let mut v_k_x27_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: u8 = 0;
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2680_ = lean_array_get_size(v_keys_2677_);
                v___x_2681_ = lean_nat_dec_lt(v_i_2678_, v___x_2680_);
                if v___x_2681_ == 0 {
                    leanh::lean_dec(v_i_2678_);
                    return v___x_2681_;
                } else {
                    v_k_x27_2682_ = lean_array_fget_borrowed(v_keys_2677_, v_i_2678_);
                    v___x_2683_ = lean_name_eq(v_k_2679_, v_k_x27_2682_);
                    if v___x_2683_ == 0 {
                        v___x_2684_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2685_ = lean_nat_add(v_i_2678_, v___x_2684_);
                        leanh::lean_dec(v_i_2678_);
                        v_i_2678_ = v___x_2685_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_2678_);
                        return v___x_2683_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg___boxed(
    mut v_keys_2687_: *mut leanh::LeanObject,
    mut v_i_2688_: *mut leanh::LeanObject,
    mut v_k_2689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2690_: u8 = 0;
    let mut v_r_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2690_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(v_keys_2687_, v_i_2688_, v_k_2689_);
    leanh::lean_dec(v_k_2689_);
    leanh::lean_dec_ref(v_keys_2687_);
    v_r_2691_ = leanh::lean_box((v_res_2690_) as usize);
    return v_r_2691_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__0()
-> usize {
    let mut v___x_2692_: usize = 0;
    let mut v___x_2693_: usize = 0;
    let mut v___x_2694_: usize = 0;
    v___x_2692_ = 5usize;
    v___x_2693_ = 1usize;
    v___x_2694_ = lean_usize_shift_left(v___x_2693_, v___x_2692_);
    return v___x_2694_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__1()
-> usize {
    let mut v___x_2695_: usize = 0;
    let mut v___x_2696_: usize = 0;
    let mut v___x_2697_: usize = 0;
    v___x_2695_ = 1usize;
    v___x_2696_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__0);
    v___x_2697_ = lean_usize_sub(v___x_2696_, v___x_2695_);
    return v___x_2697_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(
    mut v_x_2698_: *mut leanh::LeanObject,
    mut v_x_2699_: usize,
    mut v_x_2700_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: usize = 0;
    let mut v___x_2704_: usize = 0;
    let mut v___x_2705_: usize = 0;
    let mut v_j_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: u8 = 0;
    let mut v_node_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: usize = 0;
    let mut v___x_2713_: u8 = 0;
    let mut v_ks_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2698_) == 0 {
                    v_es_2701_ = leanh::lean_ctor_get(v_x_2698_, 0);
                    v___x_2702_ = leanh::lean_box(2);
                    v___x_2703_ = 5usize;
                    v___x_2704_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___closed__1);
                    v___x_2705_ = lean_usize_land(v_x_2699_, v___x_2704_);
                    v_j_2706_ = lean_usize_to_nat(v___x_2705_);
                    v___x_2707_ = lean_array_get_borrowed(v___x_2702_, v_es_2701_, v_j_2706_);
                    leanh::lean_dec(v_j_2706_);
                    match leanh::lean_obj_tag(v___x_2707_) {
                        0 => {
                            v_key_2708_ = leanh::lean_ctor_get(v___x_2707_, 0);
                            v___x_2709_ = lean_name_eq(v_x_2700_, v_key_2708_);
                            return v___x_2709_;
                        }
                        1 => {
                            v_node_2710_ = leanh::lean_ctor_get(v___x_2707_, 0);
                            v___x_2711_ = lean_usize_shift_right(v_x_2699_, v___x_2703_);
                            v_x_2698_ = v_node_2710_;
                            v_x_2699_ = v___x_2711_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2713_ = 0;
                            return v___x_2713_;
                        }
                    }
                } else {
                    v_ks_2714_ = leanh::lean_ctor_get(v_x_2698_, 0);
                    v___x_2715_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2716_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(v_ks_2714_, v___x_2715_, v_x_2700_);
                    return v___x_2716_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___boxed(
    mut v_x_2717_: *mut leanh::LeanObject,
    mut v_x_2718_: *mut leanh::LeanObject,
    mut v_x_2719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_9280__boxed_2720_: usize = 0;
    let mut v_res_2721_: u8 = 0;
    let mut v_r_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_9280__boxed_2720_ = leanh::lean_unbox_usize(v_x_2718_);
    leanh::lean_dec(v_x_2718_);
    v_res_2721_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(v_x_2717_, v_x_9280__boxed_2720_, v_x_2719_);
    leanh::lean_dec(v_x_2719_);
    leanh::lean_dec_ref(v_x_2717_);
    v_r_2722_ = leanh::lean_box((v_res_2721_) as usize);
    return v_r_2722_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0()
-> u64 {
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: u64 = 0;
    v___x_2723_ = leanh::lean_unsigned_to_nat(1723);
    v___x_2724_ = lean_uint64_of_nat(v___x_2723_);
    return v___x_2724_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(
    mut v_x_2725_: *mut leanh::LeanObject,
    mut v_x_2726_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_2728_: u64 = 0;
    let mut v___x_2729_: usize = 0;
    let mut v___x_2730_: u8 = 0;
    let mut v___x_2731_: u64 = 0;
    let mut v_hash_2732_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2726_) == 0 {
                    v___x_2731_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0);
                    v___y_2728_ = v___x_2731_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2732_ = leanh::lean_ctor_get_uint64(
                        v_x_2726_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2728_ = v_hash_2732_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2729_ = lean_uint64_to_usize(v___y_2728_);
                v___x_2730_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(v_x_2725_, v___x_2729_, v_x_2726_);
                return v___x_2730_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___boxed(
    mut v_x_2733_: *mut leanh::LeanObject,
    mut v_x_2734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2735_: u8 = 0;
    let mut v_r_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2735_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(v_x_2733_, v_x_2734_);
    leanh::lean_dec(v_x_2734_);
    leanh::lean_dec_ref(v_x_2733_);
    v_r_2736_ = leanh::lean_box((v_res_2735_) as usize);
    return v_r_2736_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10(
    mut v_msgData_2737_: *mut leanh::LeanObject,
    mut v___y_2738_: *mut leanh::LeanObject,
    mut v___y_2739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2741_ = lean_st_ref_get(v___y_2739_);
    v_env_2742_ = leanh::lean_ctor_get(v___x_2741_, 0);
    leanh::lean_inc_ref(v_env_2742_);
    leanh::lean_dec(v___x_2741_);
    v_options_2743_ = leanh::lean_ctor_get(v___y_2738_, 2);
    v___x_2744_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2);
    v___x_2745_ = leanh::lean_unsigned_to_nat(32);
    v___x_2746_ = lean_mk_empty_array_with_capacity(v___x_2745_);
    leanh::lean_dec_ref(v___x_2746_);
    v___x_2747_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5);
    leanh::lean_inc_ref(v_options_2743_);
    v___x_2748_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2748_, 0, v_env_2742_);
    leanh::lean_ctor_set(v___x_2748_, 1, v___x_2744_);
    leanh::lean_ctor_set(v___x_2748_, 2, v___x_2747_);
    leanh::lean_ctor_set(v___x_2748_, 3, v_options_2743_);
    v___x_2749_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2749_, 0, v___x_2748_);
    leanh::lean_ctor_set(v___x_2749_, 1, v_msgData_2737_);
    v___x_2750_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2750_, 0, v___x_2749_);
    return v___x_2750_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10___boxed(
    mut v_msgData_2751_: *mut leanh::LeanObject,
    mut v___y_2752_: *mut leanh::LeanObject,
    mut v___y_2753_: *mut leanh::LeanObject,
    mut v___y_2754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2755_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10(v_msgData_2751_, v___y_2752_, v___y_2753_);
    leanh::lean_dec(v___y_2753_);
    leanh::lean_dec_ref(v___y_2752_);
    return v_res_2755_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0(
    mut v___y_2763_: u8,
    mut v_suppressElabErrors_2764_: u8,
    mut v_x_2765_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_2765_) == 1 {
        let mut v_pre_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_2766_ = leanh::lean_ctor_get(v_x_2765_, 0);
        match leanh::lean_obj_tag(v_pre_2766_) {
            1 => {
                let mut v_pre_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_2767_ = leanh::lean_ctor_get(v_pre_2766_, 0);
                match leanh::lean_obj_tag(v_pre_2767_) {
                    0 => {
                        let mut v_str_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2771_: u8 = 0;
                        v_str_2768_ = leanh::lean_ctor_get(v_x_2765_, 1);
                        v_str_2769_ = leanh::lean_ctor_get(v_pre_2766_, 1);
                        v___x_2770_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__0;
                        v___x_2771_ = lean_string_dec_eq(v_str_2769_, v___x_2770_);
                        if v___x_2771_ == 0 {
                            let mut v___x_2772_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2773_: u8 = 0;
                            v___x_2772_ = l_Lean_Meta_mkSimpAttr___auto__1___closed__2;
                            v___x_2773_ = lean_string_dec_eq(v_str_2769_, v___x_2772_);
                            if v___x_2773_ == 0 {
                                return v___y_2763_;
                            } else {
                                let mut v___x_2774_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2775_: u8 = 0;
                                v___x_2774_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__1;
                                v___x_2775_ = lean_string_dec_eq(v_str_2768_, v___x_2774_);
                                if v___x_2775_ == 0 {
                                    return v___y_2763_;
                                } else {
                                    return v_suppressElabErrors_2764_;
                                }
                            }
                        } else {
                            let mut v___x_2776_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2777_: u8 = 0;
                            v___x_2776_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__2;
                            v___x_2777_ = lean_string_dec_eq(v_str_2768_, v___x_2776_);
                            if v___x_2777_ == 0 {
                                return v___y_2763_;
                            } else {
                                return v_suppressElabErrors_2764_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_pre_2778_ = leanh::lean_ctor_get(v_pre_2767_, 0);
                        if leanh::lean_obj_tag(v_pre_2778_) == 0 {
                            let mut v_str_2779_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2780_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2781_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2782_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2783_: u8 = 0;
                            v_str_2779_ = leanh::lean_ctor_get(v_x_2765_, 1);
                            v_str_2780_ = leanh::lean_ctor_get(v_pre_2766_, 1);
                            v_str_2781_ = leanh::lean_ctor_get(v_pre_2767_, 1);
                            v___x_2782_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__3;
                            v___x_2783_ = lean_string_dec_eq(v_str_2781_, v___x_2782_);
                            if v___x_2783_ == 0 {
                                return v___y_2763_;
                            } else {
                                let mut v___x_2784_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2785_: u8 = 0;
                                v___x_2784_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__4;
                                v___x_2785_ = lean_string_dec_eq(v_str_2780_, v___x_2784_);
                                if v___x_2785_ == 0 {
                                    return v___y_2763_;
                                } else {
                                    let mut v___x_2786_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_2787_: u8 = 0;
                                    v___x_2786_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__5;
                                    v___x_2787_ = lean_string_dec_eq(v_str_2779_, v___x_2786_);
                                    if v___x_2787_ == 0 {
                                        return v___y_2763_;
                                    } else {
                                        return v_suppressElabErrors_2764_;
                                    }
                                }
                            }
                        } else {
                            return v___y_2763_;
                        }
                    }
                    _ => {
                        return v___y_2763_;
                    }
                }
            }
            0 => {
                let mut v_str_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2790_: u8 = 0;
                v_str_2788_ = leanh::lean_ctor_get(v_x_2765_, 1);
                v___x_2789_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__6;
                v___x_2790_ = lean_string_dec_eq(v_str_2788_, v___x_2789_);
                if v___x_2790_ == 0 {
                    return v___y_2763_;
                } else {
                    return v_suppressElabErrors_2764_;
                }
            }
            _ => {
                return v___y_2763_;
            }
        }
    } else {
        return v___y_2763_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___boxed(
    mut v___y_2791_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_2792_: *mut leanh::LeanObject,
    mut v_x_2793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_9423__boxed_2794_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2795_: u8 = 0;
    let mut v_res_2796_: u8 = 0;
    let mut v_r_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_9423__boxed_2794_ = (leanh::lean_unbox(v___y_2791_) as u8);
    v_suppressElabErrors_boxed_2795_ = (leanh::lean_unbox(v_suppressElabErrors_2792_) as u8);
    v_res_2796_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0(v___y_9423__boxed_2794_, v_suppressElabErrors_boxed_2795_, v_x_2793_);
    leanh::lean_dec(v_x_2793_);
    v_r_2797_ = leanh::lean_box((v_res_2796_) as usize);
    return v_r_2797_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11(
    mut v_opts_2798_: *mut leanh::LeanObject,
    mut v_opt_2799_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2800_ = leanh::lean_ctor_get(v_opt_2799_, 0);
    v_defValue_2801_ = leanh::lean_ctor_get(v_opt_2799_, 1);
    v_map_2802_ = leanh::lean_ctor_get(v_opts_2798_, 0);
    v___x_2803_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2802_,
            v_name_2800_,
        );
    if leanh::lean_obj_tag(v___x_2803_) == 0 {
        let mut v___x_2804_: u8 = 0;
        v___x_2804_ = (leanh::lean_unbox(v_defValue_2801_) as u8);
        return v___x_2804_;
    } else {
        let mut v_val_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2805_ = leanh::lean_ctor_get(v___x_2803_, 0);
        leanh::lean_inc(v_val_2805_);
        leanh::lean_dec_ref_known(v___x_2803_, 1);
        if leanh::lean_obj_tag(v_val_2805_) == 1 {
            let mut v_v_2806_: u8 = 0;
            v_v_2806_ = leanh::lean_ctor_get_uint8(v_val_2805_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_2805_, 0);
            return v_v_2806_;
        } else {
            let mut v___x_2807_: u8 = 0;
            leanh::lean_dec(v_val_2805_);
            v___x_2807_ = (leanh::lean_unbox(v_defValue_2801_) as u8);
            return v___x_2807_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11___boxed(
    mut v_opts_2808_: *mut leanh::LeanObject,
    mut v_opt_2809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2810_: u8 = 0;
    let mut v_r_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2810_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11(v_opts_2808_, v_opt_2809_);
    leanh::lean_dec_ref(v_opt_2809_);
    leanh::lean_dec_ref(v_opts_2808_);
    v_r_2811_ = leanh::lean_box((v_res_2810_) as usize);
    return v_r_2811_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6(
    mut v_ref_2813_: *mut leanh::LeanObject,
    mut v_msgData_2814_: *mut leanh::LeanObject,
    mut v_severity_2815_: u8,
    mut v_isSilent_2816_: u8,
    mut v___y_2817_: *mut leanh::LeanObject,
    mut v___y_2818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2823_: u8 = 0;
    let mut v___y_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2827_: u8 = 0;
    let mut v___y_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2844_: u8 = 0;
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2855_: u8 = 0;
    let mut v___y_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2859_: u8 = 0;
    let mut v___y_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2861_: u8 = 0;
    let mut v___y_2862_: u8 = 0;
    let mut v___y_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2870_: u8 = 0;
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: u8 = 0;
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2880_: u8 = 0;
    let mut v___y_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2884_: u8 = 0;
    let mut v___y_2885_: u8 = 0;
    let mut v___y_2886_: u8 = 0;
    let mut v___y_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2896_: u8 = 0;
    let mut v___y_2897_: u8 = 0;
    let mut v___y_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2899_: u8 = 0;
    let mut v_ref_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: u8 = 0;
    let mut v___y_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2909_: u8 = 0;
    let mut v___y_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2911_: u8 = 0;
    let mut v___y_2912_: u8 = 0;
    let mut v___y_2914_: u8 = 0;
    let mut v_fileName_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2919_: u8 = 0;
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: u8 = 0;
    let mut v___x_2924_: u8 = 0;
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: u8 = 0;
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: u8 = 0;
    let mut v___x_2930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2904_ = 2;
                v___x_2929_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2815_, v___x_2904_);
                if v___x_2929_ == 0 {
                    v___y_2914_ = v___x_2929_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_msgData_2814_);
                    v___x_2930_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2814_);
                    v___y_2914_ = v___x_2930_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_2830_ = lean_st_ref_take(v___y_2829_);
                v_currNamespace_2831_ = leanh::lean_ctor_get(v___y_2828_, 6);
                v_openDecls_2832_ = leanh::lean_ctor_get(v___y_2828_, 7);
                v_env_2833_ = leanh::lean_ctor_get(v___x_2830_, 0);
                v_nextMacroScope_2834_ = leanh::lean_ctor_get(v___x_2830_, 1);
                v_ngen_2835_ = leanh::lean_ctor_get(v___x_2830_, 2);
                v_auxDeclNGen_2836_ = leanh::lean_ctor_get(v___x_2830_, 3);
                v_traceState_2837_ = leanh::lean_ctor_get(v___x_2830_, 4);
                v_cache_2838_ = leanh::lean_ctor_get(v___x_2830_, 5);
                v_messages_2839_ = leanh::lean_ctor_get(v___x_2830_, 6);
                v_infoState_2840_ = leanh::lean_ctor_get(v___x_2830_, 7);
                v_snapshotTasks_2841_ = leanh::lean_ctor_get(v___x_2830_, 8);
                v_isSharedCheck_2855_ = (!leanh::lean_is_exclusive(v___x_2830_)) as u8;
                if v_isSharedCheck_2855_ == 0 {
                    v___x_2843_ = v___x_2830_;
                    v_isShared_2844_ = v_isSharedCheck_2855_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2841_);
                    leanh::lean_inc(v_infoState_2840_);
                    leanh::lean_inc(v_messages_2839_);
                    leanh::lean_inc(v_cache_2838_);
                    leanh::lean_inc(v_traceState_2837_);
                    leanh::lean_inc(v_auxDeclNGen_2836_);
                    leanh::lean_inc(v_ngen_2835_);
                    leanh::lean_inc(v_nextMacroScope_2834_);
                    leanh::lean_inc(v_env_2833_);
                    leanh::lean_dec(v___x_2830_);
                    v___x_2843_ = leanh::lean_box(0);
                    v_isShared_2844_ = v_isSharedCheck_2855_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_openDecls_2832_);
                leanh::lean_inc(v_currNamespace_2831_);
                v___x_2845_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2845_, 0, v_currNamespace_2831_);
                leanh::lean_ctor_set(v___x_2845_, 1, v_openDecls_2832_);
                v___x_2846_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2846_, 0, v___x_2845_);
                leanh::lean_ctor_set(v___x_2846_, 1, v___y_2822_);
                leanh::lean_inc_ref(v___y_2825_);
                leanh::lean_inc_ref(v___y_2821_);
                v___x_2847_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_2847_, 0, v___y_2821_);
                leanh::lean_ctor_set(v___x_2847_, 1, v___y_2826_);
                leanh::lean_ctor_set(v___x_2847_, 2, v___y_2824_);
                leanh::lean_ctor_set(v___x_2847_, 3, v___y_2825_);
                leanh::lean_ctor_set(v___x_2847_, 4, v___x_2846_);
                leanh::lean_ctor_set_uint8(
                    v___x_2847_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_2823_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2847_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_2827_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2847_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2816_,
                );
                v___x_2848_ = l_Lean_MessageLog_add(v___x_2847_, v_messages_2839_);
                if v_isShared_2844_ == 0 {
                    leanh::lean_ctor_set(v___x_2843_, 6, v___x_2848_);
                    v___x_2850_ = v___x_2843_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2854_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_env_2833_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_nextMacroScope_2834_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_ngen_2835_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_auxDeclNGen_2836_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 4, v_traceState_2837_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 5, v_cache_2838_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 6, v___x_2848_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 7, v_infoState_2840_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 8, v_snapshotTasks_2841_);
                    v___x_2850_ = v_reuseFailAlloc_2854_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2851_ = lean_st_ref_set(v___y_2829_, v___x_2850_);
                v___x_2852_ = leanh::lean_box(0);
                v___x_2853_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2853_, 0, v___x_2852_);
                return v___x_2853_;
            }
            4 => {
                v___x_2865_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2814_,
                    );
                v___x_2866_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10(v___x_2865_, v___y_2817_, v___y_2818_);
                v_a_2867_ = leanh::lean_ctor_get(v___x_2866_, 0);
                v_isSharedCheck_2880_ = (!leanh::lean_is_exclusive(v___x_2866_)) as u8;
                if v_isSharedCheck_2880_ == 0 {
                    v___x_2869_ = v___x_2866_;
                    v_isShared_2870_ = v_isSharedCheck_2880_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2867_);
                    leanh::lean_dec(v___x_2866_);
                    v___x_2869_ = leanh::lean_box(0);
                    v_isShared_2870_ = v_isSharedCheck_2880_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref_n(v___y_2863_, 2);
                v___x_2871_ = l_Lean_FileMap_toPosition(v___y_2863_, v___y_2860_);
                leanh::lean_dec(v___y_2860_);
                v___x_2872_ = l_Lean_FileMap_toPosition(v___y_2863_, v___y_2864_);
                leanh::lean_dec(v___y_2864_);
                v___x_2873_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2873_, 0, v___x_2872_);
                v___x_2874_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___closed__0;
                if v___y_2861_ == 0 {
                    leanh::lean_del_object(v___x_2869_);
                    leanh::lean_dec_ref(v___y_2857_);
                    v___y_2821_ = v___y_2858_;
                    v___y_2822_ = v_a_2867_;
                    v___y_2823_ = v___y_2859_;
                    v___y_2824_ = v___x_2873_;
                    v___y_2825_ = v___x_2874_;
                    v___y_2826_ = v___x_2871_;
                    v___y_2827_ = v___y_2862_;
                    v___y_2828_ = v___y_2817_;
                    v___y_2829_ = v___y_2818_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2867_);
                    v___x_2875_ = l_Lean_MessageData_hasTag(v___y_2857_, v_a_2867_);
                    if v___x_2875_ == 0 {
                        leanh::lean_dec_ref_known(v___x_2873_, 1);
                        leanh::lean_dec_ref(v___x_2871_);
                        leanh::lean_dec(v_a_2867_);
                        v___x_2876_ = leanh::lean_box(0);
                        if v_isShared_2870_ == 0 {
                            leanh::lean_ctor_set(v___x_2869_, 0, v___x_2876_);
                            v___x_2878_ = v___x_2869_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2879_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2876_);
                            v___x_2878_ = v_reuseFailAlloc_2879_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2869_);
                        v___y_2821_ = v___y_2858_;
                        v___y_2822_ = v_a_2867_;
                        v___y_2823_ = v___y_2859_;
                        v___y_2824_ = v___x_2873_;
                        v___y_2825_ = v___x_2874_;
                        v___y_2826_ = v___x_2871_;
                        v___y_2827_ = v___y_2862_;
                        v___y_2828_ = v___y_2817_;
                        v___y_2829_ = v___y_2818_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2878_;
            }
            7 => {
                v___x_2890_ = l_Lean_Syntax_getTailPos_x3f(v___y_2887_, v___y_2884_);
                leanh::lean_dec(v___y_2887_);
                if leanh::lean_obj_tag(v___x_2890_) == 0 {
                    leanh::lean_inc(v___y_2889_);
                    v___y_2857_ = v___y_2882_;
                    v___y_2858_ = v___y_2883_;
                    v___y_2859_ = v___y_2884_;
                    v___y_2860_ = v___y_2889_;
                    v___y_2861_ = v___y_2885_;
                    v___y_2862_ = v___y_2886_;
                    v___y_2863_ = v___y_2888_;
                    v___y_2864_ = v___y_2889_;
                    state = 4;
                    continue;
                } else {
                    v_val_2891_ = leanh::lean_ctor_get(v___x_2890_, 0);
                    leanh::lean_inc(v_val_2891_);
                    leanh::lean_dec_ref_known(v___x_2890_, 1);
                    v___y_2857_ = v___y_2882_;
                    v___y_2858_ = v___y_2883_;
                    v___y_2859_ = v___y_2884_;
                    v___y_2860_ = v___y_2889_;
                    v___y_2861_ = v___y_2885_;
                    v___y_2862_ = v___y_2886_;
                    v___y_2863_ = v___y_2888_;
                    v___y_2864_ = v_val_2891_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_2900_ = l_Lean_replaceRef(v_ref_2813_, v___y_2895_);
                v___x_2901_ = l_Lean_Syntax_getPos_x3f(v_ref_2900_, v___y_2896_);
                if leanh::lean_obj_tag(v___x_2901_) == 0 {
                    v___x_2902_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2882_ = v___y_2893_;
                    v___y_2883_ = v___y_2894_;
                    v___y_2884_ = v___y_2896_;
                    v___y_2885_ = v___y_2897_;
                    v___y_2886_ = v___y_2899_;
                    v___y_2887_ = v_ref_2900_;
                    v___y_2888_ = v___y_2898_;
                    v___y_2889_ = v___x_2902_;
                    state = 7;
                    continue;
                } else {
                    v_val_2903_ = leanh::lean_ctor_get(v___x_2901_, 0);
                    leanh::lean_inc(v_val_2903_);
                    leanh::lean_dec_ref_known(v___x_2901_, 1);
                    v___y_2882_ = v___y_2893_;
                    v___y_2883_ = v___y_2894_;
                    v___y_2884_ = v___y_2896_;
                    v___y_2885_ = v___y_2897_;
                    v___y_2886_ = v___y_2899_;
                    v___y_2887_ = v_ref_2900_;
                    v___y_2888_ = v___y_2898_;
                    v___y_2889_ = v_val_2903_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_2912_ == 0 {
                    v___y_2893_ = v___y_2906_;
                    v___y_2894_ = v___y_2908_;
                    v___y_2895_ = v___y_2907_;
                    v___y_2896_ = v___y_2911_;
                    v___y_2897_ = v___y_2909_;
                    v___y_2898_ = v___y_2910_;
                    v___y_2899_ = v_severity_2815_;
                    state = 8;
                    continue;
                } else {
                    v___y_2893_ = v___y_2906_;
                    v___y_2894_ = v___y_2908_;
                    v___y_2895_ = v___y_2907_;
                    v___y_2896_ = v___y_2911_;
                    v___y_2897_ = v___y_2909_;
                    v___y_2898_ = v___y_2910_;
                    v___y_2899_ = v___x_2904_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_2914_ == 0 {
                    v_fileName_2915_ = leanh::lean_ctor_get(v___y_2817_, 0);
                    v_fileMap_2916_ = leanh::lean_ctor_get(v___y_2817_, 1);
                    v_options_2917_ = leanh::lean_ctor_get(v___y_2817_, 2);
                    v_ref_2918_ = leanh::lean_ctor_get(v___y_2817_, 5);
                    v_suppressElabErrors_2919_ = leanh::lean_ctor_get_uint8(
                        v___y_2817_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_2920_ = leanh::lean_box((v___y_2914_) as usize);
                    v___x_2921_ = leanh::lean_box((v_suppressElabErrors_2919_) as usize);
                    v___f_2922_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_2922_, 0, v___x_2920_);
                    leanh::lean_closure_set(v___f_2922_, 1, v___x_2921_);
                    v___x_2923_ = 1;
                    v___x_2924_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2815_, v___x_2923_);
                    if v___x_2924_ == 0 {
                        v___y_2906_ = v___f_2922_;
                        v___y_2907_ = v_ref_2918_;
                        v___y_2908_ = v_fileName_2915_;
                        v___y_2909_ = v_suppressElabErrors_2919_;
                        v___y_2910_ = v_fileMap_2916_;
                        v___y_2911_ = v___y_2914_;
                        v___y_2912_ = v___x_2924_;
                        state = 9;
                        continue;
                    } else {
                        v___x_2925_ = l_Lean_warningAsError;
                        v___x_2926_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11(v_options_2917_, v___x_2925_);
                        v___y_2906_ = v___f_2922_;
                        v___y_2907_ = v_ref_2918_;
                        v___y_2908_ = v_fileName_2915_;
                        v___y_2909_ = v_suppressElabErrors_2919_;
                        v___y_2910_ = v_fileMap_2916_;
                        v___y_2911_ = v___y_2914_;
                        v___y_2912_ = v___x_2926_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_2814_);
                    v___x_2927_ = leanh::lean_box(0);
                    v___x_2928_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2928_, 0, v___x_2927_);
                    return v___x_2928_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_ref_2931_: *mut leanh::LeanObject,
    mut v_msgData_2932_: *mut leanh::LeanObject,
    mut v_severity_2933_: *mut leanh::LeanObject,
    mut v_isSilent_2934_: *mut leanh::LeanObject,
    mut v___y_2935_: *mut leanh::LeanObject,
    mut v___y_2936_: *mut leanh::LeanObject,
    mut v___y_2937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_2938_: u8 = 0;
    let mut v_isSilent_boxed_2939_: u8 = 0;
    let mut v_res_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2938_ = (leanh::lean_unbox(v_severity_2933_) as u8);
    v_isSilent_boxed_2939_ = (leanh::lean_unbox(v_isSilent_2934_) as u8);
    v_res_2940_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6(v_ref_2931_, v_msgData_2932_, v_severity_boxed_2938_, v_isSilent_boxed_2939_, v___y_2935_, v___y_2936_);
    leanh::lean_dec(v___y_2936_);
    leanh::lean_dec_ref(v___y_2935_);
    leanh::lean_dec(v_ref_2931_);
    return v_res_2940_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4(
    mut v_msgData_2941_: *mut leanh::LeanObject,
    mut v_severity_2942_: u8,
    mut v_isSilent_2943_: u8,
    mut v___y_2944_: *mut leanh::LeanObject,
    mut v___y_2945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_2947_ = leanh::lean_ctor_get(v___y_2944_, 5);
    v___x_2948_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6(v_ref_2947_, v_msgData_2941_, v_severity_2942_, v_isSilent_2943_, v___y_2944_, v___y_2945_);
    return v___x_2948_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4___boxed(
    mut v_msgData_2949_: *mut leanh::LeanObject,
    mut v_severity_2950_: *mut leanh::LeanObject,
    mut v_isSilent_2951_: *mut leanh::LeanObject,
    mut v___y_2952_: *mut leanh::LeanObject,
    mut v___y_2953_: *mut leanh::LeanObject,
    mut v___y_2954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_2955_: u8 = 0;
    let mut v_isSilent_boxed_2956_: u8 = 0;
    let mut v_res_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2955_ = (leanh::lean_unbox(v_severity_2950_) as u8);
    v_isSilent_boxed_2956_ = (leanh::lean_unbox(v_isSilent_2951_) as u8);
    v_res_2957_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4(v_msgData_2949_, v_severity_boxed_2955_, v_isSilent_boxed_2956_, v___y_2952_, v___y_2953_);
    leanh::lean_dec(v___y_2953_);
    leanh::lean_dec_ref(v___y_2952_);
    return v_res_2957_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2(
    mut v_msgData_2958_: *mut leanh::LeanObject,
    mut v___y_2959_: *mut leanh::LeanObject,
    mut v___y_2960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2962_: u8 = 0;
    let mut v___x_2963_: u8 = 0;
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2962_ = 1;
    v___x_2963_ = 0;
    v___x_2964_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4(v_msgData_2958_, v___x_2962_, v___x_2963_, v___y_2959_, v___y_2960_);
    return v___x_2964_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2___boxed(
    mut v_msgData_2965_: *mut leanh::LeanObject,
    mut v___y_2966_: *mut leanh::LeanObject,
    mut v___y_2967_: *mut leanh::LeanObject,
    mut v___y_2968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2969_ = l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2(v_msgData_2965_, v___y_2966_, v___y_2967_);
    leanh::lean_dec(v___y_2967_);
    leanh::lean_dec_ref(v___y_2966_);
    return v_res_2969_;
}
pub unsafe fn _init_l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2971_ = l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__0;
    v___x_2972_ = l_Lean_stringToMessageData(v___x_2971_);
    return v___x_2972_;
}
pub unsafe fn l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1(
    mut v_d_2973_: *mut leanh::LeanObject,
    mut v_thmId_2974_: *mut leanh::LeanObject,
    mut v___y_2975_: *mut leanh::LeanObject,
    mut v___y_2976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2988_: u8 = 0;
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2992_: u8 = 0;
    let mut v_unused_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2997_: u8 = 0;
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3001_: u8 = 0;
    let mut v___y_3003_: u8 = 0;
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3008_: u8 = 0;
    let mut v___x_3009_: u8 = 0;
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: u8 = 0;
    let mut v_declName_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: u8 = 0;
    let mut v_toUnfoldThms_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3017_ = l_Lean_Meta_SimpTheorems_isLemma(v_d_2973_, v_thmId_2974_);
                if v___x_3017_ == 0 {
                    if leanh::lean_obj_tag(v_thmId_2974_) == 0 {
                        v_declName_3018_ = leanh::lean_ctor_get(v_thmId_2974_, 0);
                        v___x_3019_ =
                            l_Lean_Meta_SimpTheorems_isDeclToUnfold(v_d_2973_, v_declName_3018_);
                        if v___x_3019_ == 0 {
                            v_toUnfoldThms_3020_ = leanh::lean_ctor_get(v_d_2973_, 5);
                            v___x_3021_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(v_toUnfoldThms_3020_, v_declName_3018_);
                            v___y_3003_ = v___x_3021_;
                            state = 6;
                            continue;
                        } else {
                            v___y_3003_ = v___x_3019_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___y_3003_ = v___x_3017_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___y_3003_ = v___x_3017_;
                    state = 6;
                    continue;
                }
            }
            1 => {
                v___x_2979_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3);
                v___x_2980_ = l_Lean_Meta_Origin_key(v_thmId_2974_);
                leanh::lean_dec_ref(v_thmId_2974_);
                v___x_2981_ = l_Lean_MessageData_ofName(v___x_2980_);
                v___x_2982_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2982_, 0, v___x_2979_);
                leanh::lean_ctor_set(v___x_2982_, 1, v___x_2981_);
                v___x_2983_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1_once), _init_l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1);
                v___x_2984_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2984_, 0, v___x_2982_);
                leanh::lean_ctor_set(v___x_2984_, 1, v___x_2983_);
                v___x_2985_ = l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2(v___x_2984_, v___y_2975_, v___y_2976_);
                if leanh::lean_obj_tag(v___x_2985_) == 0 {
                    v_isSharedCheck_2992_ = (!leanh::lean_is_exclusive(v___x_2985_)) as u8;
                    if v_isSharedCheck_2992_ == 0 {
                        v_unused_2993_ = leanh::lean_ctor_get(v___x_2985_, 0);
                        leanh::lean_dec(v_unused_2993_);
                        v___x_2987_ = v___x_2985_;
                        v_isShared_2988_ = v_isSharedCheck_2992_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2985_);
                        v___x_2987_ = leanh::lean_box(0);
                        v_isShared_2988_ = v_isSharedCheck_2992_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_d_2973_);
                    v_a_2994_ = leanh::lean_ctor_get(v___x_2985_, 0);
                    v_isSharedCheck_3001_ = (!leanh::lean_is_exclusive(v___x_2985_)) as u8;
                    if v_isSharedCheck_3001_ == 0 {
                        v___x_2996_ = v___x_2985_;
                        v_isShared_2997_ = v_isSharedCheck_3001_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2994_);
                        leanh::lean_dec(v___x_2985_);
                        v___x_2996_ = leanh::lean_box(0);
                        v_isShared_2997_ = v_isSharedCheck_3001_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2988_ == 0 {
                    leanh::lean_ctor_set(v___x_2987_, 0, v_d_2973_);
                    v___x_2990_ = v___x_2987_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2991_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_d_2973_);
                    v___x_2990_ = v_reuseFailAlloc_2991_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2990_;
            }
            4 => {
                if v_isShared_2997_ == 0 {
                    v___x_2999_ = v___x_2996_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3000_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
                    v___x_2999_ = v_reuseFailAlloc_3000_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2999_;
            }
            6 => {
                if v___y_3003_ == 0 {
                    leanh::lean_inc_ref(v_thmId_2974_);
                    v___x_3004_ = l_Lean_Meta_Origin_converse(v_thmId_2974_);
                    if leanh::lean_obj_tag(v___x_3004_) == 1 {
                        v_val_3005_ = leanh::lean_ctor_get(v___x_3004_, 0);
                        v_isSharedCheck_3014_ =
                            (!leanh::lean_is_exclusive(v___x_3004_)) as u8;
                        if v_isSharedCheck_3014_ == 0 {
                            v___x_3007_ = v___x_3004_;
                            v_isShared_3008_ = v_isSharedCheck_3014_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3005_);
                            leanh::lean_dec(v___x_3004_);
                            v___x_3007_ = leanh::lean_box(0);
                            v_isShared_3008_ = v_isSharedCheck_3014_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3004_);
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3015_ = l_Lean_Meta_SimpTheorems_eraseCore(v_d_2973_, v_thmId_2974_);
                    v___x_3016_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3016_, 0, v___x_3015_);
                    return v___x_3016_;
                }
            }
            7 => {
                v___x_3009_ = l_Lean_Meta_SimpTheorems_isLemma(v_d_2973_, v_val_3005_);
                if v___x_3009_ == 0 {
                    leanh::lean_del_object(v___x_3007_);
                    leanh::lean_dec(v_val_3005_);
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_thmId_2974_);
                    v___x_3010_ = l_Lean_Meta_SimpTheorems_eraseCore(v_d_2973_, v_val_3005_);
                    if v_isShared_3008_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3007_, 0);
                        leanh::lean_ctor_set(v___x_3007_, 0, v___x_3010_);
                        v___x_3012_ = v___x_3007_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3013_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3010_);
                        v___x_3012_ = v_reuseFailAlloc_3013_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_3012_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___boxed(
    mut v_d_3022_: *mut leanh::LeanObject,
    mut v_thmId_3023_: *mut leanh::LeanObject,
    mut v___y_3024_: *mut leanh::LeanObject,
    mut v___y_3025_: *mut leanh::LeanObject,
    mut v___y_3026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3027_ = l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1(
        v_d_3022_,
        v_thmId_3023_,
        v___y_3024_,
        v___y_3025_,
    );
    leanh::lean_dec(v___y_3025_);
    leanh::lean_dec_ref(v___y_3024_);
    return v_res_3027_;
}
pub unsafe fn l_Lean_Meta_mkSimpAttr___lam__2(
    mut v_ext_3028_: *mut leanh::LeanObject,
    mut v_attrName_3029_: *mut leanh::LeanObject,
    mut v_declName_3030_: *mut leanh::LeanObject,
    mut v___y_3031_: *mut leanh::LeanObject,
    mut v___y_3032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: u8 = 0;
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: u8 = 0;
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: u8 = 0;
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3052_: u8 = 0;
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3064_: u8 = 0;
    let mut v___f_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3076_: u8 = 0;
    let mut v_unused_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3078_: u8 = 0;
    let mut v_a_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3082_: u8 = 0;
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3086_: u8 = 0;
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3092_: u8 = 0;
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3096_: u8 = 0;
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: u8 = 0;
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_3030_);
                v___x_3097_ = l_Lean_Meta_Simp_isSimproc___redArg(v_declName_3030_, v___y_3032_);
                if leanh::lean_obj_tag(v___x_3097_) == 0 {
                    v_a_3098_ = leanh::lean_ctor_get(v___x_3097_, 0);
                    leanh::lean_inc(v_a_3098_);
                    v___x_3099_ = (leanh::lean_unbox(v_a_3098_) as u8);
                    leanh::lean_dec(v_a_3098_);
                    if v___x_3099_ == 0 {
                        leanh::lean_dec_ref_known(v___x_3097_, 1);
                        v___x_3100_ = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(
                            v_declName_3030_,
                            v___y_3032_,
                        );
                        v___y_3035_ = v___x_3100_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3035_ = v___x_3097_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_3035_ = v___x_3097_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_3035_) == 0 {
                    v_a_3036_ = leanh::lean_ctor_get(v___y_3035_, 0);
                    leanh::lean_inc(v_a_3036_);
                    leanh::lean_dec_ref_known(v___y_3035_, 1);
                    v___x_3037_ = (leanh::lean_unbox(v_a_3036_) as u8);
                    if v___x_3037_ == 0 {
                        leanh::lean_dec(v_attrName_3029_);
                        v___x_3038_ = lean_st_ref_get(v___y_3032_);
                        v_ext_3039_ = leanh::lean_ctor_get(v_ext_3028_, 1);
                        v_toEnvExtension_3040_ = leanh::lean_ctor_get(v_ext_3039_, 0);
                        v_env_3041_ = leanh::lean_ctor_get(v___x_3038_, 0);
                        leanh::lean_inc_ref(v_env_3041_);
                        leanh::lean_dec(v___x_3038_);
                        v_asyncMode_3042_ = leanh::lean_ctor_get(v_toEnvExtension_3040_, 2);
                        v___x_3043_ = 1;
                        v___x_3044_ = l_Lean_Meta_instInhabitedSimpTheorems_default;
                        v___x_3045_ = l_Lean_ScopedEnvExtension_getState___redArg(
                            v___x_3044_,
                            v_ext_3028_,
                            v_env_3041_,
                            v_asyncMode_3042_,
                        );
                        v___x_3046_ = leanh::lean_alloc_ctor(0, 1, (2) as u32);
                        leanh::lean_ctor_set(v___x_3046_, 0, v_declName_3030_);
                        leanh::lean_ctor_set_uint8(
                            v___x_3046_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_3043_,
                        );
                        v___x_3047_ = (leanh::lean_unbox(v_a_3036_) as u8);
                        leanh::lean_dec(v_a_3036_);
                        leanh::lean_ctor_set_uint8(
                            v___x_3046_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                            v___x_3047_,
                        );
                        v___x_3048_ =
                            l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1(
                                v___x_3045_,
                                v___x_3046_,
                                v___y_3031_,
                                v___y_3032_,
                            );
                        if leanh::lean_obj_tag(v___x_3048_) == 0 {
                            v_a_3049_ = leanh::lean_ctor_get(v___x_3048_, 0);
                            v_isSharedCheck_3078_ =
                                (!leanh::lean_is_exclusive(v___x_3048_)) as u8;
                            if v_isSharedCheck_3078_ == 0 {
                                v___x_3051_ = v___x_3048_;
                                v_isShared_3052_ = v_isSharedCheck_3078_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3049_);
                                leanh::lean_dec(v___x_3048_);
                                v___x_3051_ = leanh::lean_box(0);
                                v_isShared_3052_ = v_isSharedCheck_3078_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_ext_3028_);
                            v_a_3079_ = leanh::lean_ctor_get(v___x_3048_, 0);
                            v_isSharedCheck_3086_ =
                                (!leanh::lean_is_exclusive(v___x_3048_)) as u8;
                            if v_isSharedCheck_3086_ == 0 {
                                v___x_3081_ = v___x_3048_;
                                v_isShared_3082_ = v_isSharedCheck_3086_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3079_);
                                leanh::lean_dec(v___x_3048_);
                                v___x_3081_ = leanh::lean_box(0);
                                v_isShared_3082_ = v_isSharedCheck_3086_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_3036_);
                        leanh::lean_dec_ref(v_ext_3028_);
                        v___x_3087_ =
                            l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(v_attrName_3029_);
                        v___x_3088_ = l_Lean_Attribute_erase(
                            v_declName_3030_,
                            v___x_3087_,
                            v___y_3031_,
                            v___y_3032_,
                        );
                        return v___x_3088_;
                    }
                } else {
                    leanh::lean_dec(v_declName_3030_);
                    leanh::lean_dec(v_attrName_3029_);
                    leanh::lean_dec_ref(v_ext_3028_);
                    v_a_3089_ = leanh::lean_ctor_get(v___y_3035_, 0);
                    v_isSharedCheck_3096_ = (!leanh::lean_is_exclusive(v___y_3035_)) as u8;
                    if v_isSharedCheck_3096_ == 0 {
                        v___x_3091_ = v___y_3035_;
                        v_isShared_3092_ = v_isSharedCheck_3096_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3089_);
                        leanh::lean_dec(v___y_3035_);
                        v___x_3091_ = leanh::lean_box(0);
                        v_isShared_3092_ = v_isSharedCheck_3096_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3053_ = lean_st_ref_take(v___y_3032_);
                v_env_3054_ = leanh::lean_ctor_get(v___x_3053_, 0);
                v_nextMacroScope_3055_ = leanh::lean_ctor_get(v___x_3053_, 1);
                v_ngen_3056_ = leanh::lean_ctor_get(v___x_3053_, 2);
                v_auxDeclNGen_3057_ = leanh::lean_ctor_get(v___x_3053_, 3);
                v_traceState_3058_ = leanh::lean_ctor_get(v___x_3053_, 4);
                v_messages_3059_ = leanh::lean_ctor_get(v___x_3053_, 6);
                v_infoState_3060_ = leanh::lean_ctor_get(v___x_3053_, 7);
                v_snapshotTasks_3061_ = leanh::lean_ctor_get(v___x_3053_, 8);
                v_isSharedCheck_3076_ = (!leanh::lean_is_exclusive(v___x_3053_)) as u8;
                if v_isSharedCheck_3076_ == 0 {
                    v_unused_3077_ = leanh::lean_ctor_get(v___x_3053_, 5);
                    leanh::lean_dec(v_unused_3077_);
                    v___x_3063_ = v___x_3053_;
                    v_isShared_3064_ = v_isSharedCheck_3076_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3061_);
                    leanh::lean_inc(v_infoState_3060_);
                    leanh::lean_inc(v_messages_3059_);
                    leanh::lean_inc(v_traceState_3058_);
                    leanh::lean_inc(v_auxDeclNGen_3057_);
                    leanh::lean_inc(v_ngen_3056_);
                    leanh::lean_inc(v_nextMacroScope_3055_);
                    leanh::lean_inc(v_env_3054_);
                    leanh::lean_dec(v___x_3053_);
                    v___x_3063_ = leanh::lean_box(0);
                    v_isShared_3064_ = v_isSharedCheck_3076_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___f_3065_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_mkSimpAttr___lam__1___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3065_, 0, v_a_3049_);
                v___x_3066_ = l_Lean_ScopedEnvExtension_modifyState___redArg(
                    v_ext_3028_,
                    v_env_3054_,
                    v___f_3065_,
                );
                v___x_3067_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2);
                if v_isShared_3064_ == 0 {
                    leanh::lean_ctor_set(v___x_3063_, 5, v___x_3067_);
                    leanh::lean_ctor_set(v___x_3063_, 0, v___x_3066_);
                    v___x_3069_ = v___x_3063_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3075_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3066_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_nextMacroScope_3055_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3075_, 2, v_ngen_3056_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3075_, 3, v_auxDeclNGen_3057_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3075_, 4, v_traceState_3058_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3075_, 5, v___x_3067_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3075_, 6, v_messages_3059_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3075_, 7, v_infoState_3060_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3075_, 8, v_snapshotTasks_3061_);
                    v___x_3069_ = v_reuseFailAlloc_3075_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3070_ = lean_st_ref_set(v___y_3032_, v___x_3069_);
                v___x_3071_ = leanh::lean_box(0);
                if v_isShared_3052_ == 0 {
                    leanh::lean_ctor_set(v___x_3051_, 0, v___x_3071_);
                    v___x_3073_ = v___x_3051_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3074_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3071_);
                    v___x_3073_ = v_reuseFailAlloc_3074_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3073_;
            }
            6 => {
                if v_isShared_3082_ == 0 {
                    v___x_3084_ = v___x_3081_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3085_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
                    v___x_3084_ = v_reuseFailAlloc_3085_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3084_;
            }
            8 => {
                if v_isShared_3092_ == 0 {
                    v___x_3094_ = v___x_3091_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3095_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
                    v___x_3094_ = v_reuseFailAlloc_3095_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkSimpAttr___lam__2___boxed(
    mut v_ext_3101_: *mut leanh::LeanObject,
    mut v_attrName_3102_: *mut leanh::LeanObject,
    mut v_declName_3103_: *mut leanh::LeanObject,
    mut v___y_3104_: *mut leanh::LeanObject,
    mut v___y_3105_: *mut leanh::LeanObject,
    mut v___y_3106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3107_ = l_Lean_Meta_mkSimpAttr___lam__2(
        v_ext_3101_,
        v_attrName_3102_,
        v_declName_3103_,
        v___y_3104_,
        v___y_3105_,
    );
    leanh::lean_dec(v___y_3105_);
    leanh::lean_dec_ref(v___y_3104_);
    return v_res_3107_;
}
pub unsafe fn l_Lean_Meta_mkSimpAttr(
    mut v_attrName_3108_: *mut leanh::LeanObject,
    mut v_attrDescr_3109_: *mut leanh::LeanObject,
    mut v_ext_3110_: *mut leanh::LeanObject,
    mut v_ref_3111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: u8 = 0;
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_attrName_3108_, 2);
    leanh::lean_inc_ref(v_ext_3110_);
    v___f_3113_ = leanh::lean_alloc_closure(
        l_Lean_Meta_mkSimpAttr___lam__0___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    leanh::lean_closure_set(v___f_3113_, 0, v_ext_3110_);
    leanh::lean_closure_set(v___f_3113_, 1, v_attrName_3108_);
    v___f_3114_ = leanh::lean_alloc_closure(
        l_Lean_Meta_mkSimpAttr___lam__2___boxed as *mut core::ffi::c_void,
        6,
        2,
    );
    leanh::lean_closure_set(v___f_3114_, 0, v_ext_3110_);
    leanh::lean_closure_set(v___f_3114_, 1, v_attrName_3108_);
    v___x_3115_ = 1;
    v___x_3116_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_3116_, 0, v_ref_3111_);
    leanh::lean_ctor_set(v___x_3116_, 1, v_attrName_3108_);
    leanh::lean_ctor_set(v___x_3116_, 2, v_attrDescr_3109_);
    leanh::lean_ctor_set_uint8(
        v___x_3116_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_3115_,
    );
    v___x_3117_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3117_, 0, v___x_3116_);
    leanh::lean_ctor_set(v___x_3117_, 1, v___f_3113_);
    leanh::lean_ctor_set(v___x_3117_, 2, v___f_3114_);
    v___x_3118_ = l_Lean_registerBuiltinAttribute(v___x_3117_);
    return v___x_3118_;
}
pub unsafe fn l_Lean_Meta_mkSimpAttr___boxed(
    mut v_attrName_3119_: *mut leanh::LeanObject,
    mut v_attrDescr_3120_: *mut leanh::LeanObject,
    mut v_ext_3121_: *mut leanh::LeanObject,
    mut v_ref_3122_: *mut leanh::LeanObject,
    mut v_a_3123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3124_ = l_Lean_Meta_mkSimpAttr(
        v_attrName_3119_,
        v_attrDescr_3120_,
        v_ext_3121_,
        v_ref_3122_,
    );
    return v_res_3124_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0(
    mut v_00_u03b1_3125_: *mut leanh::LeanObject,
    mut v_constName_3126_: *mut leanh::LeanObject,
    mut v___y_3127_: *mut leanh::LeanObject,
    mut v___y_3128_: *mut leanh::LeanObject,
    mut v___y_3129_: *mut leanh::LeanObject,
    mut v___y_3130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3132_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(v_constName_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
    return v___x_3132_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___boxed(
    mut v_00_u03b1_3133_: *mut leanh::LeanObject,
    mut v_constName_3134_: *mut leanh::LeanObject,
    mut v___y_3135_: *mut leanh::LeanObject,
    mut v___y_3136_: *mut leanh::LeanObject,
    mut v___y_3137_: *mut leanh::LeanObject,
    mut v___y_3138_: *mut leanh::LeanObject,
    mut v___y_3139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3140_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0(v_00_u03b1_3133_, v_constName_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
    leanh::lean_dec(v___y_3138_);
    leanh::lean_dec_ref(v___y_3137_);
    leanh::lean_dec(v___y_3136_);
    leanh::lean_dec_ref(v___y_3135_);
    return v_res_3140_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3(
    mut v_00_u03b2_3141_: *mut leanh::LeanObject,
    mut v_x_3142_: *mut leanh::LeanObject,
    mut v_x_3143_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3144_: u8 = 0;
    v___x_3144_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(v_x_3142_, v_x_3143_);
    return v___x_3144_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___boxed(
    mut v_00_u03b2_3145_: *mut leanh::LeanObject,
    mut v_x_3146_: *mut leanh::LeanObject,
    mut v_x_3147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3148_: u8 = 0;
    let mut v_r_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3148_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3(v_00_u03b2_3145_, v_x_3146_, v_x_3147_);
    leanh::lean_dec(v_x_3147_);
    leanh::lean_dec_ref(v_x_3146_);
    v_r_3149_ = leanh::lean_box((v_res_3148_) as usize);
    return v_r_3149_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1(
    mut v_00_u03b1_3150_: *mut leanh::LeanObject,
    mut v_ref_3151_: *mut leanh::LeanObject,
    mut v_constName_3152_: *mut leanh::LeanObject,
    mut v___y_3153_: *mut leanh::LeanObject,
    mut v___y_3154_: *mut leanh::LeanObject,
    mut v___y_3155_: *mut leanh::LeanObject,
    mut v___y_3156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3158_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_3151_, v_constName_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
    return v___x_3158_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_3159_: *mut leanh::LeanObject,
    mut v_ref_3160_: *mut leanh::LeanObject,
    mut v_constName_3161_: *mut leanh::LeanObject,
    mut v___y_3162_: *mut leanh::LeanObject,
    mut v___y_3163_: *mut leanh::LeanObject,
    mut v___y_3164_: *mut leanh::LeanObject,
    mut v___y_3165_: *mut leanh::LeanObject,
    mut v___y_3166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3167_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1(v_00_u03b1_3159_, v_ref_3160_, v_constName_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
    leanh::lean_dec(v___y_3165_);
    leanh::lean_dec_ref(v___y_3164_);
    leanh::lean_dec(v___y_3163_);
    leanh::lean_dec_ref(v___y_3162_);
    leanh::lean_dec(v_ref_3160_);
    return v_res_3167_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6(
    mut v_00_u03b2_3168_: *mut leanh::LeanObject,
    mut v_x_3169_: *mut leanh::LeanObject,
    mut v_x_3170_: usize,
    mut v_x_3171_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3172_: u8 = 0;
    v___x_3172_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(v_x_3169_, v_x_3170_, v_x_3171_);
    return v___x_3172_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___boxed(
    mut v_00_u03b2_3173_: *mut leanh::LeanObject,
    mut v_x_3174_: *mut leanh::LeanObject,
    mut v_x_3175_: *mut leanh::LeanObject,
    mut v_x_3176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_10027__boxed_3177_: usize = 0;
    let mut v_res_3178_: u8 = 0;
    let mut v_r_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_10027__boxed_3177_ = leanh::lean_unbox_usize(v_x_3175_);
    leanh::lean_dec(v_x_3175_);
    v_res_3178_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6(v_00_u03b2_3173_, v_x_3174_, v_x_10027__boxed_3177_, v_x_3176_);
    leanh::lean_dec(v_x_3176_);
    leanh::lean_dec_ref(v_x_3174_);
    v_r_3179_ = leanh::lean_box((v_res_3178_) as usize);
    return v_r_3179_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b1_3180_: *mut leanh::LeanObject,
    mut v_ref_3181_: *mut leanh::LeanObject,
    mut v_msg_3182_: *mut leanh::LeanObject,
    mut v_declHint_3183_: *mut leanh::LeanObject,
    mut v___y_3184_: *mut leanh::LeanObject,
    mut v___y_3185_: *mut leanh::LeanObject,
    mut v___y_3186_: *mut leanh::LeanObject,
    mut v___y_3187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3189_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3181_, v_msg_3182_, v_declHint_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
    return v___x_3189_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b1_3190_: *mut leanh::LeanObject,
    mut v_ref_3191_: *mut leanh::LeanObject,
    mut v_msg_3192_: *mut leanh::LeanObject,
    mut v_declHint_3193_: *mut leanh::LeanObject,
    mut v___y_3194_: *mut leanh::LeanObject,
    mut v___y_3195_: *mut leanh::LeanObject,
    mut v___y_3196_: *mut leanh::LeanObject,
    mut v___y_3197_: *mut leanh::LeanObject,
    mut v___y_3198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3199_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_3190_, v_ref_3191_, v_msg_3192_, v_declHint_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
    leanh::lean_dec(v___y_3197_);
    leanh::lean_dec_ref(v___y_3196_);
    leanh::lean_dec(v___y_3195_);
    leanh::lean_dec_ref(v___y_3194_);
    leanh::lean_dec(v_ref_3191_);
    return v_res_3199_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9(
    mut v_00_u03b2_3200_: *mut leanh::LeanObject,
    mut v_keys_3201_: *mut leanh::LeanObject,
    mut v_vals_3202_: *mut leanh::LeanObject,
    mut v_heq_3203_: *mut leanh::LeanObject,
    mut v_i_3204_: *mut leanh::LeanObject,
    mut v_k_3205_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3206_: u8 = 0;
    v___x_3206_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(v_keys_3201_, v_i_3204_, v_k_3205_);
    return v___x_3206_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___boxed(
    mut v_00_u03b2_3207_: *mut leanh::LeanObject,
    mut v_keys_3208_: *mut leanh::LeanObject,
    mut v_vals_3209_: *mut leanh::LeanObject,
    mut v_heq_3210_: *mut leanh::LeanObject,
    mut v_i_3211_: *mut leanh::LeanObject,
    mut v_k_3212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3213_: u8 = 0;
    let mut v_r_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3213_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9(v_00_u03b2_3207_, v_keys_3208_, v_vals_3209_, v_heq_3210_, v_i_3211_, v_k_3212_);
    leanh::lean_dec(v_k_3212_);
    leanh::lean_dec_ref(v_vals_3209_);
    leanh::lean_dec_ref(v_keys_3208_);
    v_r_3214_ = leanh::lean_box((v_res_3213_) as usize);
    return v_r_3214_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9(
    mut v_msg_3215_: *mut leanh::LeanObject,
    mut v_declHint_3216_: *mut leanh::LeanObject,
    mut v___y_3217_: *mut leanh::LeanObject,
    mut v___y_3218_: *mut leanh::LeanObject,
    mut v___y_3219_: *mut leanh::LeanObject,
    mut v___y_3220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3222_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg(v_msg_3215_, v_declHint_3216_, v___y_3220_);
    return v___x_3222_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___boxed(
    mut v_msg_3223_: *mut leanh::LeanObject,
    mut v_declHint_3224_: *mut leanh::LeanObject,
    mut v___y_3225_: *mut leanh::LeanObject,
    mut v___y_3226_: *mut leanh::LeanObject,
    mut v___y_3227_: *mut leanh::LeanObject,
    mut v___y_3228_: *mut leanh::LeanObject,
    mut v___y_3229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3230_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9(v_msg_3223_, v_declHint_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
    leanh::lean_dec(v___y_3228_);
    leanh::lean_dec_ref(v___y_3227_);
    leanh::lean_dec(v___y_3226_);
    leanh::lean_dec_ref(v___y_3225_);
    return v_res_3230_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7(
    mut v_00_u03b1_3231_: *mut leanh::LeanObject,
    mut v_ref_3232_: *mut leanh::LeanObject,
    mut v_msg_3233_: *mut leanh::LeanObject,
    mut v___y_3234_: *mut leanh::LeanObject,
    mut v___y_3235_: *mut leanh::LeanObject,
    mut v___y_3236_: *mut leanh::LeanObject,
    mut v___y_3237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3239_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_3232_, v_msg_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
    return v___x_3239_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(
    mut v_00_u03b1_3240_: *mut leanh::LeanObject,
    mut v_ref_3241_: *mut leanh::LeanObject,
    mut v_msg_3242_: *mut leanh::LeanObject,
    mut v___y_3243_: *mut leanh::LeanObject,
    mut v___y_3244_: *mut leanh::LeanObject,
    mut v___y_3245_: *mut leanh::LeanObject,
    mut v___y_3246_: *mut leanh::LeanObject,
    mut v___y_3247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3248_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b1_3240_, v_ref_3241_, v_msg_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
    leanh::lean_dec(v___y_3246_);
    leanh::lean_dec_ref(v___y_3245_);
    leanh::lean_dec(v___y_3244_);
    leanh::lean_dec_ref(v___y_3243_);
    leanh::lean_dec(v_ref_3241_);
    return v_res_3248_;
}
pub unsafe fn _init_l_Lean_Meta_registerSimpAttr___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3249_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpAttr___auto__1___closed__28_once),
        _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__28,
    );
    return v___x_3249_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(
    mut v_a_3250_: *mut leanh::LeanObject,
    mut v_b_3251_: *mut leanh::LeanObject,
    mut v_x_3252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3258_: u8 = 0;
    let mut v___x_3259_: u8 = 0;
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3267_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3252_) == 0 {
                    leanh::lean_dec(v_b_3251_);
                    leanh::lean_dec(v_a_3250_);
                    return v_x_3252_;
                } else {
                    v_key_3253_ = leanh::lean_ctor_get(v_x_3252_, 0);
                    v_value_3254_ = leanh::lean_ctor_get(v_x_3252_, 1);
                    v_tail_3255_ = leanh::lean_ctor_get(v_x_3252_, 2);
                    v_isSharedCheck_3267_ = (!leanh::lean_is_exclusive(v_x_3252_)) as u8;
                    if v_isSharedCheck_3267_ == 0 {
                        v___x_3257_ = v_x_3252_;
                        v_isShared_3258_ = v_isSharedCheck_3267_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3255_);
                        leanh::lean_inc(v_value_3254_);
                        leanh::lean_inc(v_key_3253_);
                        leanh::lean_dec(v_x_3252_);
                        v___x_3257_ = leanh::lean_box(0);
                        v_isShared_3258_ = v_isSharedCheck_3267_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3259_ = lean_name_eq(v_key_3253_, v_a_3250_);
                if v___x_3259_ == 0 {
                    v___x_3260_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(v_a_3250_, v_b_3251_, v_tail_3255_);
                    if v_isShared_3258_ == 0 {
                        leanh::lean_ctor_set(v___x_3257_, 2, v___x_3260_);
                        v___x_3262_ = v___x_3257_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3263_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_key_3253_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3263_, 1, v_value_3254_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3263_, 2, v___x_3260_);
                        v___x_3262_ = v_reuseFailAlloc_3263_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_3254_);
                    leanh::lean_dec(v_key_3253_);
                    if v_isShared_3258_ == 0 {
                        leanh::lean_ctor_set(v___x_3257_, 1, v_b_3251_);
                        leanh::lean_ctor_set(v___x_3257_, 0, v_a_3250_);
                        v___x_3265_ = v___x_3257_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3266_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3250_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3266_, 1, v_b_3251_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3266_, 2, v_tail_3255_);
                        v___x_3265_ = v_reuseFailAlloc_3266_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3262_;
            }
            3 => {
                return v___x_3265_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_3268_: *mut leanh::LeanObject,
    mut v_x_3269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3275_: u8 = 0;
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3278_: u64 = 0;
    let mut v___x_3279_: u64 = 0;
    let mut v___x_3280_: u64 = 0;
    let mut v_fold_3281_: u64 = 0;
    let mut v___x_3282_: u64 = 0;
    let mut v___x_3283_: u64 = 0;
    let mut v___x_3284_: u64 = 0;
    let mut v___x_3285_: usize = 0;
    let mut v___x_3286_: usize = 0;
    let mut v___x_3287_: usize = 0;
    let mut v___x_3288_: usize = 0;
    let mut v___x_3289_: usize = 0;
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: u64 = 0;
    let mut v_hash_3297_: u64 = 0;
    let mut v_isSharedCheck_3298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3269_) == 0 {
                    return v_x_3268_;
                } else {
                    v_key_3270_ = leanh::lean_ctor_get(v_x_3269_, 0);
                    v_value_3271_ = leanh::lean_ctor_get(v_x_3269_, 1);
                    v_tail_3272_ = leanh::lean_ctor_get(v_x_3269_, 2);
                    v_isSharedCheck_3298_ = (!leanh::lean_is_exclusive(v_x_3269_)) as u8;
                    if v_isSharedCheck_3298_ == 0 {
                        v___x_3274_ = v_x_3269_;
                        v_isShared_3275_ = v_isSharedCheck_3298_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3272_);
                        leanh::lean_inc(v_value_3271_);
                        leanh::lean_inc(v_key_3270_);
                        leanh::lean_dec(v_x_3269_);
                        v___x_3274_ = leanh::lean_box(0);
                        v_isShared_3275_ = v_isSharedCheck_3298_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3276_ = lean_array_get_size(v_x_3268_);
                if leanh::lean_obj_tag(v_key_3270_) == 0 {
                    v___x_3296_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0);
                    v___y_3278_ = v___x_3296_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3297_ = leanh::lean_ctor_get_uint64(
                        v_key_3270_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3278_ = v_hash_3297_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3279_ = 32u64;
                v___x_3280_ = lean_uint64_shift_right(v___y_3278_, v___x_3279_);
                v_fold_3281_ = lean_uint64_xor(v___y_3278_, v___x_3280_);
                v___x_3282_ = 16u64;
                v___x_3283_ = lean_uint64_shift_right(v_fold_3281_, v___x_3282_);
                v___x_3284_ = lean_uint64_xor(v_fold_3281_, v___x_3283_);
                v___x_3285_ = lean_uint64_to_usize(v___x_3284_);
                v___x_3286_ = lean_usize_of_nat(v___x_3276_);
                v___x_3287_ = 1usize;
                v___x_3288_ = lean_usize_sub(v___x_3286_, v___x_3287_);
                v___x_3289_ = lean_usize_land(v___x_3285_, v___x_3288_);
                v___x_3290_ = lean_array_uget_borrowed(v_x_3268_, v___x_3289_);
                leanh::lean_inc(v___x_3290_);
                if v_isShared_3275_ == 0 {
                    leanh::lean_ctor_set(v___x_3274_, 2, v___x_3290_);
                    v___x_3292_ = v___x_3274_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3295_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_key_3270_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3295_, 1, v_value_3271_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3295_, 2, v___x_3290_);
                    v___x_3292_ = v_reuseFailAlloc_3295_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3293_ = lean_array_uset(v_x_3268_, v___x_3289_, v___x_3292_);
                v_x_3268_ = v___x_3293_;
                v_x_3269_ = v_tail_3272_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2___redArg(
    mut v_i_3299_: *mut leanh::LeanObject,
    mut v_source_3300_: *mut leanh::LeanObject,
    mut v_target_3301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: u8 = 0;
    let mut v_es_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3302_ = lean_array_get_size(v_source_3300_);
                v___x_3303_ = lean_nat_dec_lt(v_i_3299_, v___x_3302_);
                if v___x_3303_ == 0 {
                    leanh::lean_dec_ref(v_source_3300_);
                    leanh::lean_dec(v_i_3299_);
                    return v_target_3301_;
                } else {
                    v_es_3304_ = lean_array_fget(v_source_3300_, v_i_3299_);
                    v___x_3305_ = leanh::lean_box(0);
                    v_source_3306_ = lean_array_fset(v_source_3300_, v_i_3299_, v___x_3305_);
                    v_target_3307_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_3301_, v_es_3304_);
                    v___x_3308_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3309_ = lean_nat_add(v_i_3299_, v___x_3308_);
                    leanh::lean_dec(v_i_3299_);
                    v_i_3299_ = v___x_3309_;
                    v_source_3300_ = v_source_3306_;
                    v_target_3301_ = v_target_3307_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1___redArg(
    mut v_data_3311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3312_ = lean_array_get_size(v_data_3311_);
    v___x_3313_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3314_ = lean_nat_mul(v___x_3312_, v___x_3313_);
    v___x_3315_ = leanh::lean_unsigned_to_nat(0);
    v___x_3316_ = leanh::lean_box(0);
    v___x_3317_ = lean_mk_array(v_nbuckets_3314_, v___x_3316_);
    v___x_3318_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2___redArg(v___x_3315_, v_data_3311_, v___x_3317_);
    return v___x_3318_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(
    mut v_a_3319_: *mut leanh::LeanObject,
    mut v_x_3320_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3321_: u8 = 0;
    let mut v_key_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3320_) == 0 {
                    v___x_3321_ = 0;
                    return v___x_3321_;
                } else {
                    v_key_3322_ = leanh::lean_ctor_get(v_x_3320_, 0);
                    v_tail_3323_ = leanh::lean_ctor_get(v_x_3320_, 2);
                    v___x_3324_ = lean_name_eq(v_key_3322_, v_a_3319_);
                    if v___x_3324_ == 0 {
                        v_x_3320_ = v_tail_3323_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3324_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg___boxed(
    mut v_a_3326_: *mut leanh::LeanObject,
    mut v_x_3327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3328_: u8 = 0;
    let mut v_r_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3328_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(v_a_3326_, v_x_3327_);
    leanh::lean_dec(v_x_3327_);
    leanh::lean_dec(v_a_3326_);
    v_r_3329_ = leanh::lean_box((v_res_3328_) as usize);
    return v_r_3329_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(
    mut v_m_3330_: *mut leanh::LeanObject,
    mut v_a_3331_: *mut leanh::LeanObject,
    mut v_b_3332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3337_: u8 = 0;
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3340_: u64 = 0;
    let mut v___x_3341_: u64 = 0;
    let mut v___x_3342_: u64 = 0;
    let mut v_fold_3343_: u64 = 0;
    let mut v___x_3344_: u64 = 0;
    let mut v___x_3345_: u64 = 0;
    let mut v___x_3346_: u64 = 0;
    let mut v___x_3347_: usize = 0;
    let mut v___x_3348_: usize = 0;
    let mut v___x_3349_: usize = 0;
    let mut v___x_3350_: usize = 0;
    let mut v___x_3351_: usize = 0;
    let mut v_bkt_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: u8 = 0;
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: u8 = 0;
    let mut v_val_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: u64 = 0;
    let mut v_hash_3379_: u64 = 0;
    let mut v_isSharedCheck_3380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3333_ = leanh::lean_ctor_get(v_m_3330_, 0);
                v_buckets_3334_ = leanh::lean_ctor_get(v_m_3330_, 1);
                v_isSharedCheck_3380_ = (!leanh::lean_is_exclusive(v_m_3330_)) as u8;
                if v_isSharedCheck_3380_ == 0 {
                    v___x_3336_ = v_m_3330_;
                    v_isShared_3337_ = v_isSharedCheck_3380_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_3334_);
                    leanh::lean_inc(v_size_3333_);
                    leanh::lean_dec(v_m_3330_);
                    v___x_3336_ = leanh::lean_box(0);
                    v_isShared_3337_ = v_isSharedCheck_3380_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3338_ = lean_array_get_size(v_buckets_3334_);
                if leanh::lean_obj_tag(v_a_3331_) == 0 {
                    v___x_3378_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___closed__0);
                    v___y_3340_ = v___x_3378_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3379_ = leanh::lean_ctor_get_uint64(
                        v_a_3331_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3340_ = v_hash_3379_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3341_ = 32u64;
                v___x_3342_ = lean_uint64_shift_right(v___y_3340_, v___x_3341_);
                v_fold_3343_ = lean_uint64_xor(v___y_3340_, v___x_3342_);
                v___x_3344_ = 16u64;
                v___x_3345_ = lean_uint64_shift_right(v_fold_3343_, v___x_3344_);
                v___x_3346_ = lean_uint64_xor(v_fold_3343_, v___x_3345_);
                v___x_3347_ = lean_uint64_to_usize(v___x_3346_);
                v___x_3348_ = lean_usize_of_nat(v___x_3338_);
                v___x_3349_ = 1usize;
                v___x_3350_ = lean_usize_sub(v___x_3348_, v___x_3349_);
                v___x_3351_ = lean_usize_land(v___x_3347_, v___x_3350_);
                v_bkt_3352_ = lean_array_uget_borrowed(v_buckets_3334_, v___x_3351_);
                v___x_3353_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(v_a_3331_, v_bkt_3352_);
                if v___x_3353_ == 0 {
                    v___x_3354_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3355_ = lean_nat_add(v_size_3333_, v___x_3354_);
                    leanh::lean_dec(v_size_3333_);
                    leanh::lean_inc(v_bkt_3352_);
                    v___x_3356_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_3356_, 0, v_a_3331_);
                    leanh::lean_ctor_set(v___x_3356_, 1, v_b_3332_);
                    leanh::lean_ctor_set(v___x_3356_, 2, v_bkt_3352_);
                    v_buckets_x27_3357_ =
                        lean_array_uset(v_buckets_3334_, v___x_3351_, v___x_3356_);
                    v___x_3358_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3359_ = lean_nat_mul(v_size_x27_3355_, v___x_3358_);
                    v___x_3360_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3361_ = lean_nat_div(v___x_3359_, v___x_3360_);
                    leanh::lean_dec(v___x_3359_);
                    v___x_3362_ = lean_array_get_size(v_buckets_x27_3357_);
                    v___x_3363_ = lean_nat_dec_le(v___x_3361_, v___x_3362_);
                    leanh::lean_dec(v___x_3361_);
                    if v___x_3363_ == 0 {
                        v_val_3364_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1___redArg(v_buckets_x27_3357_);
                        if v_isShared_3337_ == 0 {
                            leanh::lean_ctor_set(v___x_3336_, 1, v_val_3364_);
                            leanh::lean_ctor_set(v___x_3336_, 0, v_size_x27_3355_);
                            v___x_3366_ = v___x_3336_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3367_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3367_,
                                0,
                                v_size_x27_3355_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_val_3364_);
                            v___x_3366_ = v_reuseFailAlloc_3367_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_3337_ == 0 {
                            leanh::lean_ctor_set(v___x_3336_, 1, v_buckets_x27_3357_);
                            leanh::lean_ctor_set(v___x_3336_, 0, v_size_x27_3355_);
                            v___x_3369_ = v___x_3336_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3370_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3370_,
                                0,
                                v_size_x27_3355_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3370_,
                                1,
                                v_buckets_x27_3357_,
                            );
                            v___x_3369_ = v_reuseFailAlloc_3370_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_3352_);
                    v___x_3371_ = leanh::lean_box(0);
                    v_buckets_x27_3372_ =
                        lean_array_uset(v_buckets_3334_, v___x_3351_, v___x_3371_);
                    v___x_3373_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(v_a_3331_, v_b_3332_, v_bkt_3352_);
                    v___x_3374_ = lean_array_uset(v_buckets_x27_3372_, v___x_3351_, v___x_3373_);
                    if v_isShared_3337_ == 0 {
                        leanh::lean_ctor_set(v___x_3336_, 1, v___x_3374_);
                        v___x_3376_ = v___x_3336_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3377_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_size_3333_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3377_, 1, v___x_3374_);
                        v___x_3376_ = v_reuseFailAlloc_3377_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3366_;
            }
            4 => {
                return v___x_3369_;
            }
            5 => {
                return v___x_3376_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_registerSimpAttr(
    mut v_attrName_3381_: *mut leanh::LeanObject,
    mut v_attrDescr_3382_: *mut leanh::LeanObject,
    mut v_ref_3383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3390_: u8 = 0;
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3398_: u8 = 0;
    let mut v_unused_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3403_: u8 = 0;
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3407_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_ref_3383_);
                v___x_3385_ = l_Lean_Meta_mkSimpExt(v_ref_3383_);
                if leanh::lean_obj_tag(v___x_3385_) == 0 {
                    v_a_3386_ = leanh::lean_ctor_get(v___x_3385_, 0);
                    leanh::lean_inc_n(v_a_3386_, 2);
                    leanh::lean_dec_ref_known(v___x_3385_, 1);
                    leanh::lean_inc(v_attrName_3381_);
                    v___x_3387_ = l_Lean_Meta_mkSimpAttr(
                        v_attrName_3381_,
                        v_attrDescr_3382_,
                        v_a_3386_,
                        v_ref_3383_,
                    );
                    if leanh::lean_obj_tag(v___x_3387_) == 0 {
                        v_isSharedCheck_3398_ =
                            (!leanh::lean_is_exclusive(v___x_3387_)) as u8;
                        if v_isSharedCheck_3398_ == 0 {
                            v_unused_3399_ = leanh::lean_ctor_get(v___x_3387_, 0);
                            leanh::lean_dec(v_unused_3399_);
                            v___x_3389_ = v___x_3387_;
                            v_isShared_3390_ = v_isSharedCheck_3398_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3387_);
                            v___x_3389_ = leanh::lean_box(0);
                            v_isShared_3390_ = v_isSharedCheck_3398_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3386_);
                        leanh::lean_dec(v_attrName_3381_);
                        v_a_3400_ = leanh::lean_ctor_get(v___x_3387_, 0);
                        v_isSharedCheck_3407_ =
                            (!leanh::lean_is_exclusive(v___x_3387_)) as u8;
                        if v_isSharedCheck_3407_ == 0 {
                            v___x_3402_ = v___x_3387_;
                            v_isShared_3403_ = v_isSharedCheck_3407_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3400_);
                            leanh::lean_dec(v___x_3387_);
                            v___x_3402_ = leanh::lean_box(0);
                            v_isShared_3403_ = v_isSharedCheck_3407_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_ref_3383_);
                    leanh::lean_dec_ref(v_attrDescr_3382_);
                    leanh::lean_dec(v_attrName_3381_);
                    return v___x_3385_;
                }
            }
            1 => {
                v___x_3391_ = l_Lean_Meta_simpExtensionMapRef;
                v___x_3392_ = lean_st_ref_take(v___x_3391_);
                leanh::lean_inc(v_a_3386_);
                v___x_3393_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(v___x_3392_, v_attrName_3381_, v_a_3386_);
                v___x_3394_ = lean_st_ref_set(v___x_3391_, v___x_3393_);
                if v_isShared_3390_ == 0 {
                    leanh::lean_ctor_set(v___x_3389_, 0, v_a_3386_);
                    v___x_3396_ = v___x_3389_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3397_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3386_);
                    v___x_3396_ = v_reuseFailAlloc_3397_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3396_;
            }
            3 => {
                if v_isShared_3403_ == 0 {
                    v___x_3405_ = v___x_3402_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3406_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
                    v___x_3405_ = v_reuseFailAlloc_3406_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3405_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_registerSimpAttr___boxed(
    mut v_attrName_3408_: *mut leanh::LeanObject,
    mut v_attrDescr_3409_: *mut leanh::LeanObject,
    mut v_ref_3410_: *mut leanh::LeanObject,
    mut v_a_3411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3412_ = l_Lean_Meta_registerSimpAttr(v_attrName_3408_, v_attrDescr_3409_, v_ref_3410_);
    return v_res_3412_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0(
    mut v_00_u03b2_3413_: *mut leanh::LeanObject,
    mut v_m_3414_: *mut leanh::LeanObject,
    mut v_a_3415_: *mut leanh::LeanObject,
    mut v_b_3416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3417_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(v_m_3414_, v_a_3415_, v_b_3416_);
    return v___x_3417_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0(
    mut v_00_u03b2_3418_: *mut leanh::LeanObject,
    mut v_a_3419_: *mut leanh::LeanObject,
    mut v_x_3420_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3421_: u8 = 0;
    v___x_3421_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(v_a_3419_, v_x_3420_);
    return v___x_3421_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___boxed(
    mut v_00_u03b2_3422_: *mut leanh::LeanObject,
    mut v_a_3423_: *mut leanh::LeanObject,
    mut v_x_3424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3425_: u8 = 0;
    let mut v_r_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3425_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0(v_00_u03b2_3422_, v_a_3423_, v_x_3424_);
    leanh::lean_dec(v_x_3424_);
    leanh::lean_dec(v_a_3423_);
    v_r_3426_ = leanh::lean_box((v_res_3425_) as usize);
    return v_r_3426_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1(
    mut v_00_u03b2_3427_: *mut leanh::LeanObject,
    mut v_data_3428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3429_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1___redArg(v_data_3428_);
    return v___x_3429_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2(
    mut v_00_u03b2_3430_: *mut leanh::LeanObject,
    mut v_a_3431_: *mut leanh::LeanObject,
    mut v_b_3432_: *mut leanh::LeanObject,
    mut v_x_3433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3434_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(v_a_3431_, v_b_3432_, v_x_3433_);
    return v___x_3434_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2(
    mut v_00_u03b2_3435_: *mut leanh::LeanObject,
    mut v_i_3436_: *mut leanh::LeanObject,
    mut v_source_3437_: *mut leanh::LeanObject,
    mut v_target_3438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3439_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2___redArg(v_i_3436_, v_source_3437_, v_target_3438_);
    return v___x_3439_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_3440_: *mut leanh::LeanObject,
    mut v_x_3441_: *mut leanh::LeanObject,
    mut v_x_3442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3443_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_3441_, v_x_3442_);
    return v___x_3443_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3455_ = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_;
    v___x_3456_ = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_;
    v___x_3457_ = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_;
    v___x_3458_ = l_Lean_Meta_registerSimpAttr(v___x_3455_, v___x_3456_, v___x_3457_);
    return v___x_3458_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2____boxed(
    mut v_a_3459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3460_ = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_();
    return v_res_3460_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3471_ = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_;
    v___x_3472_ = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_;
    v___x_3473_ = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_;
    v___x_3474_ = l_Lean_Meta_registerSimpAttr(v___x_3471_, v___x_3472_, v___x_3473_);
    return v___x_3474_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2____boxed(
    mut v_a_3475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3476_ = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_();
    return v_res_3476_;
}
pub unsafe fn l_Lean_Meta_getSimpTheorems___redArg(
    mut v_a_3477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3479_ = l_Lean_Meta_simpExtension;
    v___x_3480_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_3479_, v_a_3477_);
    return v___x_3480_;
}
pub unsafe fn l_Lean_Meta_getSimpTheorems___redArg___boxed(
    mut v_a_3481_: *mut leanh::LeanObject,
    mut v_a_3482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3483_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_3481_);
    leanh::lean_dec(v_a_3481_);
    return v_res_3483_;
}
pub unsafe fn l_Lean_Meta_getSimpTheorems(
    mut v_a_3484_: *mut leanh::LeanObject,
    mut v_a_3485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3487_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_3485_);
    return v___x_3487_;
}
pub unsafe fn l_Lean_Meta_getSimpTheorems___boxed(
    mut v_a_3488_: *mut leanh::LeanObject,
    mut v_a_3489_: *mut leanh::LeanObject,
    mut v_a_3490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3491_ = l_Lean_Meta_getSimpTheorems(v_a_3488_, v_a_3489_);
    leanh::lean_dec(v_a_3489_);
    leanh::lean_dec_ref(v_a_3488_);
    return v_res_3491_;
}
pub unsafe fn l_Lean_Meta_getSEvalTheorems___redArg(
    mut v_a_3492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3494_ = l_Lean_Meta_sevalSimpExtension;
    v___x_3495_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_3494_, v_a_3492_);
    return v___x_3495_;
}
pub unsafe fn l_Lean_Meta_getSEvalTheorems___redArg___boxed(
    mut v_a_3496_: *mut leanh::LeanObject,
    mut v_a_3497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3498_ = l_Lean_Meta_getSEvalTheorems___redArg(v_a_3496_);
    leanh::lean_dec(v_a_3496_);
    return v_res_3498_;
}
pub unsafe fn l_Lean_Meta_getSEvalTheorems(
    mut v_a_3499_: *mut leanh::LeanObject,
    mut v_a_3500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3502_ = l_Lean_Meta_getSEvalTheorems___redArg(v_a_3500_);
    return v___x_3502_;
}
pub unsafe fn l_Lean_Meta_getSEvalTheorems___boxed(
    mut v_a_3503_: *mut leanh::LeanObject,
    mut v_a_3504_: *mut leanh::LeanObject,
    mut v_a_3505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3506_ = l_Lean_Meta_getSEvalTheorems(v_a_3503_, v_a_3504_);
    leanh::lean_dec(v_a_3504_);
    leanh::lean_dec_ref(v_a_3503_);
    return v_res_3506_;
}
pub unsafe fn l_Lean_Meta_Simp_Context_mkDefault___redArg(
    mut v_a_3514_: *mut leanh::LeanObject,
    mut v_a_3515_: *mut leanh::LeanObject,
    mut v_a_3516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3531_: u8 = 0;
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3535_: u8 = 0;
    let mut v_a_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3539_: u8 = 0;
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3543_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3518_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_3516_);
                if leanh::lean_obj_tag(v___x_3518_) == 0 {
                    v_a_3519_ = leanh::lean_ctor_get(v___x_3518_, 0);
                    leanh::lean_inc(v_a_3519_);
                    leanh::lean_dec_ref_known(v___x_3518_, 1);
                    v___x_3520_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_3516_);
                    if leanh::lean_obj_tag(v___x_3520_) == 0 {
                        v_a_3521_ = leanh::lean_ctor_get(v___x_3520_, 0);
                        leanh::lean_inc(v_a_3521_);
                        leanh::lean_dec_ref_known(v___x_3520_, 1);
                        v___x_3522_ = l_Lean_Meta_Simp_Context_mkDefault___redArg___closed__0;
                        v___x_3523_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3524_ = lean_mk_empty_array_with_capacity(v___x_3523_);
                        v___x_3525_ = lean_array_push(v___x_3524_, v_a_3519_);
                        v___x_3526_ = l_Lean_Options_empty;
                        v___x_3527_ = l_Lean_Meta_Simp_mkContext___redArg(
                            v___x_3522_,
                            v___x_3525_,
                            v_a_3521_,
                            v___x_3526_,
                            v_a_3514_,
                            v_a_3515_,
                            v_a_3516_,
                        );
                        return v___x_3527_;
                    } else {
                        leanh::lean_dec(v_a_3519_);
                        v_a_3528_ = leanh::lean_ctor_get(v___x_3520_, 0);
                        v_isSharedCheck_3535_ =
                            (!leanh::lean_is_exclusive(v___x_3520_)) as u8;
                        if v_isSharedCheck_3535_ == 0 {
                            v___x_3530_ = v___x_3520_;
                            v_isShared_3531_ = v_isSharedCheck_3535_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3528_);
                            leanh::lean_dec(v___x_3520_);
                            v___x_3530_ = leanh::lean_box(0);
                            v_isShared_3531_ = v_isSharedCheck_3535_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_3536_ = leanh::lean_ctor_get(v___x_3518_, 0);
                    v_isSharedCheck_3543_ = (!leanh::lean_is_exclusive(v___x_3518_)) as u8;
                    if v_isSharedCheck_3543_ == 0 {
                        v___x_3538_ = v___x_3518_;
                        v_isShared_3539_ = v_isSharedCheck_3543_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3536_);
                        leanh::lean_dec(v___x_3518_);
                        v___x_3538_ = leanh::lean_box(0);
                        v_isShared_3539_ = v_isSharedCheck_3543_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3531_ == 0 {
                    v___x_3533_ = v___x_3530_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3534_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
                    v___x_3533_ = v_reuseFailAlloc_3534_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3533_;
            }
            3 => {
                if v_isShared_3539_ == 0 {
                    v___x_3541_ = v___x_3538_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3542_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
                    v___x_3541_ = v_reuseFailAlloc_3542_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3541_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Context_mkDefault___redArg___boxed(
    mut v_a_3544_: *mut leanh::LeanObject,
    mut v_a_3545_: *mut leanh::LeanObject,
    mut v_a_3546_: *mut leanh::LeanObject,
    mut v_a_3547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3548_ = l_Lean_Meta_Simp_Context_mkDefault___redArg(v_a_3544_, v_a_3545_, v_a_3546_);
    leanh::lean_dec(v_a_3546_);
    leanh::lean_dec_ref(v_a_3545_);
    leanh::lean_dec_ref(v_a_3544_);
    return v_res_3548_;
}
pub unsafe fn l_Lean_Meta_Simp_Context_mkDefault(
    mut v_a_3549_: *mut leanh::LeanObject,
    mut v_a_3550_: *mut leanh::LeanObject,
    mut v_a_3551_: *mut leanh::LeanObject,
    mut v_a_3552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3554_ = l_Lean_Meta_Simp_Context_mkDefault___redArg(v_a_3549_, v_a_3551_, v_a_3552_);
    return v___x_3554_;
}
pub unsafe fn l_Lean_Meta_Simp_Context_mkDefault___boxed(
    mut v_a_3555_: *mut leanh::LeanObject,
    mut v_a_3556_: *mut leanh::LeanObject,
    mut v_a_3557_: *mut leanh::LeanObject,
    mut v_a_3558_: *mut leanh::LeanObject,
    mut v_a_3559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3560_ = l_Lean_Meta_Simp_Context_mkDefault(v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
    leanh::lean_dec(v_a_3558_);
    leanh::lean_dec_ref(v_a_3557_);
    leanh::lean_dec(v_a_3556_);
    leanh::lean_dec_ref(v_a_3555_);
    return v_res_3560_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_Attr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_simpExtension = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_simpExtension);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_sevalSimpExtension = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_sevalSimpExtension);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_Attr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Meta_mkSimpAttr___auto__1 = _init_l_Lean_Meta_mkSimpAttr___auto__1();
    leanh::lean_mark_persistent(l_Lean_Meta_mkSimpAttr___auto__1);
    l_Lean_Meta_registerSimpAttr___auto__1 = _init_l_Lean_Meta_registerSimpAttr___auto__1();
    leanh::lean_mark_persistent(l_Lean_Meta_registerSimpAttr___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_Attr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
}