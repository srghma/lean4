// Lean compiler output
// Module: Lean.EnvExtension
// Imports: Lean.Environment
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::Array::BinSearch::l_Array_binSearchAux___redArg;
use crate::r#gen::Init::Data::List::Basic::{l_List_appendTR___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::List::Impl::l___private_Init_Data_List_Impl_0__List_takeTR_go;
use crate::r#gen::Init::Data::Option::Basic::l_Option_isSome___boxed;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom, l_List_lengthTR___redArg, l_id___boxed,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO___aux__5___boxed;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_isAnonymous, l_Lean_Name_quickLt};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Environment::{
    initialize_Lean_Environment, l_Lean_Environment_allImportedModuleNames,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getModuleEntries___redArg,
    l_Lean_PersistentEnvExtension_getState___redArg,
    l_Lean_PersistentEnvExtension_modifyState___redArg, l_Lean_instInhabitedEnvExtension_default,
    l_Lean_registerPersistentEnvExtensionUnsafe___redArg, runtime_initialize_Lean_Environment,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_fswap;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size, lean_array_mk,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
};
pub static l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__4_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__5_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__6_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__7_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__8_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__9_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
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
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
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
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__2_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__3_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__3_value
) as *mut crate::leanh::LeanObject;
static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4_value_aux_1:
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
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4_value_aux_2:
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
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4_value:
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
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5_value:
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
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__6_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__6_value
) as *mut crate::leanh::LeanObject;
static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7_value_aux_1:
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
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7_value_aux_2:
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
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7_value:
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
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__8_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
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
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__9_value:
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
        core::ptr::addr_of!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__10_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__10_value
) as *mut crate::leanh::LeanObject;
static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11_value_aux_1:
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
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11_value_aux_2:
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
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11_value:
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
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__10_value
        ) as *mut crate::leanh::LeanObject,
        14997215300048349804 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__14_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
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
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__15_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__15_value
) as *mut crate::leanh::LeanObject;
static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16_value_aux_1:
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
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16_value_aux_2:
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
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__14_value
        ) as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16_value:
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
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__15_value
        ) as *mut crate::leanh::LeanObject,
        7677164612348466033 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__17_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__17_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__27_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2___closed__0_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 108, 111, 99, 97, 108, 32, 101, 110, 116,
        114, 105, 101, 115, 58, 32, 0,
    ],
};
static mut l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0_value:
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
static mut l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_registerSimplePersistentEnvExtension___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_registerSimplePersistentEnvExtension___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_registerSimplePersistentEnvExtension___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_registerSimplePersistentEnvExtension___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_registerSimplePersistentEnvExtension___redArg___closed__2_value:
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
static mut l_Lean_registerSimplePersistentEnvExtension___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
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
        40, 96, 73, 110, 104, 97, 98, 105, 116, 101, 100, 46, 100, 101, 102, 97, 117, 108, 116, 96,
        32, 102, 111, 114, 32, 96, 73, 79, 46, 69, 114, 114, 111, 114, 96, 41, 0,
    ],
};
static mut l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2___closed__0_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_mkTagDeclarationExtension___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_mkTagDeclarationExtension___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_NameSet_insert as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_mkTagDeclarationExtension___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkTagDeclarationExtension___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkTagDeclarationExtension___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_mkTagDeclarationExtension___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_mkTagDeclarationExtension___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkTagDeclarationExtension___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkTagDeclarationExtension___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_mkTagDeclarationExtension___lam__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_mkTagDeclarationExtension___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkTagDeclarationExtension___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkTagDeclarationExtension___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_mkTagDeclarationExtension___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_mkTagDeclarationExtension___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkTagDeclarationExtension___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkTagDeclarationExtension___closed__4_value: crate::leanh::LeanClosureObject<4> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed
            as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_mkTagDeclarationExtension___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_mkTagDeclarationExtension___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_mkTagDeclarationExtension___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkTagDeclarationExtension___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkTagDeclarationExtension___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_mkTagDeclarationExtension___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_mkTagDeclarationExtension___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkTagDeclarationExtension___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__0_value:
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
static mut l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__0_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_TagDeclarationExtension_instInhabited___aux__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_TagDeclarationExtension_instInhabited: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_TagDeclarationExtension_tag___closed__0_value: crate::leanh::LeanStringObject<
    18,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        76, 101, 97, 110, 46, 69, 110, 118, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0,
    ],
};
static mut l_Lean_TagDeclarationExtension_tag___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_TagDeclarationExtension_tag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_TagDeclarationExtension_tag___closed__1_value: crate::leanh::LeanStringObject<
    33,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        76, 101, 97, 110, 46, 84, 97, 103, 68, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 69,
        120, 116, 101, 110, 115, 105, 111, 110, 46, 116, 97, 103, 0,
    ],
};
static mut l_Lean_TagDeclarationExtension_tag___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_TagDeclarationExtension_tag___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_TagDeclarationExtension_tag___closed__2_value: crate::leanh::LeanStringObject<
    110,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 110,
    m_capacity: 110,
    m_length: 109,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 101, 110, 118, 46, 103, 101, 116, 77, 111, 100, 117, 108, 101, 73, 100, 120, 70,
        111, 114, 63, 32, 100, 101, 99, 108, 78, 97, 109, 101, 32, 124, 62, 46, 105, 115, 78, 111,
        110, 101, 32, 45, 45, 32, 83, 101, 101, 32, 99, 111, 109, 109, 101, 110, 116, 32, 97, 116,
        32, 96, 84, 97, 103, 68, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 69, 120, 116, 101,
        110, 115, 105, 111, 110, 96, 10, 32, 32, 32, 32, 0,
    ],
};
static mut l_Lean_TagDeclarationExtension_tag___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_TagDeclarationExtension_tag___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_TagDeclarationExtension_tag___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_TagDeclarationExtension_tag___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_TagDeclarationExtension_isTagged___closed__0_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_TagDeclarationExtension_isTagged___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_TagDeclarationExtension_isTagged___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__0_value:
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
static mut l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__0_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instInhabitedMapDeclarationExtension_default___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instInhabitedMapDeclarationExtension_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedMapDeclarationExtension_default___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instInhabitedMapDeclarationExtension_default___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instInhabitedMapDeclarationExtension_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedMapDeclarationExtension_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedMapDeclarationExtension_default___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instInhabitedMapDeclarationExtension_default___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedMapDeclarationExtension_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedMapDeclarationExtension_default___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instInhabitedMapDeclarationExtension_default___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instInhabitedMapDeclarationExtension_default___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedMapDeclarationExtension_default___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instInhabitedMapDeclarationExtension_default___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedMapDeclarationExtension_default___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instInhabitedMapDeclarationExtension_default___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedMapDeclarationExtension_default___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instInhabitedMapDeclarationExtension___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedMapDeclarationExtension___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_mkMapDeclarationExtension___auto__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_mkMapDeclarationExtension___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_mkMapDeclarationExtension___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_mkMapDeclarationExtension___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkMapDeclarationExtension___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkMapDeclarationExtension___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_mkMapDeclarationExtension___redArg___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_mkMapDeclarationExtension___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkMapDeclarationExtension___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkMapDeclarationExtension___redArg___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_mkMapDeclarationExtension___redArg___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_mkMapDeclarationExtension___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkMapDeclarationExtension___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkMapDeclarationExtension___redArg___closed__3_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_mkMapDeclarationExtension___redArg___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_mkMapDeclarationExtension___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkMapDeclarationExtension___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkMapDeclarationExtension___redArg___closed__4_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_mkMapDeclarationExtension___redArg___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_mkMapDeclarationExtension___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkMapDeclarationExtension___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkMapDeclarationExtension___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_mkMapDeclarationExtension___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_mkMapDeclarationExtension___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkMapDeclarationExtension___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MapDeclarationExtension_insert___redArg___closed__0_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        76, 101, 97, 110, 46, 77, 97, 112, 68, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 69,
        120, 116, 101, 110, 115, 105, 111, 110, 46, 105, 110, 115, 101, 114, 116, 0,
    ],
};
static mut l_Lean_MapDeclarationExtension_insert___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MapDeclarationExtension_insert___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MapDeclarationExtension_insert___redArg___closed__1_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
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
        99, 97, 110, 110, 111, 116, 32, 105, 110, 115, 101, 114, 116, 32, 96, 0,
    ],
};
static mut l_Lean_MapDeclarationExtension_insert___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MapDeclarationExtension_insert___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MapDeclarationExtension_insert___redArg___closed__2_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [96, 32, 105, 110, 116, 111, 32, 96, 0],
};
static mut l_Lean_MapDeclarationExtension_insert___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MapDeclarationExtension_insert___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MapDeclarationExtension_insert___redArg___closed__3_value:
    crate::leanh::LeanStringObject<52> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 52,
    m_capacity: 52,
    m_length: 51,
    m_data: [
        96, 44, 32, 105, 116, 32, 105, 115, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 101,
        100, 32, 105, 110, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111,
        100, 117, 108, 101, 32, 98, 117, 116, 32, 105, 110, 32, 96, 0,
    ],
};
static mut l_Lean_MapDeclarationExtension_insert___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MapDeclarationExtension_insert___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MapDeclarationExtension_insert___redArg___closed__4_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [96, 0],
};
static mut l_Lean_MapDeclarationExtension_insert___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MapDeclarationExtension_insert___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_id___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MapDeclarationExtension_contains___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_isSome___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_MapDeclarationExtension_contains___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MapDeclarationExtension_contains___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_mkStateFromImportedEntries___redArg___lam__0(
    mut v_addEntryFn_1123_: *mut crate::leanh::LeanObject,
    mut v_x1_1124_: *mut crate::leanh::LeanObject,
    mut v_x2_1125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1126_ = crate::leanh::lean_apply_2(v_addEntryFn_1123_, v_x1_1124_, v_x2_1125_);
    return v___x_1126_;
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___redArg___lam__1(
    mut v___f_1146_: *mut crate::leanh::LeanObject,
    mut v_x1_1147_: *mut crate::leanh::LeanObject,
    mut v_x2_1148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: u8 = 0;
    v___x_1149_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1150_ = lean_array_get_size(v_x2_1148_);
    v___x_1151_ = l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__9;
    v___x_1152_ = lean_nat_dec_lt(v___x_1149_, v___x_1150_);
    if v___x_1152_ == 0 {
        crate::leanh::lean_dec_ref(v_x2_1148_);
        crate::leanh::lean_dec(v___f_1146_);
        return v_x1_1147_;
    } else {
        let mut v___x_1153_: u8 = 0;
        v___x_1153_ = lean_nat_dec_le(v___x_1150_, v___x_1150_);
        if v___x_1153_ == 0 {
            if v___x_1152_ == 0 {
                crate::leanh::lean_dec_ref(v_x2_1148_);
                crate::leanh::lean_dec(v___f_1146_);
                return v_x1_1147_;
            } else {
                let mut v___x_1154_: usize = 0;
                let mut v___x_1155_: usize = 0;
                let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1154_ = 0usize;
                v___x_1155_ = lean_usize_of_nat(v___x_1150_);
                v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1151_,
                    v___f_1146_,
                    v_x2_1148_,
                    v___x_1154_,
                    v___x_1155_,
                    v_x1_1147_,
                );
                return v___x_1156_;
            }
        } else {
            let mut v___x_1157_: usize = 0;
            let mut v___x_1158_: usize = 0;
            let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1157_ = 0usize;
            v___x_1158_ = lean_usize_of_nat(v___x_1150_);
            v___x_1159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1151_,
                v___f_1146_,
                v_x2_1148_,
                v___x_1157_,
                v___x_1158_,
                v_x1_1147_,
            );
            return v___x_1159_;
        }
    }
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___redArg(
    mut v_addEntryFn_1160_: *mut crate::leanh::LeanObject,
    mut v_initState_1161_: *mut crate::leanh::LeanObject,
    mut v_as_1162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: u8 = 0;
    v___x_1163_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1164_ = lean_array_get_size(v_as_1162_);
    v___x_1165_ = l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__9;
    v___x_1166_ = lean_nat_dec_lt(v___x_1163_, v___x_1164_);
    if v___x_1166_ == 0 {
        crate::leanh::lean_dec_ref(v_as_1162_);
        crate::leanh::lean_dec(v_addEntryFn_1160_);
        return v_initState_1161_;
    } else {
        let mut v___f_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1169_: u8 = 0;
        v___f_1167_ = crate::leanh::lean_alloc_closure(
            l_Lean_mkStateFromImportedEntries___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_1167_, 0, v_addEntryFn_1160_);
        v___f_1168_ = crate::leanh::lean_alloc_closure(
            l_Lean_mkStateFromImportedEntries___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_1168_, 0, v___f_1167_);
        v___x_1169_ = lean_nat_dec_le(v___x_1164_, v___x_1164_);
        if v___x_1169_ == 0 {
            if v___x_1166_ == 0 {
                crate::leanh::lean_dec_ref(v___f_1168_);
                crate::leanh::lean_dec_ref(v_as_1162_);
                return v_initState_1161_;
            } else {
                let mut v___x_1170_: usize = 0;
                let mut v___x_1171_: usize = 0;
                let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1170_ = 0usize;
                v___x_1171_ = lean_usize_of_nat(v___x_1164_);
                v___x_1172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1165_,
                    v___f_1168_,
                    v_as_1162_,
                    v___x_1170_,
                    v___x_1171_,
                    v_initState_1161_,
                );
                return v___x_1172_;
            }
        } else {
            let mut v___x_1173_: usize = 0;
            let mut v___x_1174_: usize = 0;
            let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1173_ = 0usize;
            v___x_1174_ = lean_usize_of_nat(v___x_1164_);
            v___x_1175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1165_,
                v___f_1168_,
                v_as_1162_,
                v___x_1173_,
                v___x_1174_,
                v_initState_1161_,
            );
            return v___x_1175_;
        }
    }
}
pub unsafe fn l_Lean_mkStateFromImportedEntries(
    mut v_00_u03b1_1176_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1177_: *mut crate::leanh::LeanObject,
    mut v_addEntryFn_1178_: *mut crate::leanh::LeanObject,
    mut v_initState_1179_: *mut crate::leanh::LeanObject,
    mut v_as_1180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1181_ = l_Lean_mkStateFromImportedEntries___redArg(
        v_addEntryFn_1178_,
        v_initState_1179_,
        v_as_1180_,
    );
    return v___x_1181_;
}
pub unsafe fn _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1208_ = l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__10;
    v___x_1209_ = l_Lean_mkAtom(v___x_1208_);
    return v___x_1209_;
}
pub unsafe fn _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1210_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__12_once
        ),
        _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__12,
    );
    v___x_1211_ = l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5;
    v___x_1212_ = lean_array_push(v___x_1211_, v___x_1210_);
    return v___x_1212_;
}
pub unsafe fn _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1221_ = l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__17;
    v___x_1222_ = l_Lean_mkAtom(v___x_1221_);
    return v___x_1222_;
}
pub unsafe fn _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1223_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__18
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__18_once
        ),
        _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__18,
    );
    v___x_1224_ = l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5;
    v___x_1225_ = lean_array_push(v___x_1224_, v___x_1223_);
    return v___x_1225_;
}
pub unsafe fn _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1226_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__19
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__19_once
        ),
        _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__19,
    );
    v___x_1227_ = l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16;
    v___x_1228_ = crate::leanh::lean_box(2);
    v___x_1229_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1229_, 0, v___x_1228_);
    crate::leanh::lean_ctor_set(v___x_1229_, 1, v___x_1227_);
    crate::leanh::lean_ctor_set(v___x_1229_, 2, v___x_1226_);
    return v___x_1229_;
}
pub unsafe fn _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1230_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__20
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__20_once
        ),
        _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__20,
    );
    v___x_1231_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__13_once
        ),
        _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__13,
    );
    v___x_1232_ = lean_array_push(v___x_1231_, v___x_1230_);
    return v___x_1232_;
}
pub unsafe fn _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1233_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__21
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__21_once
        ),
        _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__21,
    );
    v___x_1234_ = l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11;
    v___x_1235_ = crate::leanh::lean_box(2);
    v___x_1236_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1236_, 0, v___x_1235_);
    crate::leanh::lean_ctor_set(v___x_1236_, 1, v___x_1234_);
    crate::leanh::lean_ctor_set(v___x_1236_, 2, v___x_1233_);
    return v___x_1236_;
}
pub unsafe fn _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1237_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__22
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__22_once
        ),
        _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__22,
    );
    v___x_1238_ = l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5;
    v___x_1239_ = lean_array_push(v___x_1238_, v___x_1237_);
    return v___x_1239_;
}
pub unsafe fn _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1240_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__23
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__23_once
        ),
        _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__23,
    );
    v___x_1241_ = l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__9;
    v___x_1242_ = crate::leanh::lean_box(2);
    v___x_1243_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1243_, 0, v___x_1242_);
    crate::leanh::lean_ctor_set(v___x_1243_, 1, v___x_1241_);
    crate::leanh::lean_ctor_set(v___x_1243_, 2, v___x_1240_);
    return v___x_1243_;
}
pub unsafe fn _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1244_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__24
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__24_once
        ),
        _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__24,
    );
    v___x_1245_ = l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5;
    v___x_1246_ = lean_array_push(v___x_1245_, v___x_1244_);
    return v___x_1246_;
}
pub unsafe fn _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1247_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__25
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__25_once
        ),
        _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__25,
    );
    v___x_1248_ = l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7;
    v___x_1249_ = crate::leanh::lean_box(2);
    v___x_1250_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1250_, 0, v___x_1249_);
    crate::leanh::lean_ctor_set(v___x_1250_, 1, v___x_1248_);
    crate::leanh::lean_ctor_set(v___x_1250_, 2, v___x_1247_);
    return v___x_1250_;
}
pub unsafe fn _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1251_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__26
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__26_once
        ),
        _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__26,
    );
    v___x_1252_ = l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5;
    v___x_1253_ = lean_array_push(v___x_1252_, v___x_1251_);
    return v___x_1253_;
}
pub unsafe fn _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1254_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__27
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__27_once
        ),
        _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__27,
    );
    v___x_1255_ = l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4;
    v___x_1256_ = crate::leanh::lean_box(2);
    v___x_1257_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1257_, 0, v___x_1256_);
    crate::leanh::lean_ctor_set(v___x_1257_, 1, v___x_1255_);
    crate::leanh::lean_ctor_set(v___x_1257_, 2, v___x_1254_);
    return v___x_1257_;
}
pub unsafe fn _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1258_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once
        ),
        _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28,
    );
    return v___x_1258_;
}
pub unsafe fn l_List_foldl___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__1___redArg(
    mut v_addEntryFn_1259_: *mut crate::leanh::LeanObject,
    mut v_x_1260_: *mut crate::leanh::LeanObject,
    mut v_x_1261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1261_) == 0 {
                    crate::leanh::lean_dec(v_addEntryFn_1259_);
                    return v_x_1260_;
                } else {
                    v_head_1262_ = crate::leanh::lean_ctor_get(v_x_1261_, 0);
                    crate::leanh::lean_inc(v_head_1262_);
                    v_tail_1263_ = crate::leanh::lean_ctor_get(v_x_1261_, 1);
                    crate::leanh::lean_inc(v_tail_1263_);
                    crate::leanh::lean_dec_ref_known(v_x_1261_, 2);
                    crate::leanh::lean_inc(v_addEntryFn_1259_);
                    v___x_1264_ =
                        crate::leanh::lean_apply_2(v_addEntryFn_1259_, v_x_1260_, v_head_1262_);
                    v_x_1260_ = v___x_1264_;
                    v_x_1261_ = v_tail_1263_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__0___redArg(
    mut v___x_1266_: *mut crate::leanh::LeanObject,
    mut v_a_1267_: *mut crate::leanh::LeanObject,
    mut v_a_1268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1274_: u8 = 0;
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: u8 = 0;
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1267_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_1266_);
                    v___x_1269_ = l_List_reverse___redArg(v_a_1268_);
                    return v___x_1269_;
                } else {
                    v_head_1270_ = crate::leanh::lean_ctor_get(v_a_1267_, 0);
                    v_tail_1271_ = crate::leanh::lean_ctor_get(v_a_1267_, 1);
                    v_isSharedCheck_1282_ = (!crate::leanh::lean_is_exclusive(v_a_1267_)) as u8;
                    if v_isSharedCheck_1282_ == 0 {
                        v___x_1273_ = v_a_1267_;
                        v_isShared_1274_ = v_isSharedCheck_1282_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1271_);
                        crate::leanh::lean_inc(v_head_1270_);
                        crate::leanh::lean_dec(v_a_1267_);
                        v___x_1273_ = crate::leanh::lean_box(0);
                        v_isShared_1274_ = v_isSharedCheck_1282_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___x_1266_);
                crate::leanh::lean_inc(v_head_1270_);
                v___x_1275_ = crate::leanh::lean_apply_1(v___x_1266_, v_head_1270_);
                v___x_1276_ = (crate::leanh::lean_unbox(v___x_1275_) as u8);
                if v___x_1276_ == 0 {
                    crate::leanh::lean_del_object(v___x_1273_);
                    crate::leanh::lean_dec(v_head_1270_);
                    v_a_1267_ = v_tail_1271_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_1274_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1273_, 1, v_a_1268_);
                        v___x_1279_ = v___x_1273_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1281_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_head_1270_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_a_1268_);
                        v___x_1279_ = v_reuseFailAlloc_1281_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_a_1267_ = v_tail_1271_;
                v_a_1268_ = v___x_1279_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_replayOfFilter___redArg(
    mut v_p_1283_: *mut crate::leanh::LeanObject,
    mut v_addEntryFn_1284_: *mut crate::leanh::LeanObject,
    mut v_newEntries_1285_: *mut crate::leanh::LeanObject,
    mut v_s_1286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_s_1286_);
    v___x_1287_ = crate::leanh::lean_apply_1(v_p_1283_, v_s_1286_);
    v___x_1288_ = crate::leanh::lean_box(0);
    v_newEntries_1289_ = l_List_filterTR_loop___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__0___redArg(v___x_1287_, v_newEntries_1285_, v___x_1288_);
    crate::leanh::lean_inc(v_newEntries_1289_);
    v___x_1290_ =
        l_List_foldl___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__1___redArg(
            v_addEntryFn_1284_,
            v_s_1286_,
            v_newEntries_1289_,
        );
    v___x_1291_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1291_, 0, v_newEntries_1289_);
    crate::leanh::lean_ctor_set(v___x_1291_, 1, v___x_1290_);
    return v___x_1291_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_replayOfFilter(
    mut v_00_u03c3_1292_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1293_: *mut crate::leanh::LeanObject,
    mut v_p_1294_: *mut crate::leanh::LeanObject,
    mut v_addEntryFn_1295_: *mut crate::leanh::LeanObject,
    mut v_newEntries_1296_: *mut crate::leanh::LeanObject,
    mut v_x_1297_: *mut crate::leanh::LeanObject,
    mut v_s_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1299_ = l_Lean_SimplePersistentEnvExtension_replayOfFilter___redArg(
        v_p_1294_,
        v_addEntryFn_1295_,
        v_newEntries_1296_,
        v_s_1298_,
    );
    return v___x_1299_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(
    mut v_00_u03c3_1300_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1301_: *mut crate::leanh::LeanObject,
    mut v_p_1302_: *mut crate::leanh::LeanObject,
    mut v_addEntryFn_1303_: *mut crate::leanh::LeanObject,
    mut v_newEntries_1304_: *mut crate::leanh::LeanObject,
    mut v_x_1305_: *mut crate::leanh::LeanObject,
    mut v_s_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1307_ = l_Lean_SimplePersistentEnvExtension_replayOfFilter(
        v_00_u03c3_1300_,
        v_00_u03b1_1301_,
        v_p_1302_,
        v_addEntryFn_1303_,
        v_newEntries_1304_,
        v_x_1305_,
        v_s_1306_,
    );
    crate::leanh::lean_dec(v_x_1305_);
    return v_res_1307_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__0(
    mut v_00_u03b1_1308_: *mut crate::leanh::LeanObject,
    mut v___x_1309_: *mut crate::leanh::LeanObject,
    mut v_a_1310_: *mut crate::leanh::LeanObject,
    mut v_a_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1312_ = l_List_filterTR_loop___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__0___redArg(v___x_1309_, v_a_1310_, v_a_1311_);
    return v___x_1312_;
}
pub unsafe fn l_List_foldl___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__1(
    mut v_00_u03c3_1313_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1314_: *mut crate::leanh::LeanObject,
    mut v_addEntryFn_1315_: *mut crate::leanh::LeanObject,
    mut v_x_1316_: *mut crate::leanh::LeanObject,
    mut v_x_1317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1318_ =
        l_List_foldl___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__1___redArg(
            v_addEntryFn_1315_,
            v_x_1316_,
            v_x_1317_,
        );
    return v___x_1318_;
}
pub unsafe fn l_Lean_registerSimplePersistentEnvExtension___redArg___lam__0(
    mut v_addEntryFn_1319_: *mut crate::leanh::LeanObject,
    mut v_s_1320_: *mut crate::leanh::LeanObject,
    mut v_e_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1326_: u8 = 0;
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1332_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1322_ = crate::leanh::lean_ctor_get(v_s_1320_, 0);
                v_snd_1323_ = crate::leanh::lean_ctor_get(v_s_1320_, 1);
                v_isSharedCheck_1332_ = (!crate::leanh::lean_is_exclusive(v_s_1320_)) as u8;
                if v_isSharedCheck_1332_ == 0 {
                    v___x_1325_ = v_s_1320_;
                    v_isShared_1326_ = v_isSharedCheck_1332_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1323_);
                    crate::leanh::lean_inc(v_fst_1322_);
                    crate::leanh::lean_dec(v_s_1320_);
                    v___x_1325_ = crate::leanh::lean_box(0);
                    v_isShared_1326_ = v_isSharedCheck_1332_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_e_1321_);
                v___x_1327_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1327_, 0, v_e_1321_);
                crate::leanh::lean_ctor_set(v___x_1327_, 1, v_fst_1322_);
                v___x_1328_ =
                    crate::leanh::lean_apply_2(v_addEntryFn_1319_, v_snd_1323_, v_e_1321_);
                if v_isShared_1326_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1325_, 1, v___x_1328_);
                    crate::leanh::lean_ctor_set(v___x_1325_, 0, v___x_1327_);
                    v___x_1330_ = v___x_1325_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1331_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1327_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1331_, 1, v___x_1328_);
                    v___x_1330_ = v_reuseFailAlloc_1331_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1330_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_registerSimplePersistentEnvExtension___redArg___lam__1(
    mut v_exportEntriesFnEx_x3f_1333_: *mut crate::leanh::LeanObject,
    mut v_toArrayFn_1334_: *mut crate::leanh::LeanObject,
    mut v_env_1335_: *mut crate::leanh::LeanObject,
    mut v_s_1336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_exportEntriesFnEx_x3f_1333_) == 0 {
        let mut v_fst_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_env_1335_);
        v_fst_1337_ = crate::leanh::lean_ctor_get(v_s_1336_, 0);
        crate::leanh::lean_inc(v_fst_1337_);
        crate::leanh::lean_dec_ref(v_s_1336_);
        v___x_1338_ = l_List_reverse___redArg(v_fst_1337_);
        v___x_1339_ = crate::leanh::lean_apply_1(v_toArrayFn_1334_, v___x_1338_);
        crate::leanh::lean_inc_ref_n(v___x_1339_, 2);
        v___x_1340_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1340_, 0, v___x_1339_);
        crate::leanh::lean_ctor_set(v___x_1340_, 1, v___x_1339_);
        crate::leanh::lean_ctor_set(v___x_1340_, 2, v___x_1339_);
        return v___x_1340_;
    } else {
        let mut v_val_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_toArrayFn_1334_);
        v_val_1341_ = crate::leanh::lean_ctor_get(v_exportEntriesFnEx_x3f_1333_, 0);
        crate::leanh::lean_inc(v_val_1341_);
        crate::leanh::lean_dec_ref_known(v_exportEntriesFnEx_x3f_1333_, 1);
        v_fst_1342_ = crate::leanh::lean_ctor_get(v_s_1336_, 0);
        crate::leanh::lean_inc(v_fst_1342_);
        v_snd_1343_ = crate::leanh::lean_ctor_get(v_s_1336_, 1);
        crate::leanh::lean_inc(v_snd_1343_);
        crate::leanh::lean_dec_ref(v_s_1336_);
        v___x_1344_ = l_List_reverse___redArg(v_fst_1342_);
        v___x_1345_ =
            crate::leanh::lean_apply_3(v_val_1341_, v_env_1335_, v_snd_1343_, v___x_1344_);
        return v___x_1345_;
    }
}
pub unsafe fn l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2(
    mut v_s_1349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1353_: u8 = 0;
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1361_: u8 = 0;
    let mut v_unused_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1350_ = crate::leanh::lean_ctor_get(v_s_1349_, 0);
                v_isSharedCheck_1361_ = (!crate::leanh::lean_is_exclusive(v_s_1349_)) as u8;
                if v_isSharedCheck_1361_ == 0 {
                    v_unused_1362_ = crate::leanh::lean_ctor_get(v_s_1349_, 1);
                    crate::leanh::lean_dec(v_unused_1362_);
                    v___x_1352_ = v_s_1349_;
                    v_isShared_1353_ = v_isSharedCheck_1361_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_1350_);
                    crate::leanh::lean_dec(v_s_1349_);
                    v___x_1352_ = crate::leanh::lean_box(0);
                    v_isShared_1353_ = v_isSharedCheck_1361_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1354_ =
                    l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2___closed__1;
                v___x_1355_ = l_List_lengthTR___redArg(v_fst_1350_);
                crate::leanh::lean_dec(v_fst_1350_);
                v___x_1356_ = l_Nat_reprFast(v___x_1355_);
                v___x_1357_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1357_, 0, v___x_1356_);
                if v_isShared_1353_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1352_, 5);
                    crate::leanh::lean_ctor_set(v___x_1352_, 1, v___x_1357_);
                    crate::leanh::lean_ctor_set(v___x_1352_, 0, v___x_1354_);
                    v___x_1359_ = v___x_1352_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1360_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1354_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1360_, 1, v___x_1357_);
                    v___x_1359_ = v_reuseFailAlloc_1360_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1359_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3(
    mut v_x_1365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1366_ = l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0;
    return v___x_1366_;
}
pub unsafe fn l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___boxed(
    mut v_x_1367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1368_ = l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3(v_x_1367_);
    crate::leanh::lean_dec_ref(v_x_1367_);
    return v_res_1368_;
}
pub unsafe fn l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4(
    mut v_addImportedFn_1369_: *mut crate::leanh::LeanObject,
    mut v___x_1370_: *mut crate::leanh::LeanObject,
    mut v_as_1371_: *mut crate::leanh::LeanObject,
    mut v___y_1372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1374_ = crate::leanh::lean_apply_1(v_addImportedFn_1369_, v_as_1371_);
    v___x_1375_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1375_, 0, v___x_1370_);
    crate::leanh::lean_ctor_set(v___x_1375_, 1, v___x_1374_);
    v___x_1376_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1376_, 0, v___x_1375_);
    return v___x_1376_;
}
pub unsafe fn l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4___boxed(
    mut v_addImportedFn_1377_: *mut crate::leanh::LeanObject,
    mut v___x_1378_: *mut crate::leanh::LeanObject,
    mut v_as_1379_: *mut crate::leanh::LeanObject,
    mut v___y_1380_: *mut crate::leanh::LeanObject,
    mut v___y_1381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1382_ = l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4(
        v_addImportedFn_1377_,
        v___x_1378_,
        v_as_1379_,
        v___y_1380_,
    );
    crate::leanh::lean_dec_ref(v___y_1380_);
    return v_res_1382_;
}
pub unsafe fn l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5(
    mut v___x_1383_: *mut crate::leanh::LeanObject,
    mut v_val_1384_: *mut crate::leanh::LeanObject,
    mut v___y_1385_: *mut crate::leanh::LeanObject,
    mut v___y_1386_: *mut crate::leanh::LeanObject,
    mut v___y_1387_: *mut crate::leanh::LeanObject,
    mut v___y_1388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1404_: u8 = 0;
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1409_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1389_ = crate::leanh::lean_ctor_get(v___y_1388_, 0);
                crate::leanh::lean_inc(v_fst_1389_);
                v_snd_1390_ = crate::leanh::lean_ctor_get(v___y_1388_, 1);
                crate::leanh::lean_inc(v_snd_1390_);
                crate::leanh::lean_dec_ref(v___y_1388_);
                v_fst_1391_ = crate::leanh::lean_ctor_get(v___y_1386_, 0);
                crate::leanh::lean_inc_n(v_fst_1391_, 2);
                v_snd_1392_ = crate::leanh::lean_ctor_get(v___y_1386_, 1);
                crate::leanh::lean_inc(v_snd_1392_);
                crate::leanh::lean_dec_ref(v___y_1386_);
                v_fst_1393_ = crate::leanh::lean_ctor_get(v___y_1385_, 0);
                v___x_1394_ = l_List_lengthTR___redArg(v_fst_1391_);
                v___x_1395_ = l_List_lengthTR___redArg(v_fst_1393_);
                v___x_1396_ = lean_nat_sub(v___x_1394_, v___x_1395_);
                crate::leanh::lean_dec(v___x_1395_);
                crate::leanh::lean_dec(v___x_1394_);
                v___x_1397_ = lean_mk_empty_array_with_capacity(v___x_1383_);
                v_newEntries_1398_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    crate::leanh::lean_box(0),
                    v_fst_1391_,
                    v_fst_1391_,
                    v___x_1396_,
                    v___x_1397_,
                );
                crate::leanh::lean_dec(v_fst_1391_);
                v___x_1399_ = crate::leanh::lean_apply_3(
                    v_val_1384_,
                    v_newEntries_1398_,
                    v_snd_1392_,
                    v_snd_1390_,
                );
                v_fst_1400_ = crate::leanh::lean_ctor_get(v___x_1399_, 0);
                v_snd_1401_ = crate::leanh::lean_ctor_get(v___x_1399_, 1);
                v_isSharedCheck_1409_ = (!crate::leanh::lean_is_exclusive(v___x_1399_)) as u8;
                if v_isSharedCheck_1409_ == 0 {
                    v___x_1403_ = v___x_1399_;
                    v_isShared_1404_ = v_isSharedCheck_1409_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1401_);
                    crate::leanh::lean_inc(v_fst_1400_);
                    crate::leanh::lean_dec(v___x_1399_);
                    v___x_1403_ = crate::leanh::lean_box(0);
                    v_isShared_1404_ = v_isSharedCheck_1409_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1405_ = l_List_appendTR___redArg(v_fst_1400_, v_fst_1389_);
                if v_isShared_1404_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1403_, 0, v___x_1405_);
                    v___x_1407_ = v___x_1403_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1408_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_snd_1401_);
                    v___x_1407_ = v_reuseFailAlloc_1408_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1407_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5___boxed(
    mut v___x_1410_: *mut crate::leanh::LeanObject,
    mut v_val_1411_: *mut crate::leanh::LeanObject,
    mut v___y_1412_: *mut crate::leanh::LeanObject,
    mut v___y_1413_: *mut crate::leanh::LeanObject,
    mut v___y_1414_: *mut crate::leanh::LeanObject,
    mut v___y_1415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1416_ = l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5(
        v___x_1410_,
        v_val_1411_,
        v___y_1412_,
        v___y_1413_,
        v___y_1414_,
        v___y_1415_,
    );
    crate::leanh::lean_dec(v___y_1414_);
    crate::leanh::lean_dec_ref(v___y_1412_);
    crate::leanh::lean_dec(v___x_1410_);
    return v_res_1416_;
}
pub unsafe fn l_Lean_registerSimplePersistentEnvExtension___redArg(
    mut v_descr_1421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addEntryFn_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addImportedFn_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toArrayFn_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exportEntriesFnEx_x3f_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_replay_x3f_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1450_: u8 = 0;
    let mut v___f_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_1423_ = crate::leanh::lean_ctor_get(v_descr_1421_, 0);
                crate::leanh::lean_inc(v_name_1423_);
                v_addEntryFn_1424_ = crate::leanh::lean_ctor_get(v_descr_1421_, 1);
                crate::leanh::lean_inc(v_addEntryFn_1424_);
                v_addImportedFn_1425_ = crate::leanh::lean_ctor_get(v_descr_1421_, 2);
                crate::leanh::lean_inc_n(v_addImportedFn_1425_, 2);
                v_toArrayFn_1426_ = crate::leanh::lean_ctor_get(v_descr_1421_, 3);
                crate::leanh::lean_inc_ref(v_toArrayFn_1426_);
                v_exportEntriesFnEx_x3f_1427_ = crate::leanh::lean_ctor_get(v_descr_1421_, 4);
                crate::leanh::lean_inc(v_exportEntriesFnEx_x3f_1427_);
                v_asyncMode_1428_ = crate::leanh::lean_ctor_get(v_descr_1421_, 5);
                crate::leanh::lean_inc(v_asyncMode_1428_);
                v_replay_x3f_1429_ = crate::leanh::lean_ctor_get(v_descr_1421_, 6);
                crate::leanh::lean_inc(v_replay_x3f_1429_);
                crate::leanh::lean_dec_ref(v_descr_1421_);
                v___f_1430_ = crate::leanh::lean_alloc_closure(
                    l_Lean_registerSimplePersistentEnvExtension___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1430_, 0, v_addEntryFn_1424_);
                v___f_1431_ = crate::leanh::lean_alloc_closure(
                    l_Lean_registerSimplePersistentEnvExtension___redArg___lam__1
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1431_, 0, v_exportEntriesFnEx_x3f_1427_);
                crate::leanh::lean_closure_set(v___f_1431_, 1, v_toArrayFn_1426_);
                v___f_1432_ = l_Lean_registerSimplePersistentEnvExtension___redArg___closed__0;
                v___f_1433_ = l_Lean_registerSimplePersistentEnvExtension___redArg___closed__1;
                v___x_1434_ = crate::leanh::lean_box(0);
                v___f_1435_ = crate::leanh::lean_alloc_closure(
                    l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4___boxed
                        as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1435_, 0, v_addImportedFn_1425_);
                crate::leanh::lean_closure_set(v___f_1435_, 1, v___x_1434_);
                v___x_1436_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1437_ = l_Lean_registerSimplePersistentEnvExtension___redArg___closed__2;
                v___x_1438_ = crate::leanh::lean_apply_1(v_addImportedFn_1425_, v___x_1437_);
                v___x_1439_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1439_, 0, v___x_1434_);
                crate::leanh::lean_ctor_set(v___x_1439_, 1, v___x_1438_);
                v___x_1440_ = crate::leanh::lean_alloc_closure(
                    l_instMonadEIO___aux__5___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_1440_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_1440_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_1440_, 2, v___x_1439_);
                if crate::leanh::lean_obj_tag(v_replay_x3f_1429_) == 0 {
                    v___x_1446_ = crate::leanh::lean_box(0);
                    v___y_1442_ = v___x_1446_;
                    state = 1;
                    continue;
                } else {
                    v_val_1447_ = crate::leanh::lean_ctor_get(v_replay_x3f_1429_, 0);
                    v_isSharedCheck_1455_ =
                        (!crate::leanh::lean_is_exclusive(v_replay_x3f_1429_)) as u8;
                    if v_isSharedCheck_1455_ == 0 {
                        v___x_1449_ = v_replay_x3f_1429_;
                        v_isShared_1450_ = v_isSharedCheck_1455_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1447_);
                        crate::leanh::lean_dec(v_replay_x3f_1429_);
                        v___x_1449_ = crate::leanh::lean_box(0);
                        v_isShared_1450_ = v_isSharedCheck_1455_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1443_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1443_, 0, v_name_1423_);
                crate::leanh::lean_ctor_set(v___x_1443_, 1, v___x_1440_);
                crate::leanh::lean_ctor_set(v___x_1443_, 2, v___f_1435_);
                crate::leanh::lean_ctor_set(v___x_1443_, 3, v___f_1430_);
                crate::leanh::lean_ctor_set(v___x_1443_, 4, v___f_1431_);
                crate::leanh::lean_ctor_set(v___x_1443_, 5, v___f_1432_);
                crate::leanh::lean_ctor_set(v___x_1443_, 6, v_asyncMode_1428_);
                crate::leanh::lean_ctor_set(v___x_1443_, 7, v___y_1442_);
                v___x_1444_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1444_, 0, v___x_1443_);
                crate::leanh::lean_ctor_set(v___x_1444_, 1, v___f_1433_);
                v___x_1445_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1444_);
                return v___x_1445_;
            }
            2 => {
                v___f_1451_ = crate::leanh::lean_alloc_closure(
                    l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5___boxed
                        as *mut core::ffi::c_void,
                    6,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1451_, 0, v___x_1436_);
                crate::leanh::lean_closure_set(v___f_1451_, 1, v_val_1447_);
                if v_isShared_1450_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1449_, 0, v___f_1451_);
                    v___x_1453_ = v___x_1449_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1454_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___f_1451_);
                    v___x_1453_ = v_reuseFailAlloc_1454_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_1442_ = v___x_1453_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_registerSimplePersistentEnvExtension___redArg___boxed(
    mut v_descr_1456_: *mut crate::leanh::LeanObject,
    mut v_a_1457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1458_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v_descr_1456_);
    return v_res_1458_;
}
pub unsafe fn l_Lean_registerSimplePersistentEnvExtension(
    mut v_00_u03b1_1459_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1460_: *mut crate::leanh::LeanObject,
    mut v_inst_1461_: *mut crate::leanh::LeanObject,
    mut v_descr_1462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1464_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v_descr_1462_);
    return v___x_1464_;
}
pub unsafe fn l_Lean_registerSimplePersistentEnvExtension___boxed(
    mut v_00_u03b1_1465_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1466_: *mut crate::leanh::LeanObject,
    mut v_inst_1467_: *mut crate::leanh::LeanObject,
    mut v_descr_1468_: *mut crate::leanh::LeanObject,
    mut v_a_1469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1470_ = l_Lean_registerSimplePersistentEnvExtension(
        v_00_u03b1_1465_,
        v_00_u03c3_1466_,
        v_inst_1467_,
        v_descr_1468_,
    );
    crate::leanh::lean_dec(v_inst_1467_);
    return v_res_1470_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0(
    mut v_x_1474_: *mut crate::leanh::LeanObject,
    mut v___y_1475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1477_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__1;
    v___x_1478_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1478_, 0, v___x_1477_);
    return v___x_1478_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___boxed(
    mut v_x_1479_: *mut crate::leanh::LeanObject,
    mut v___y_1480_: *mut crate::leanh::LeanObject,
    mut v___y_1481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1482_ =
        l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0(v_x_1479_, v___y_1480_);
    crate::leanh::lean_dec_ref(v___y_1480_);
    crate::leanh::lean_dec_ref(v_x_1479_);
    return v_res_1482_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__1(
    mut v_s_1483_: *mut crate::leanh::LeanObject,
    mut v_x_1484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_s_1483_);
    return v_s_1483_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__1___boxed(
    mut v_s_1485_: *mut crate::leanh::LeanObject,
    mut v_x_1486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1487_ =
        l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__1(v_s_1485_, v_x_1486_);
    crate::leanh::lean_dec(v_x_1486_);
    crate::leanh::lean_dec_ref(v_s_1485_);
    return v_res_1487_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2(
    mut v_x_1490_: *mut crate::leanh::LeanObject,
    mut v_x_1491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1492_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2___closed__0;
    return v___x_1492_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2___boxed(
    mut v_x_1493_: *mut crate::leanh::LeanObject,
    mut v_x_1494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1495_ =
        l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2(v_x_1493_, v_x_1494_);
    crate::leanh::lean_dec_ref(v_x_1494_);
    crate::leanh::lean_dec_ref(v_x_1493_);
    return v_res_1495_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__3(
    mut v_x_1496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = crate::leanh::lean_box(0);
    return v___x_1497_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__3___boxed(
    mut v_x_1498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1499_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__3(v_x_1498_);
    crate::leanh::lean_dec_ref(v_x_1498_);
    return v_res_1499_;
}
pub unsafe fn _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1504_ = l_Lean_instInhabitedEnvExtension_default(crate::leanh::lean_box(0));
    return v___x_1504_;
}
pub unsafe fn _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1505_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__3;
    v___f_1506_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__2;
    v___f_1507_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__1;
    v___f_1508_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__0;
    v___x_1509_ = crate::leanh::lean_box(0);
    v___x_1510_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__4_once
        ),
        _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__4,
    );
    v___x_1511_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1511_, 0, v___x_1510_);
    crate::leanh::lean_ctor_set(v___x_1511_, 1, v___x_1509_);
    crate::leanh::lean_ctor_set(v___x_1511_, 2, v___f_1508_);
    crate::leanh::lean_ctor_set(v___x_1511_, 3, v___f_1507_);
    crate::leanh::lean_ctor_set(v___x_1511_, 4, v___f_1506_);
    crate::leanh::lean_ctor_set(v___x_1511_, 5, v___f_1505_);
    return v___x_1511_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1(
    mut v_00_u03b1_1512_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1514_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5_once
        ),
        _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5,
    );
    return v___x_1514_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_instInhabited(
    mut v_00_u03b1_1515_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1516_: *mut crate::leanh::LeanObject,
    mut v_inst_1517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1518_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5_once
        ),
        _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5,
    );
    return v___x_1518_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_instInhabited___boxed(
    mut v_00_u03b1_1519_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1520_: *mut crate::leanh::LeanObject,
    mut v_inst_1521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1522_ = l_Lean_SimplePersistentEnvExtension_instInhabited(
        v_00_u03b1_1519_,
        v_00_u03c3_1520_,
        v_inst_1521_,
    );
    crate::leanh::lean_dec(v_inst_1521_);
    return v_res_1522_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_getEntries___redArg(
    mut v_inst_1523_: *mut crate::leanh::LeanObject,
    mut v_ext_1524_: *mut crate::leanh::LeanObject,
    mut v_env_1525_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_1526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1527_ = crate::leanh::lean_box(0);
    v___x_1528_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1528_, 0, v___x_1527_);
    crate::leanh::lean_ctor_set(v___x_1528_, 1, v_inst_1523_);
    v___x_1529_ = crate::leanh::lean_box(0);
    v___x_1530_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_1528_,
        v_ext_1524_,
        v_env_1525_,
        v_asyncMode_1526_,
        v___x_1529_,
    );
    v_fst_1531_ = crate::leanh::lean_ctor_get(v___x_1530_, 0);
    crate::leanh::lean_inc(v_fst_1531_);
    crate::leanh::lean_dec(v___x_1530_);
    return v_fst_1531_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_getEntries___redArg___boxed(
    mut v_inst_1532_: *mut crate::leanh::LeanObject,
    mut v_ext_1533_: *mut crate::leanh::LeanObject,
    mut v_env_1534_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_1535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1536_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(
        v_inst_1532_,
        v_ext_1533_,
        v_env_1534_,
        v_asyncMode_1535_,
    );
    crate::leanh::lean_dec(v_asyncMode_1535_);
    crate::leanh::lean_dec_ref(v_ext_1533_);
    return v_res_1536_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_getEntries(
    mut v_00_u03b1_1537_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1538_: *mut crate::leanh::LeanObject,
    mut v_inst_1539_: *mut crate::leanh::LeanObject,
    mut v_ext_1540_: *mut crate::leanh::LeanObject,
    mut v_env_1541_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_1542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1543_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(
        v_inst_1539_,
        v_ext_1540_,
        v_env_1541_,
        v_asyncMode_1542_,
    );
    return v___x_1543_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_getEntries___boxed(
    mut v_00_u03b1_1544_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1545_: *mut crate::leanh::LeanObject,
    mut v_inst_1546_: *mut crate::leanh::LeanObject,
    mut v_ext_1547_: *mut crate::leanh::LeanObject,
    mut v_env_1548_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_1549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1550_ = l_Lean_SimplePersistentEnvExtension_getEntries(
        v_00_u03b1_1544_,
        v_00_u03c3_1545_,
        v_inst_1546_,
        v_ext_1547_,
        v_env_1548_,
        v_asyncMode_1549_,
    );
    crate::leanh::lean_dec(v_asyncMode_1549_);
    crate::leanh::lean_dec_ref(v_ext_1547_);
    return v_res_1550_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_getState___redArg(
    mut v_inst_1551_: *mut crate::leanh::LeanObject,
    mut v_ext_1552_: *mut crate::leanh::LeanObject,
    mut v_env_1553_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_1554_: *mut crate::leanh::LeanObject,
    mut v_asyncDecl_1555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1556_ = crate::leanh::lean_box(0);
    v___x_1557_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1557_, 0, v___x_1556_);
    crate::leanh::lean_ctor_set(v___x_1557_, 1, v_inst_1551_);
    v___x_1558_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_1557_,
        v_ext_1552_,
        v_env_1553_,
        v_asyncMode_1554_,
        v_asyncDecl_1555_,
    );
    v_snd_1559_ = crate::leanh::lean_ctor_get(v___x_1558_, 1);
    crate::leanh::lean_inc(v_snd_1559_);
    crate::leanh::lean_dec(v___x_1558_);
    return v_snd_1559_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_getState___redArg___boxed(
    mut v_inst_1560_: *mut crate::leanh::LeanObject,
    mut v_ext_1561_: *mut crate::leanh::LeanObject,
    mut v_env_1562_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_1563_: *mut crate::leanh::LeanObject,
    mut v_asyncDecl_1564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1565_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v_inst_1560_,
        v_ext_1561_,
        v_env_1562_,
        v_asyncMode_1563_,
        v_asyncDecl_1564_,
    );
    crate::leanh::lean_dec(v_asyncMode_1563_);
    crate::leanh::lean_dec_ref(v_ext_1561_);
    return v_res_1565_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_getState(
    mut v_00_u03b1_1566_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1567_: *mut crate::leanh::LeanObject,
    mut v_inst_1568_: *mut crate::leanh::LeanObject,
    mut v_ext_1569_: *mut crate::leanh::LeanObject,
    mut v_env_1570_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_1571_: *mut crate::leanh::LeanObject,
    mut v_asyncDecl_1572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1573_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v_inst_1568_,
        v_ext_1569_,
        v_env_1570_,
        v_asyncMode_1571_,
        v_asyncDecl_1572_,
    );
    return v___x_1573_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_getState___boxed(
    mut v_00_u03b1_1574_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1575_: *mut crate::leanh::LeanObject,
    mut v_inst_1576_: *mut crate::leanh::LeanObject,
    mut v_ext_1577_: *mut crate::leanh::LeanObject,
    mut v_env_1578_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_1579_: *mut crate::leanh::LeanObject,
    mut v_asyncDecl_1580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1581_ = l_Lean_SimplePersistentEnvExtension_getState(
        v_00_u03b1_1574_,
        v_00_u03c3_1575_,
        v_inst_1576_,
        v_ext_1577_,
        v_env_1578_,
        v_asyncMode_1579_,
        v_asyncDecl_1580_,
    );
    crate::leanh::lean_dec(v_asyncMode_1579_);
    crate::leanh::lean_dec_ref(v_ext_1577_);
    return v_res_1581_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_setState___redArg___lam__0(
    mut v_s_1582_: *mut crate::leanh::LeanObject,
    mut v_x_1583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1587_: u8 = 0;
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1591_: u8 = 0;
    let mut v_unused_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1584_ = crate::leanh::lean_ctor_get(v_x_1583_, 0);
                v_isSharedCheck_1591_ = (!crate::leanh::lean_is_exclusive(v_x_1583_)) as u8;
                if v_isSharedCheck_1591_ == 0 {
                    v_unused_1592_ = crate::leanh::lean_ctor_get(v_x_1583_, 1);
                    crate::leanh::lean_dec(v_unused_1592_);
                    v___x_1586_ = v_x_1583_;
                    v_isShared_1587_ = v_isSharedCheck_1591_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_1584_);
                    crate::leanh::lean_dec(v_x_1583_);
                    v___x_1586_ = crate::leanh::lean_box(0);
                    v_isShared_1587_ = v_isSharedCheck_1591_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1587_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1586_, 1, v_s_1582_);
                    v___x_1589_ = v___x_1586_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1590_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_fst_1584_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_s_1582_);
                    v___x_1589_ = v_reuseFailAlloc_1590_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_setState___redArg(
    mut v_ext_1593_: *mut crate::leanh::LeanObject,
    mut v_env_1594_: *mut crate::leanh::LeanObject,
    mut v_s_1595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toEnvExtension_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toEnvExtension_1596_ = crate::leanh::lean_ctor_get(v_ext_1593_, 0);
    v_asyncMode_1597_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1596_, 2);
    crate::leanh::lean_inc(v_asyncMode_1597_);
    v___f_1598_ = crate::leanh::lean_alloc_closure(
        l_Lean_SimplePersistentEnvExtension_setState___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1598_, 0, v_s_1595_);
    v___x_1599_ = crate::leanh::lean_box(0);
    v___x_1600_ = l_Lean_PersistentEnvExtension_modifyState___redArg(
        v_ext_1593_,
        v_env_1594_,
        v___f_1598_,
        v_asyncMode_1597_,
        v___x_1599_,
    );
    crate::leanh::lean_dec(v_asyncMode_1597_);
    return v___x_1600_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_setState(
    mut v_00_u03b1_1601_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1602_: *mut crate::leanh::LeanObject,
    mut v_ext_1603_: *mut crate::leanh::LeanObject,
    mut v_env_1604_: *mut crate::leanh::LeanObject,
    mut v_s_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ =
        l_Lean_SimplePersistentEnvExtension_setState___redArg(v_ext_1603_, v_env_1604_, v_s_1605_);
    return v___x_1606_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_modifyState___redArg___lam__0(
    mut v_f_1607_: *mut crate::leanh::LeanObject,
    mut v_x_1608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1613_: u8 = 0;
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1609_ = crate::leanh::lean_ctor_get(v_x_1608_, 0);
                v_snd_1610_ = crate::leanh::lean_ctor_get(v_x_1608_, 1);
                v_isSharedCheck_1618_ = (!crate::leanh::lean_is_exclusive(v_x_1608_)) as u8;
                if v_isSharedCheck_1618_ == 0 {
                    v___x_1612_ = v_x_1608_;
                    v_isShared_1613_ = v_isSharedCheck_1618_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1610_);
                    crate::leanh::lean_inc(v_fst_1609_);
                    crate::leanh::lean_dec(v_x_1608_);
                    v___x_1612_ = crate::leanh::lean_box(0);
                    v_isShared_1613_ = v_isSharedCheck_1618_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1614_ = crate::leanh::lean_apply_1(v_f_1607_, v_snd_1610_);
                if v_isShared_1613_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1612_, 1, v___x_1614_);
                    v___x_1616_ = v___x_1612_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1617_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_fst_1609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1617_, 1, v___x_1614_);
                    v___x_1616_ = v_reuseFailAlloc_1617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_modifyState___redArg(
    mut v_ext_1619_: *mut crate::leanh::LeanObject,
    mut v_env_1620_: *mut crate::leanh::LeanObject,
    mut v_f_1621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toEnvExtension_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toEnvExtension_1622_ = crate::leanh::lean_ctor_get(v_ext_1619_, 0);
    v_asyncMode_1623_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1622_, 2);
    crate::leanh::lean_inc(v_asyncMode_1623_);
    v___f_1624_ = crate::leanh::lean_alloc_closure(
        l_Lean_SimplePersistentEnvExtension_modifyState___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1624_, 0, v_f_1621_);
    v___x_1625_ = crate::leanh::lean_box(0);
    v___x_1626_ = l_Lean_PersistentEnvExtension_modifyState___redArg(
        v_ext_1619_,
        v_env_1620_,
        v___f_1624_,
        v_asyncMode_1623_,
        v___x_1625_,
    );
    crate::leanh::lean_dec(v_asyncMode_1623_);
    return v___x_1626_;
}
pub unsafe fn l_Lean_SimplePersistentEnvExtension_modifyState(
    mut v_00_u03b1_1627_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1628_: *mut crate::leanh::LeanObject,
    mut v_ext_1629_: *mut crate::leanh::LeanObject,
    mut v_env_1630_: *mut crate::leanh::LeanObject,
    mut v_f_1631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1632_ = l_Lean_SimplePersistentEnvExtension_modifyState___redArg(
        v_ext_1629_,
        v_env_1630_,
        v_f_1631_,
    );
    return v___x_1632_;
}
pub unsafe fn _init_l_Lean_mkTagDeclarationExtension___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1633_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once
        ),
        _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28,
    );
    return v___x_1633_;
}
pub unsafe fn l_Lean_mkTagDeclarationExtension___lam__0(
    mut v_x_1634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1635_ = l_Lean_NameSet_empty;
    return v___x_1635_;
}
pub unsafe fn l_Lean_mkTagDeclarationExtension___lam__0___boxed(
    mut v_x_1636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1637_ = l_Lean_mkTagDeclarationExtension___lam__0(v_x_1636_);
    crate::leanh::lean_dec_ref(v_x_1636_);
    return v_res_1637_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(
    mut v_hi_1638_: *mut crate::leanh::LeanObject,
    mut v_pivot_1639_: *mut crate::leanh::LeanObject,
    mut v_as_1640_: *mut crate::leanh::LeanObject,
    mut v_i_1641_: *mut crate::leanh::LeanObject,
    mut v_k_1642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1643_: u8 = 0;
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: u8 = 0;
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1643_ = lean_nat_dec_lt(v_k_1642_, v_hi_1638_);
                if v___x_1643_ == 0 {
                    crate::leanh::lean_dec(v_k_1642_);
                    v___x_1644_ = lean_array_fswap(v_as_1640_, v_i_1641_, v_hi_1638_);
                    v___x_1645_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1645_, 0, v_i_1641_);
                    crate::leanh::lean_ctor_set(v___x_1645_, 1, v___x_1644_);
                    return v___x_1645_;
                } else {
                    v___x_1646_ = lean_array_fget_borrowed(v_as_1640_, v_k_1642_);
                    v___x_1647_ = l_Lean_Name_quickLt(v___x_1646_, v_pivot_1639_);
                    if v___x_1647_ == 0 {
                        v___x_1648_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1649_ = lean_nat_add(v_k_1642_, v___x_1648_);
                        crate::leanh::lean_dec(v_k_1642_);
                        v_k_1642_ = v___x_1649_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1651_ = lean_array_fswap(v_as_1640_, v_i_1641_, v_k_1642_);
                        v___x_1652_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1653_ = lean_nat_add(v_i_1641_, v___x_1652_);
                        crate::leanh::lean_dec(v_i_1641_);
                        v___x_1654_ = lean_nat_add(v_k_1642_, v___x_1652_);
                        crate::leanh::lean_dec(v_k_1642_);
                        v_as_1640_ = v___x_1651_;
                        v_i_1641_ = v___x_1653_;
                        v_k_1642_ = v___x_1654_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg___boxed(
    mut v_hi_1656_: *mut crate::leanh::LeanObject,
    mut v_pivot_1657_: *mut crate::leanh::LeanObject,
    mut v_as_1658_: *mut crate::leanh::LeanObject,
    mut v_i_1659_: *mut crate::leanh::LeanObject,
    mut v_k_1660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1661_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_1656_, v_pivot_1657_, v_as_1658_, v_i_1659_, v_k_1660_);
    crate::leanh::lean_dec(v_pivot_1657_);
    crate::leanh::lean_dec(v_hi_1656_);
    return v_res_1661_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(
    mut v_n_1662_: *mut crate::leanh::LeanObject,
    mut v_as_1663_: *mut crate::leanh::LeanObject,
    mut v_lo_1664_: *mut crate::leanh::LeanObject,
    mut v_hi_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: u8 = 0;
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: u8 = 0;
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: u8 = 0;
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: u8 = 0;
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: u8 = 0;
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1677_ = lean_nat_dec_lt(v_lo_1664_, v_hi_1665_);
                if v___x_1677_ == 0 {
                    crate::leanh::lean_dec(v_lo_1664_);
                    return v_as_1663_;
                } else {
                    v___x_1678_ = lean_nat_add(v_lo_1664_, v_hi_1665_);
                    v___x_1679_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_1680_ = lean_nat_shiftr(v___x_1678_, v___x_1679_);
                    crate::leanh::lean_dec(v___x_1678_);
                    v___x_1693_ = lean_array_fget_borrowed(v_as_1663_, v_mid_1680_);
                    v___x_1694_ = lean_array_fget_borrowed(v_as_1663_, v_lo_1664_);
                    v___x_1695_ = l_Lean_Name_quickLt(v___x_1693_, v___x_1694_);
                    if v___x_1695_ == 0 {
                        v___y_1688_ = v_as_1663_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1696_ = lean_array_fswap(v_as_1663_, v_lo_1664_, v_mid_1680_);
                        v___y_1688_ = v___x_1696_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_1668_ = lean_array_fget(v___y_1667_, v_hi_1665_);
                crate::leanh::lean_inc_n(v_lo_1664_, 2);
                v___x_1669_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_1665_, v_pivot_1668_, v___y_1667_, v_lo_1664_, v_lo_1664_);
                crate::leanh::lean_dec(v_pivot_1668_);
                v_fst_1670_ = crate::leanh::lean_ctor_get(v___x_1669_, 0);
                crate::leanh::lean_inc(v_fst_1670_);
                v_snd_1671_ = crate::leanh::lean_ctor_get(v___x_1669_, 1);
                crate::leanh::lean_inc(v_snd_1671_);
                crate::leanh::lean_dec_ref(v___x_1669_);
                v___x_1672_ = lean_nat_dec_le(v_hi_1665_, v_fst_1670_);
                if v___x_1672_ == 0 {
                    v___x_1673_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_1662_, v_snd_1671_, v_lo_1664_, v_fst_1670_);
                    v___x_1674_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1675_ = lean_nat_add(v_fst_1670_, v___x_1674_);
                    crate::leanh::lean_dec(v_fst_1670_);
                    v_as_1663_ = v___x_1673_;
                    v_lo_1664_ = v___x_1675_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_1670_);
                    crate::leanh::lean_dec(v_lo_1664_);
                    return v_snd_1671_;
                }
            }
            2 => {
                v___x_1683_ = lean_array_fget_borrowed(v___y_1682_, v_mid_1680_);
                v___x_1684_ = lean_array_fget_borrowed(v___y_1682_, v_hi_1665_);
                v___x_1685_ = l_Lean_Name_quickLt(v___x_1683_, v___x_1684_);
                if v___x_1685_ == 0 {
                    crate::leanh::lean_dec(v_mid_1680_);
                    v___y_1667_ = v___y_1682_;
                    state = 1;
                    continue;
                } else {
                    v___x_1686_ = lean_array_fswap(v___y_1682_, v_mid_1680_, v_hi_1665_);
                    crate::leanh::lean_dec(v_mid_1680_);
                    v___y_1667_ = v___x_1686_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1689_ = lean_array_fget_borrowed(v___y_1688_, v_hi_1665_);
                v___x_1690_ = lean_array_fget_borrowed(v___y_1688_, v_lo_1664_);
                v___x_1691_ = l_Lean_Name_quickLt(v___x_1689_, v___x_1690_);
                if v___x_1691_ == 0 {
                    v___y_1682_ = v___y_1688_;
                    state = 2;
                    continue;
                } else {
                    v___x_1692_ = lean_array_fswap(v___y_1688_, v_lo_1664_, v_hi_1665_);
                    v___y_1682_ = v___x_1692_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg___boxed(
    mut v_n_1697_: *mut crate::leanh::LeanObject,
    mut v_as_1698_: *mut crate::leanh::LeanObject,
    mut v_lo_1699_: *mut crate::leanh::LeanObject,
    mut v_hi_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1701_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_1697_, v_as_1698_, v_lo_1699_, v_hi_1700_);
    crate::leanh::lean_dec(v_hi_1700_);
    crate::leanh::lean_dec(v_n_1697_);
    return v_res_1701_;
}
pub unsafe fn l_Lean_mkTagDeclarationExtension___lam__1(
    mut v_es_1702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: u8 = 0;
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: u8 = 0;
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1703_ = lean_array_mk(v_es_1702_);
                v___x_1704_ = lean_array_get_size(v___x_1703_);
                v___x_1705_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1706_ = lean_nat_dec_eq(v___x_1704_, v___x_1705_);
                if v___x_1706_ == 0 {
                    v___x_1707_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1708_ = lean_nat_sub(v___x_1704_, v___x_1707_);
                    v___x_1714_ = lean_nat_dec_le(v___x_1705_, v___x_1708_);
                    if v___x_1714_ == 0 {
                        crate::leanh::lean_inc(v___x_1708_);
                        v___y_1710_ = v___x_1708_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1710_ = v___x_1705_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1703_;
                }
            }
            1 => {
                v___x_1711_ = lean_nat_dec_le(v___y_1710_, v___x_1708_);
                if v___x_1711_ == 0 {
                    crate::leanh::lean_dec(v___x_1708_);
                    crate::leanh::lean_inc(v___y_1710_);
                    v___x_1712_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v___x_1704_, v___x_1703_, v___y_1710_, v___y_1710_);
                    crate::leanh::lean_dec(v___y_1710_);
                    return v___x_1712_;
                } else {
                    v___x_1713_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v___x_1704_, v___x_1703_, v___y_1710_, v___x_1708_);
                    crate::leanh::lean_dec(v___x_1708_);
                    return v___x_1713_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkTagDeclarationExtension___lam__2(
    mut v_x1_1715_: *mut crate::leanh::LeanObject,
    mut v_x2_1716_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1717_: u8 = 0;
    v___x_1717_ = l_Lean_NameSet_contains(v_x1_1715_, v_x2_1716_);
    if v___x_1717_ == 0 {
        let mut v___x_1718_: u8 = 0;
        v___x_1718_ = 1;
        return v___x_1718_;
    } else {
        let mut v___x_1719_: u8 = 0;
        v___x_1719_ = 0;
        return v___x_1719_;
    }
}
pub unsafe fn l_Lean_mkTagDeclarationExtension___lam__2___boxed(
    mut v_x1_1720_: *mut crate::leanh::LeanObject,
    mut v_x2_1721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1722_: u8 = 0;
    let mut v_r_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1722_ = l_Lean_mkTagDeclarationExtension___lam__2(v_x1_1720_, v_x2_1721_);
    crate::leanh::lean_dec(v_x2_1721_);
    crate::leanh::lean_dec(v_x1_1720_);
    v_r_1723_ = crate::leanh::lean_box((v_res_1722_) as usize);
    return v_r_1723_;
}
pub unsafe fn l_Lean_mkTagDeclarationExtension(
    mut v_name_1733_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_1734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1736_ = l_Lean_mkTagDeclarationExtension___closed__0;
    v___f_1737_ = l_Lean_mkTagDeclarationExtension___closed__1;
    v___f_1738_ = l_Lean_mkTagDeclarationExtension___closed__2;
    v___x_1739_ = crate::leanh::lean_box(0);
    v___x_1740_ = l_Lean_mkTagDeclarationExtension___closed__5;
    v___x_1741_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1741_, 0, v_name_1733_);
    crate::leanh::lean_ctor_set(v___x_1741_, 1, v___f_1736_);
    crate::leanh::lean_ctor_set(v___x_1741_, 2, v___f_1737_);
    crate::leanh::lean_ctor_set(v___x_1741_, 3, v___f_1738_);
    crate::leanh::lean_ctor_set(v___x_1741_, 4, v___x_1739_);
    crate::leanh::lean_ctor_set(v___x_1741_, 5, v_asyncMode_1734_);
    crate::leanh::lean_ctor_set(v___x_1741_, 6, v___x_1740_);
    v___x_1742_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1741_);
    return v___x_1742_;
}
pub unsafe fn l_Lean_mkTagDeclarationExtension___boxed(
    mut v_name_1743_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_1744_: *mut crate::leanh::LeanObject,
    mut v_a_1745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1746_ = l_Lean_mkTagDeclarationExtension(v_name_1743_, v_asyncMode_1744_);
    return v_res_1746_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0(
    mut v_n_1747_: *mut crate::leanh::LeanObject,
    mut v_as_1748_: *mut crate::leanh::LeanObject,
    mut v_lo_1749_: *mut crate::leanh::LeanObject,
    mut v_hi_1750_: *mut crate::leanh::LeanObject,
    mut v_w_1751_: *mut crate::leanh::LeanObject,
    mut v_hlo_1752_: *mut crate::leanh::LeanObject,
    mut v_hhi_1753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1754_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_1747_, v_as_1748_, v_lo_1749_, v_hi_1750_);
    return v___x_1754_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___boxed(
    mut v_n_1755_: *mut crate::leanh::LeanObject,
    mut v_as_1756_: *mut crate::leanh::LeanObject,
    mut v_lo_1757_: *mut crate::leanh::LeanObject,
    mut v_hi_1758_: *mut crate::leanh::LeanObject,
    mut v_w_1759_: *mut crate::leanh::LeanObject,
    mut v_hlo_1760_: *mut crate::leanh::LeanObject,
    mut v_hhi_1761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1762_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0(v_n_1755_, v_as_1756_, v_lo_1757_, v_hi_1758_, v_w_1759_, v_hlo_1760_, v_hhi_1761_);
    crate::leanh::lean_dec(v_hi_1758_);
    crate::leanh::lean_dec(v_n_1755_);
    return v_res_1762_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0(
    mut v_n_1763_: *mut crate::leanh::LeanObject,
    mut v_lo_1764_: *mut crate::leanh::LeanObject,
    mut v_hi_1765_: *mut crate::leanh::LeanObject,
    mut v_hhi_1766_: *mut crate::leanh::LeanObject,
    mut v_pivot_1767_: *mut crate::leanh::LeanObject,
    mut v_as_1768_: *mut crate::leanh::LeanObject,
    mut v_i_1769_: *mut crate::leanh::LeanObject,
    mut v_k_1770_: *mut crate::leanh::LeanObject,
    mut v_ilo_1771_: *mut crate::leanh::LeanObject,
    mut v_ik_1772_: *mut crate::leanh::LeanObject,
    mut v_w_1773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_1765_, v_pivot_1767_, v_as_1768_, v_i_1769_, v_k_1770_);
    return v___x_1774_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___boxed(
    mut v_n_1775_: *mut crate::leanh::LeanObject,
    mut v_lo_1776_: *mut crate::leanh::LeanObject,
    mut v_hi_1777_: *mut crate::leanh::LeanObject,
    mut v_hhi_1778_: *mut crate::leanh::LeanObject,
    mut v_pivot_1779_: *mut crate::leanh::LeanObject,
    mut v_as_1780_: *mut crate::leanh::LeanObject,
    mut v_i_1781_: *mut crate::leanh::LeanObject,
    mut v_k_1782_: *mut crate::leanh::LeanObject,
    mut v_ilo_1783_: *mut crate::leanh::LeanObject,
    mut v_ik_1784_: *mut crate::leanh::LeanObject,
    mut v_w_1785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1786_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0(v_n_1775_, v_lo_1776_, v_hi_1777_, v_hhi_1778_, v_pivot_1779_, v_as_1780_, v_i_1781_, v_k_1782_, v_ilo_1783_, v_ik_1784_, v_w_1785_);
    crate::leanh::lean_dec(v_pivot_1779_);
    crate::leanh::lean_dec(v_hi_1777_);
    crate::leanh::lean_dec(v_lo_1776_);
    crate::leanh::lean_dec(v_n_1775_);
    return v_res_1786_;
}
pub unsafe fn l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(
    mut v_x_1787_: *mut crate::leanh::LeanObject,
    mut v___y_1788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1790_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__1;
    v___x_1791_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1791_, 0, v___x_1790_);
    return v___x_1791_;
}
pub unsafe fn l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0___boxed(
    mut v_x_1792_: *mut crate::leanh::LeanObject,
    mut v___y_1793_: *mut crate::leanh::LeanObject,
    mut v___y_1794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1795_ =
        l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(v_x_1792_, v___y_1793_);
    crate::leanh::lean_dec_ref(v___y_1793_);
    crate::leanh::lean_dec_ref(v_x_1792_);
    return v_res_1795_;
}
pub unsafe fn l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1(
    mut v_s_1796_: *mut crate::leanh::LeanObject,
    mut v_x_1797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_s_1796_);
    return v_s_1796_;
}
pub unsafe fn l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1___boxed(
    mut v_s_1798_: *mut crate::leanh::LeanObject,
    mut v_x_1799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1800_ =
        l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1(v_s_1798_, v_x_1799_);
    crate::leanh::lean_dec(v_x_1799_);
    crate::leanh::lean_dec_ref(v_s_1798_);
    return v_res_1800_;
}
pub unsafe fn l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2(
    mut v_x_1805_: *mut crate::leanh::LeanObject,
    mut v_x_1806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1807_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__1;
    return v___x_1807_;
}
pub unsafe fn l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___boxed(
    mut v_x_1808_: *mut crate::leanh::LeanObject,
    mut v_x_1809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1810_ =
        l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2(v_x_1808_, v_x_1809_);
    crate::leanh::lean_dec_ref(v_x_1809_);
    crate::leanh::lean_dec_ref(v_x_1808_);
    return v_res_1810_;
}
pub unsafe fn l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3(
    mut v_x_1811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1812_ = crate::leanh::lean_box(0);
    return v___x_1812_;
}
pub unsafe fn l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3___boxed(
    mut v_x_1813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1814_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3(v_x_1813_);
    crate::leanh::lean_dec_ref(v_x_1813_);
    return v_res_1814_;
}
pub unsafe fn _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1819_ = l_Lean_instInhabitedEnvExtension_default(crate::leanh::lean_box(0));
    return v___x_1819_;
}
pub unsafe fn _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1820_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__3;
    v___f_1821_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__2;
    v___f_1822_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__1;
    v___f_1823_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__0;
    v___x_1824_ = crate::leanh::lean_box(0);
    v___x_1825_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4_once
        ),
        _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4,
    );
    v___x_1826_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1826_, 0, v___x_1825_);
    crate::leanh::lean_ctor_set(v___x_1826_, 1, v___x_1824_);
    crate::leanh::lean_ctor_set(v___x_1826_, 2, v___f_1823_);
    crate::leanh::lean_ctor_set(v___x_1826_, 3, v___f_1822_);
    crate::leanh::lean_ctor_set(v___x_1826_, 4, v___f_1821_);
    crate::leanh::lean_ctor_set(v___x_1826_, 5, v___f_1820_);
    return v___x_1826_;
}
pub unsafe fn _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1827_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5_once
        ),
        _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5,
    );
    return v___x_1827_;
}
pub unsafe fn _init_l_Lean_TagDeclarationExtension_instInhabited() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1828_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5_once
        ),
        _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5,
    );
    return v___x_1828_;
}
pub unsafe fn l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0(
    mut v_env_1829_: *mut crate::leanh::LeanObject,
    mut v_msg_1830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1831_ = lean_panic_fn_borrowed(v_env_1829_, v_msg_1830_);
    return v___x_1831_;
}
pub unsafe fn l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0___boxed(
    mut v_env_1832_: *mut crate::leanh::LeanObject,
    mut v_msg_1833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1834_ =
        l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0(v_env_1832_, v_msg_1833_);
    crate::leanh::lean_dec_ref(v_env_1832_);
    return v_res_1834_;
}
pub unsafe fn _init_l_Lean_TagDeclarationExtension_tag___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1838_ = l_Lean_TagDeclarationExtension_tag___closed__2;
    v___x_1839_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_1840_ = crate::leanh::lean_unsigned_to_nat(115);
    v___x_1841_ = l_Lean_TagDeclarationExtension_tag___closed__1;
    v___x_1842_ = l_Lean_TagDeclarationExtension_tag___closed__0;
    v___x_1843_ = l_mkPanicMessageWithDecl(
        v___x_1842_,
        v___x_1841_,
        v___x_1840_,
        v___x_1839_,
        v___x_1838_,
    );
    return v___x_1843_;
}
pub unsafe fn l_Lean_TagDeclarationExtension_tag(
    mut v_ext_1844_: *mut crate::leanh::LeanObject,
    mut v_env_1845_: *mut crate::leanh::LeanObject,
    mut v_declName_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toEnvExtension_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: u8 = 0;
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1851_ = l_Lean_Name_isAnonymous(v_declName_1846_);
                if v___x_1851_ == 0 {
                    v___x_1852_ =
                        l_Lean_Environment_getModuleIdxFor_x3f(v_env_1845_, v_declName_1846_);
                    if crate::leanh::lean_obj_tag(v___x_1852_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_1852_, 1);
                        if v___x_1851_ == 0 {
                            crate::leanh::lean_dec(v_declName_1846_);
                            crate::leanh::lean_dec_ref(v_ext_1844_);
                            v___x_1853_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_TagDeclarationExtension_tag___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_TagDeclarationExtension_tag___closed__3_once
                                ),
                                _init_l_Lean_TagDeclarationExtension_tag___closed__3,
                            );
                            v___x_1854_ = lean_panic_fn_borrowed(v_env_1845_, v___x_1853_);
                            crate::leanh::lean_dec_ref(v_env_1845_);
                            return v___x_1854_;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_1846_);
                    crate::leanh::lean_dec_ref(v_ext_1844_);
                    return v_env_1845_;
                }
            }
            1 => {
                v_toEnvExtension_1848_ = crate::leanh::lean_ctor_get(v_ext_1844_, 0);
                v_asyncMode_1849_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1848_, 2);
                crate::leanh::lean_inc(v_asyncMode_1849_);
                crate::leanh::lean_inc(v_declName_1846_);
                v___x_1850_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v_ext_1844_,
                    v_env_1845_,
                    v_declName_1846_,
                    v_asyncMode_1849_,
                    v_declName_1846_,
                );
                crate::leanh::lean_dec(v_asyncMode_1849_);
                return v___x_1850_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(
    mut v_as_1855_: *mut crate::leanh::LeanObject,
    mut v_k_1856_: *mut crate::leanh::LeanObject,
    mut v_x_1857_: *mut crate::leanh::LeanObject,
    mut v_x_1858_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: u8 = 0;
    let mut v___x_1864_: u8 = 0;
    let mut v___x_1865_: u8 = 0;
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: u8 = 0;
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: u8 = 0;
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1859_ = lean_nat_add(v_x_1857_, v_x_1858_);
                v___x_1860_ = crate::leanh::lean_unsigned_to_nat(1);
                v_m_1861_ = lean_nat_shiftr(v___x_1859_, v___x_1860_);
                crate::leanh::lean_dec(v___x_1859_);
                v_a_1862_ = lean_array_fget_borrowed(v_as_1855_, v_m_1861_);
                v___x_1863_ = l_Lean_Name_quickLt(v_a_1862_, v_k_1856_);
                if v___x_1863_ == 0 {
                    crate::leanh::lean_dec(v_x_1858_);
                    v___x_1864_ = l_Lean_Name_quickLt(v_k_1856_, v_a_1862_);
                    if v___x_1864_ == 0 {
                        crate::leanh::lean_dec(v_m_1861_);
                        crate::leanh::lean_dec(v_x_1857_);
                        v___x_1865_ = 1;
                        return v___x_1865_;
                    } else {
                        v___x_1866_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1867_ = lean_nat_dec_eq(v_m_1861_, v___x_1866_);
                        if v___x_1867_ == 0 {
                            v___x_1868_ = lean_nat_sub(v_m_1861_, v___x_1860_);
                            crate::leanh::lean_dec(v_m_1861_);
                            v___x_1869_ = lean_nat_dec_lt(v___x_1868_, v_x_1857_);
                            if v___x_1869_ == 0 {
                                v_x_1858_ = v___x_1868_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1868_);
                                crate::leanh::lean_dec(v_x_1857_);
                                return v___x_1863_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_m_1861_);
                            crate::leanh::lean_dec(v_x_1857_);
                            return v___x_1863_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_x_1857_);
                    v___x_1871_ = lean_nat_add(v_m_1861_, v___x_1860_);
                    crate::leanh::lean_dec(v_m_1861_);
                    v___x_1872_ = lean_nat_dec_le(v___x_1871_, v_x_1858_);
                    if v___x_1872_ == 0 {
                        crate::leanh::lean_dec(v___x_1871_);
                        crate::leanh::lean_dec(v_x_1858_);
                        return v___x_1872_;
                    } else {
                        v_x_1857_ = v___x_1871_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg___boxed(
    mut v_as_1874_: *mut crate::leanh::LeanObject,
    mut v_k_1875_: *mut crate::leanh::LeanObject,
    mut v_x_1876_: *mut crate::leanh::LeanObject,
    mut v_x_1877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1878_: u8 = 0;
    let mut v_r_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1878_ =
        l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(
            v_as_1874_, v_k_1875_, v_x_1876_, v_x_1877_,
        );
    crate::leanh::lean_dec(v_k_1875_);
    crate::leanh::lean_dec_ref(v_as_1874_);
    v_r_1879_ = crate::leanh::lean_box((v_res_1878_) as usize);
    return v_r_1879_;
}
pub unsafe fn l_Lean_TagDeclarationExtension_isTagged(
    mut v_ext_1883_: *mut crate::leanh::LeanObject,
    mut v_env_1884_: *mut crate::leanh::LeanObject,
    mut v_declName_1885_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_1886_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1887_ = crate::leanh::lean_box(1);
    v___x_1888_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1884_, v_declName_1885_);
    if crate::leanh::lean_obj_tag(v___x_1888_) == 0 {
        let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1890_: u8 = 0;
        crate::leanh::lean_inc(v_declName_1885_);
        v___x_1889_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
            v___x_1887_,
            v_ext_1883_,
            v_env_1884_,
            v_asyncMode_1886_,
            v_declName_1885_,
        );
        v___x_1890_ = l_Lean_NameSet_contains(v___x_1889_, v_declName_1885_);
        crate::leanh::lean_dec(v_declName_1885_);
        crate::leanh::lean_dec(v___x_1889_);
        return v___x_1890_;
    } else {
        let mut v_val_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1893_: u8 = 0;
        let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1897_: u8 = 0;
        v_val_1891_ = crate::leanh::lean_ctor_get(v___x_1888_, 0);
        crate::leanh::lean_inc(v_val_1891_);
        crate::leanh::lean_dec_ref_known(v___x_1888_, 1);
        v___x_1892_ = l_Lean_TagDeclarationExtension_isTagged___closed__0;
        v___x_1893_ = 0;
        v___x_1894_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
            v___x_1892_,
            v_ext_1883_,
            v_env_1884_,
            v_val_1891_,
            v___x_1893_,
        );
        crate::leanh::lean_dec(v_val_1891_);
        crate::leanh::lean_dec_ref(v_env_1884_);
        v___x_1895_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1896_ = lean_array_get_size(v___x_1894_);
        v___x_1897_ = lean_nat_dec_lt(v___x_1895_, v___x_1896_);
        if v___x_1897_ == 0 {
            crate::leanh::lean_dec_ref(v___x_1894_);
            crate::leanh::lean_dec(v_declName_1885_);
            return v___x_1897_;
        } else {
            let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1900_: u8 = 0;
            v___x_1898_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1899_ = lean_nat_sub(v___x_1896_, v___x_1898_);
            v___x_1900_ = lean_nat_dec_le(v___x_1895_, v___x_1899_);
            if v___x_1900_ == 0 {
                crate::leanh::lean_dec(v___x_1899_);
                crate::leanh::lean_dec_ref(v___x_1894_);
                crate::leanh::lean_dec(v_declName_1885_);
                return v___x_1900_;
            } else {
                let mut v___x_1901_: u8 = 0;
                v___x_1901_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v___x_1894_, v_declName_1885_, v___x_1895_, v___x_1899_);
                crate::leanh::lean_dec(v_declName_1885_);
                crate::leanh::lean_dec_ref(v___x_1894_);
                return v___x_1901_;
            }
        }
    }
}
pub unsafe fn l_Lean_TagDeclarationExtension_isTagged___boxed(
    mut v_ext_1902_: *mut crate::leanh::LeanObject,
    mut v_env_1903_: *mut crate::leanh::LeanObject,
    mut v_declName_1904_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_1905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1906_: u8 = 0;
    let mut v_r_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1906_ = l_Lean_TagDeclarationExtension_isTagged(
        v_ext_1902_,
        v_env_1903_,
        v_declName_1904_,
        v_asyncMode_1905_,
    );
    crate::leanh::lean_dec(v_asyncMode_1905_);
    crate::leanh::lean_dec_ref(v_ext_1902_);
    v_r_1907_ = crate::leanh::lean_box((v_res_1906_) as usize);
    return v_r_1907_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0(
    mut v_as_1908_: *mut crate::leanh::LeanObject,
    mut v_k_1909_: *mut crate::leanh::LeanObject,
    mut v_x_1910_: *mut crate::leanh::LeanObject,
    mut v_x_1911_: *mut crate::leanh::LeanObject,
    mut v_x_1912_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1913_: u8 = 0;
    v___x_1913_ =
        l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(
            v_as_1908_, v_k_1909_, v_x_1910_, v_x_1911_,
        );
    return v___x_1913_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___boxed(
    mut v_as_1914_: *mut crate::leanh::LeanObject,
    mut v_k_1915_: *mut crate::leanh::LeanObject,
    mut v_x_1916_: *mut crate::leanh::LeanObject,
    mut v_x_1917_: *mut crate::leanh::LeanObject,
    mut v_x_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1919_: u8 = 0;
    let mut v_r_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1919_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0(
        v_as_1914_, v_k_1915_, v_x_1916_, v_x_1917_, v_x_1918_,
    );
    crate::leanh::lean_dec(v_k_1915_);
    crate::leanh::lean_dec_ref(v_as_1914_);
    v_r_1920_ = crate::leanh::lean_box((v_res_1919_) as usize);
    return v_r_1920_;
}
pub unsafe fn l_Lean_instInhabitedMapDeclarationExtension_default___lam__0(
    mut v_x_1921_: *mut crate::leanh::LeanObject,
    mut v___y_1922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1924_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__1;
    v___x_1925_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1925_, 0, v___x_1924_);
    return v___x_1925_;
}
pub unsafe fn l_Lean_instInhabitedMapDeclarationExtension_default___lam__0___boxed(
    mut v_x_1926_: *mut crate::leanh::LeanObject,
    mut v___y_1927_: *mut crate::leanh::LeanObject,
    mut v___y_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1929_ =
        l_Lean_instInhabitedMapDeclarationExtension_default___lam__0(v_x_1926_, v___y_1927_);
    crate::leanh::lean_dec_ref(v___y_1927_);
    crate::leanh::lean_dec_ref(v_x_1926_);
    return v_res_1929_;
}
pub unsafe fn l_Lean_instInhabitedMapDeclarationExtension_default___lam__1(
    mut v_s_1930_: *mut crate::leanh::LeanObject,
    mut v_x_1931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_s_1930_);
    return v_s_1930_;
}
pub unsafe fn l_Lean_instInhabitedMapDeclarationExtension_default___lam__1___boxed(
    mut v_s_1932_: *mut crate::leanh::LeanObject,
    mut v_x_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1934_ =
        l_Lean_instInhabitedMapDeclarationExtension_default___lam__1(v_s_1932_, v_x_1933_);
    crate::leanh::lean_dec_ref(v_x_1933_);
    crate::leanh::lean_dec(v_s_1932_);
    return v_res_1934_;
}
pub unsafe fn l_Lean_instInhabitedMapDeclarationExtension_default___lam__2(
    mut v_x_1939_: *mut crate::leanh::LeanObject,
    mut v_x_1940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1941_ = l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__1;
    return v___x_1941_;
}
pub unsafe fn l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___boxed(
    mut v_x_1942_: *mut crate::leanh::LeanObject,
    mut v_x_1943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1944_ =
        l_Lean_instInhabitedMapDeclarationExtension_default___lam__2(v_x_1942_, v_x_1943_);
    crate::leanh::lean_dec(v_x_1943_);
    crate::leanh::lean_dec_ref(v_x_1942_);
    return v_res_1944_;
}
pub unsafe fn l_Lean_instInhabitedMapDeclarationExtension_default___lam__3(
    mut v_x_1945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1946_ = crate::leanh::lean_box(0);
    return v___x_1946_;
}
pub unsafe fn l_Lean_instInhabitedMapDeclarationExtension_default___lam__3___boxed(
    mut v_x_1947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1948_ = l_Lean_instInhabitedMapDeclarationExtension_default___lam__3(v_x_1947_);
    crate::leanh::lean_dec(v_x_1947_);
    return v_res_1948_;
}
pub unsafe fn _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1953_ = l_Lean_instInhabitedEnvExtension_default(crate::leanh::lean_box(0));
    return v___x_1953_;
}
pub unsafe fn _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1954_ = l_Lean_instInhabitedMapDeclarationExtension_default___closed__3;
    v___f_1955_ = l_Lean_instInhabitedMapDeclarationExtension_default___closed__2;
    v___f_1956_ = l_Lean_instInhabitedMapDeclarationExtension_default___closed__1;
    v___f_1957_ = l_Lean_instInhabitedMapDeclarationExtension_default___closed__0;
    v___x_1958_ = crate::leanh::lean_box(0);
    v___x_1959_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedMapDeclarationExtension_default___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_instInhabitedMapDeclarationExtension_default___closed__4_once
        ),
        _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__4,
    );
    v___x_1960_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1960_, 0, v___x_1959_);
    crate::leanh::lean_ctor_set(v___x_1960_, 1, v___x_1958_);
    crate::leanh::lean_ctor_set(v___x_1960_, 2, v___f_1957_);
    crate::leanh::lean_ctor_set(v___x_1960_, 3, v___f_1956_);
    crate::leanh::lean_ctor_set(v___x_1960_, 4, v___f_1955_);
    crate::leanh::lean_ctor_set(v___x_1960_, 5, v___f_1954_);
    return v___x_1960_;
}
pub unsafe fn l_Lean_instInhabitedMapDeclarationExtension_default(
    mut v_00_u03b1_1961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1962_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedMapDeclarationExtension_default___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_instInhabitedMapDeclarationExtension_default___closed__5_once
        ),
        _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__5,
    );
    return v___x_1962_;
}
pub unsafe fn _init_l_Lean_instInhabitedMapDeclarationExtension___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1963_ = l_Lean_instInhabitedMapDeclarationExtension_default(crate::leanh::lean_box(0));
    return v___x_1963_;
}
pub unsafe fn l_Lean_instInhabitedMapDeclarationExtension(
    mut v_a_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1965_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedMapDeclarationExtension___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedMapDeclarationExtension___closed__0_once),
        _init_l_Lean_instInhabitedMapDeclarationExtension___closed__0,
    );
    return v___x_1965_;
}
pub unsafe fn _init_l_Lean_mkMapDeclarationExtension___auto__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1966_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once
        ),
        _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28,
    );
    return v___x_1966_;
}
pub unsafe fn l_Lean_mkMapDeclarationExtension___redArg___lam__0(
    mut v_s_1967_: *mut crate::leanh::LeanObject,
    mut v_x_1968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1969_ = crate::leanh::lean_ctor_get(v_x_1968_, 0);
    crate::leanh::lean_inc(v_fst_1969_);
    v_snd_1970_ = crate::leanh::lean_ctor_get(v_x_1968_, 1);
    crate::leanh::lean_inc(v_snd_1970_);
    crate::leanh::lean_dec_ref(v_x_1968_);
    v___x_1971_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_fst_1969_,
        v_snd_1970_,
        v_s_1967_,
    );
    return v___x_1971_;
}
pub unsafe fn l_Lean_mkMapDeclarationExtension___redArg___lam__1(
    mut v_exportEntriesFn_1972_: *mut crate::leanh::LeanObject,
    mut v_env_1973_: *mut crate::leanh::LeanObject,
    mut v_s_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1975_ = crate::leanh::lean_apply_2(v_exportEntriesFn_1972_, v_env_1973_, v_s_1974_);
    return v___x_1975_;
}
pub unsafe fn l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(
    mut v_newState_1976_: *mut crate::leanh::LeanObject,
    mut v_x_1977_: *mut crate::leanh::LeanObject,
    mut v_x_1978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1978_) == 0 {
                    return v_x_1977_;
                } else {
                    v_head_1979_ = crate::leanh::lean_ctor_get(v_x_1978_, 0);
                    crate::leanh::lean_inc(v_head_1979_);
                    v_tail_1980_ = crate::leanh::lean_ctor_get(v_x_1978_, 1);
                    crate::leanh::lean_inc(v_tail_1980_);
                    crate::leanh::lean_dec_ref_known(v_x_1978_, 2);
                    v___x_1981_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_1976_, v_head_1979_);
                    if crate::leanh::lean_obj_tag(v___x_1981_) == 1 {
                        v_val_1982_ = crate::leanh::lean_ctor_get(v___x_1981_, 0);
                        crate::leanh::lean_inc(v_val_1982_);
                        crate::leanh::lean_dec_ref_known(v___x_1981_, 1);
                        v___x_1983_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_1979_, v_val_1982_, v_x_1977_);
                        v_x_1977_ = v___x_1983_;
                        v_x_1978_ = v_tail_1980_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1981_);
                        crate::leanh::lean_dec(v_head_1979_);
                        v_x_1978_ = v_tail_1980_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg___boxed(
    mut v_newState_1986_: *mut crate::leanh::LeanObject,
    mut v_x_1987_: *mut crate::leanh::LeanObject,
    mut v_x_1988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1989_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(
        v_newState_1986_,
        v_x_1987_,
        v_x_1988_,
    );
    crate::leanh::lean_dec(v_newState_1986_);
    return v_res_1989_;
}
pub unsafe fn l_Lean_mkMapDeclarationExtension___redArg___lam__3(
    mut v_x_1990_: *mut crate::leanh::LeanObject,
    mut v_newState_1991_: *mut crate::leanh::LeanObject,
    mut v_newConsts_1992_: *mut crate::leanh::LeanObject,
    mut v_s_1993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1994_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(
        v_newState_1991_,
        v_s_1993_,
        v_newConsts_1992_,
    );
    return v___x_1994_;
}
pub unsafe fn l_Lean_mkMapDeclarationExtension___redArg___lam__3___boxed(
    mut v_x_1995_: *mut crate::leanh::LeanObject,
    mut v_newState_1996_: *mut crate::leanh::LeanObject,
    mut v_newConsts_1997_: *mut crate::leanh::LeanObject,
    mut v_s_1998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1999_ = l_Lean_mkMapDeclarationExtension___redArg___lam__3(
        v_x_1995_,
        v_newState_1996_,
        v_newConsts_1997_,
        v_s_1998_,
    );
    crate::leanh::lean_dec(v_newState_1996_);
    crate::leanh::lean_dec(v_x_1995_);
    return v_res_1999_;
}
pub unsafe fn l_Lean_mkMapDeclarationExtension___redArg___lam__2(
    mut v_x_2000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2001_ = l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__0;
    return v___x_2001_;
}
pub unsafe fn l_Lean_mkMapDeclarationExtension___redArg___lam__2___boxed(
    mut v_x_2002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2003_ = l_Lean_mkMapDeclarationExtension___redArg___lam__2(v_x_2002_);
    crate::leanh::lean_dec(v_x_2002_);
    return v_res_2003_;
}
pub unsafe fn l_Lean_mkMapDeclarationExtension___redArg___lam__4(
    mut v___x_2004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2006_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2006_, 0, v___x_2004_);
    return v___x_2006_;
}
pub unsafe fn l_Lean_mkMapDeclarationExtension___redArg___lam__4___boxed(
    mut v___x_2007_: *mut crate::leanh::LeanObject,
    mut v___y_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2009_ = l_Lean_mkMapDeclarationExtension___redArg___lam__4(v___x_2007_);
    return v_res_2009_;
}
pub unsafe fn l_Lean_mkMapDeclarationExtension___redArg___lam__5(
    mut v___x_2010_: *mut crate::leanh::LeanObject,
    mut v_x_2011_: *mut crate::leanh::LeanObject,
    mut v___y_2012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2014_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2014_, 0, v___x_2010_);
    return v___x_2014_;
}
pub unsafe fn l_Lean_mkMapDeclarationExtension___redArg___lam__5___boxed(
    mut v___x_2015_: *mut crate::leanh::LeanObject,
    mut v_x_2016_: *mut crate::leanh::LeanObject,
    mut v___y_2017_: *mut crate::leanh::LeanObject,
    mut v___y_2018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2019_ =
        l_Lean_mkMapDeclarationExtension___redArg___lam__5(v___x_2015_, v_x_2016_, v___y_2017_);
    crate::leanh::lean_dec_ref(v___y_2017_);
    crate::leanh::lean_dec_ref(v_x_2016_);
    return v_res_2019_;
}
pub unsafe fn l_Lean_mkMapDeclarationExtension___redArg(
    mut v_name_2029_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_2030_: *mut crate::leanh::LeanObject,
    mut v_exportEntriesFn_2031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2046_: u8 = 0;
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut v_a_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2054_: u8 = 0;
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2033_ = l_Lean_mkMapDeclarationExtension___redArg___closed__0;
                v___f_2034_ = crate::leanh::lean_alloc_closure(
                    l_Lean_mkMapDeclarationExtension___redArg___lam__1 as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2034_, 0, v_exportEntriesFn_2031_);
                v___f_2035_ = l_Lean_instInhabitedMapDeclarationExtension_default___closed__3;
                v___f_2036_ = l_Lean_mkMapDeclarationExtension___redArg___closed__2;
                v___f_2037_ = l_Lean_mkMapDeclarationExtension___redArg___closed__3;
                v___f_2038_ = l_Lean_mkMapDeclarationExtension___redArg___closed__4;
                v___x_2039_ = l_Lean_mkMapDeclarationExtension___redArg___closed__5;
                v___x_2040_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2040_, 0, v_name_2029_);
                crate::leanh::lean_ctor_set(v___x_2040_, 1, v___f_2037_);
                crate::leanh::lean_ctor_set(v___x_2040_, 2, v___f_2038_);
                crate::leanh::lean_ctor_set(v___x_2040_, 3, v___f_2033_);
                crate::leanh::lean_ctor_set(v___x_2040_, 4, v___f_2034_);
                crate::leanh::lean_ctor_set(v___x_2040_, 5, v___f_2035_);
                crate::leanh::lean_ctor_set(v___x_2040_, 6, v_asyncMode_2030_);
                crate::leanh::lean_ctor_set(v___x_2040_, 7, v___x_2039_);
                v___x_2041_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2041_, 0, v___x_2040_);
                crate::leanh::lean_ctor_set(v___x_2041_, 1, v___f_2036_);
                v___x_2042_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2041_);
                if crate::leanh::lean_obj_tag(v___x_2042_) == 0 {
                    v_a_2043_ = crate::leanh::lean_ctor_get(v___x_2042_, 0);
                    v_isSharedCheck_2050_ = (!crate::leanh::lean_is_exclusive(v___x_2042_)) as u8;
                    if v_isSharedCheck_2050_ == 0 {
                        v___x_2045_ = v___x_2042_;
                        v_isShared_2046_ = v_isSharedCheck_2050_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2043_);
                        crate::leanh::lean_dec(v___x_2042_);
                        v___x_2045_ = crate::leanh::lean_box(0);
                        v_isShared_2046_ = v_isSharedCheck_2050_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2051_ = crate::leanh::lean_ctor_get(v___x_2042_, 0);
                    v_isSharedCheck_2058_ = (!crate::leanh::lean_is_exclusive(v___x_2042_)) as u8;
                    if v_isSharedCheck_2058_ == 0 {
                        v___x_2053_ = v___x_2042_;
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2051_);
                        crate::leanh::lean_dec(v___x_2042_);
                        v___x_2053_ = crate::leanh::lean_box(0);
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2046_ == 0 {
                    v___x_2048_ = v___x_2045_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2049_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
                    v___x_2048_ = v_reuseFailAlloc_2049_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2048_;
            }
            3 => {
                if v_isShared_2054_ == 0 {
                    v___x_2056_ = v___x_2053_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
                    v___x_2056_ = v_reuseFailAlloc_2057_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2056_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkMapDeclarationExtension___redArg___boxed(
    mut v_name_2059_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_2060_: *mut crate::leanh::LeanObject,
    mut v_exportEntriesFn_2061_: *mut crate::leanh::LeanObject,
    mut v_a_2062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2063_ = l_Lean_mkMapDeclarationExtension___redArg(
        v_name_2059_,
        v_asyncMode_2060_,
        v_exportEntriesFn_2061_,
    );
    return v_res_2063_;
}
pub unsafe fn l_Lean_mkMapDeclarationExtension(
    mut v_00_u03b1_2064_: *mut crate::leanh::LeanObject,
    mut v_name_2065_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_2066_: *mut crate::leanh::LeanObject,
    mut v_exportEntriesFn_2067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2069_ = l_Lean_mkMapDeclarationExtension___redArg(
        v_name_2065_,
        v_asyncMode_2066_,
        v_exportEntriesFn_2067_,
    );
    return v___x_2069_;
}
pub unsafe fn l_Lean_mkMapDeclarationExtension___boxed(
    mut v_00_u03b1_2070_: *mut crate::leanh::LeanObject,
    mut v_name_2071_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_2072_: *mut crate::leanh::LeanObject,
    mut v_exportEntriesFn_2073_: *mut crate::leanh::LeanObject,
    mut v_a_2074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2075_ = l_Lean_mkMapDeclarationExtension(
        v_00_u03b1_2070_,
        v_name_2071_,
        v_asyncMode_2072_,
        v_exportEntriesFn_2073_,
    );
    return v_res_2075_;
}
pub unsafe fn l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0(
    mut v_00_u03b1_2076_: *mut crate::leanh::LeanObject,
    mut v_newState_2077_: *mut crate::leanh::LeanObject,
    mut v_x_2078_: *mut crate::leanh::LeanObject,
    mut v_x_2079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2080_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(
        v_newState_2077_,
        v_x_2078_,
        v_x_2079_,
    );
    return v___x_2080_;
}
pub unsafe fn l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___boxed(
    mut v_00_u03b1_2081_: *mut crate::leanh::LeanObject,
    mut v_newState_2082_: *mut crate::leanh::LeanObject,
    mut v_x_2083_: *mut crate::leanh::LeanObject,
    mut v_x_2084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2085_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0(
        v_00_u03b1_2081_,
        v_newState_2082_,
        v_x_2083_,
        v_x_2084_,
    );
    crate::leanh::lean_dec(v_newState_2082_);
    return v_res_2085_;
}
pub unsafe fn l_Lean_MapDeclarationExtension_insert___redArg(
    mut v_ext_2091_: *mut crate::leanh::LeanObject,
    mut v_env_2092_: *mut crate::leanh::LeanObject,
    mut v_declName_2093_: *mut crate::leanh::LeanObject,
    mut v_val_2094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2095_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2092_, v_declName_2093_);
    if crate::leanh::lean_obj_tag(v___x_2095_) == 1 {
        let mut v_val_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_name_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2104_: u8 = 0;
        let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_val_2094_);
        v_val_2096_ = crate::leanh::lean_ctor_get(v___x_2095_, 0);
        crate::leanh::lean_inc(v_val_2096_);
        crate::leanh::lean_dec_ref_known(v___x_2095_, 1);
        v_name_2097_ = crate::leanh::lean_ctor_get(v_ext_2091_, 1);
        crate::leanh::lean_inc(v_name_2097_);
        crate::leanh::lean_dec_ref(v_ext_2091_);
        v___x_2098_ = crate::leanh::lean_box(0);
        v___x_2099_ = l_Lean_TagDeclarationExtension_tag___closed__0;
        v___x_2100_ = l_Lean_MapDeclarationExtension_insert___redArg___closed__0;
        v___x_2101_ = crate::leanh::lean_unsigned_to_nat(159);
        v___x_2102_ = crate::leanh::lean_unsigned_to_nat(4);
        v___x_2103_ = l_Lean_MapDeclarationExtension_insert___redArg___closed__1;
        v___x_2104_ = 1;
        v___x_2105_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_declName_2093_,
            v___x_2104_,
        );
        v___x_2106_ = lean_string_append(v___x_2103_, v___x_2105_);
        crate::leanh::lean_dec_ref(v___x_2105_);
        v___x_2107_ = l_Lean_MapDeclarationExtension_insert___redArg___closed__2;
        v___x_2108_ = lean_string_append(v___x_2106_, v___x_2107_);
        v___x_2109_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_name_2097_,
            v___x_2104_,
        );
        v___x_2110_ = lean_string_append(v___x_2108_, v___x_2109_);
        crate::leanh::lean_dec_ref(v___x_2109_);
        v___x_2111_ = l_Lean_MapDeclarationExtension_insert___redArg___closed__3;
        v___x_2112_ = lean_string_append(v___x_2110_, v___x_2111_);
        v___x_2113_ = l_Lean_Environment_allImportedModuleNames(v_env_2092_);
        v___x_2114_ = lean_array_get(v___x_2098_, v___x_2113_, v_val_2096_);
        crate::leanh::lean_dec(v_val_2096_);
        crate::leanh::lean_dec_ref(v___x_2113_);
        v___x_2115_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v___x_2114_,
            v___x_2104_,
        );
        v___x_2116_ = lean_string_append(v___x_2112_, v___x_2115_);
        crate::leanh::lean_dec_ref(v___x_2115_);
        v___x_2117_ = l_Lean_MapDeclarationExtension_insert___redArg___closed__4;
        v___x_2118_ = lean_string_append(v___x_2116_, v___x_2117_);
        v___x_2119_ = l_mkPanicMessageWithDecl(
            v___x_2099_,
            v___x_2100_,
            v___x_2101_,
            v___x_2102_,
            v___x_2118_,
        );
        crate::leanh::lean_dec_ref(v___x_2118_);
        v___x_2120_ = lean_panic_fn_borrowed(v_env_2092_, v___x_2119_);
        crate::leanh::lean_dec_ref(v_env_2092_);
        return v___x_2120_;
    } else {
        let mut v_toEnvExtension_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_asyncMode_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_2095_);
        v_toEnvExtension_2121_ = crate::leanh::lean_ctor_get(v_ext_2091_, 0);
        v_asyncMode_2122_ = crate::leanh::lean_ctor_get(v_toEnvExtension_2121_, 2);
        crate::leanh::lean_inc(v_asyncMode_2122_);
        crate::leanh::lean_inc(v_declName_2093_);
        v___x_2123_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2123_, 0, v_declName_2093_);
        crate::leanh::lean_ctor_set(v___x_2123_, 1, v_val_2094_);
        v___x_2124_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
            v_ext_2091_,
            v_env_2092_,
            v___x_2123_,
            v_asyncMode_2122_,
            v_declName_2093_,
        );
        crate::leanh::lean_dec(v_asyncMode_2122_);
        return v___x_2124_;
    }
}
pub unsafe fn l_Lean_MapDeclarationExtension_insert(
    mut v_00_u03b1_2125_: *mut crate::leanh::LeanObject,
    mut v_ext_2126_: *mut crate::leanh::LeanObject,
    mut v_env_2127_: *mut crate::leanh::LeanObject,
    mut v_declName_2128_: *mut crate::leanh::LeanObject,
    mut v_val_2129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2130_ = l_Lean_MapDeclarationExtension_insert___redArg(
        v_ext_2126_,
        v_env_2127_,
        v_declName_2128_,
        v_val_2129_,
    );
    return v___x_2130_;
}
pub unsafe fn l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0(
    mut v_a_2131_: *mut crate::leanh::LeanObject,
    mut v_b_2132_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: u8 = 0;
    v_fst_2133_ = crate::leanh::lean_ctor_get(v_a_2131_, 0);
    v_fst_2134_ = crate::leanh::lean_ctor_get(v_b_2132_, 0);
    v___x_2135_ = l_Lean_Name_quickLt(v_fst_2133_, v_fst_2134_);
    return v___x_2135_;
}
pub unsafe fn l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0___boxed(
    mut v_a_2136_: *mut crate::leanh::LeanObject,
    mut v_b_2137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2138_: u8 = 0;
    let mut v_r_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2138_ = l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0(v_a_2136_, v_b_2137_);
    crate::leanh::lean_dec_ref(v_b_2137_);
    crate::leanh::lean_dec_ref(v_a_2136_);
    v_r_2139_ = crate::leanh::lean_box((v_res_2138_) as usize);
    return v_r_2139_;
}
pub unsafe fn l_Lean_MapDeclarationExtension_find_x3f___redArg(
    mut v_inst_2142_: *mut crate::leanh::LeanObject,
    mut v_ext_2143_: *mut crate::leanh::LeanObject,
    mut v_env_2144_: *mut crate::leanh::LeanObject,
    mut v_declName_2145_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_2146_: *mut crate::leanh::LeanObject,
    mut v_level_2147_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: u8 = 0;
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: u8 = 0;
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2170_: u8 = 0;
    let mut v_snd_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2175_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2148_ = crate::leanh::lean_box(1);
                v___x_2149_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2144_, v_declName_2145_);
                if crate::leanh::lean_obj_tag(v___x_2149_) == 0 {
                    crate::leanh::lean_dec(v_inst_2142_);
                    crate::leanh::lean_inc(v_declName_2145_);
                    v___x_2150_ = l_Lean_PersistentEnvExtension_getState___redArg(
                        v___x_2148_,
                        v_ext_2143_,
                        v_env_2144_,
                        v_asyncMode_2146_,
                        v_declName_2145_,
                    );
                    v___x_2151_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2150_, v_declName_2145_);
                    crate::leanh::lean_dec(v_declName_2145_);
                    crate::leanh::lean_dec(v___x_2150_);
                    return v___x_2151_;
                } else {
                    v_val_2152_ = crate::leanh::lean_ctor_get(v___x_2149_, 0);
                    crate::leanh::lean_inc(v_val_2152_);
                    crate::leanh::lean_dec_ref_known(v___x_2149_, 1);
                    v___x_2153_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
                        v___x_2148_,
                        v_ext_2143_,
                        v_env_2144_,
                        v_val_2152_,
                        v_level_2147_,
                    );
                    crate::leanh::lean_dec(v_val_2152_);
                    crate::leanh::lean_dec_ref(v_env_2144_);
                    v___x_2154_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2155_ = lean_array_get_size(v___x_2153_);
                    v___x_2156_ = lean_nat_dec_lt(v___x_2154_, v___x_2155_);
                    if v___x_2156_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2153_);
                        crate::leanh::lean_dec(v_declName_2145_);
                        crate::leanh::lean_dec(v_inst_2142_);
                        v___x_2157_ = crate::leanh::lean_box(0);
                        return v___x_2157_;
                    } else {
                        v___x_2158_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2159_ = lean_nat_sub(v___x_2155_, v___x_2158_);
                        v___x_2160_ = lean_nat_dec_le(v___x_2154_, v___x_2159_);
                        if v___x_2160_ == 0 {
                            crate::leanh::lean_dec(v___x_2159_);
                            crate::leanh::lean_dec_ref(v___x_2153_);
                            crate::leanh::lean_dec(v_declName_2145_);
                            crate::leanh::lean_dec(v_inst_2142_);
                            v___x_2161_ = crate::leanh::lean_box(0);
                            return v___x_2161_;
                        } else {
                            v___f_2162_ =
                                l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0;
                            v___x_2163_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2163_, 0, v_declName_2145_);
                            crate::leanh::lean_ctor_set(v___x_2163_, 1, v_inst_2142_);
                            v___x_2164_ =
                                l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__1;
                            v___x_2165_ = l_Array_binSearchAux___redArg(
                                v___f_2162_,
                                v___x_2164_,
                                v___x_2153_,
                                v___x_2163_,
                                v___x_2154_,
                                v___x_2159_,
                            );
                            crate::leanh::lean_dec_ref(v___x_2153_);
                            if crate::leanh::lean_obj_tag(v___x_2165_) == 0 {
                                v___x_2166_ = crate::leanh::lean_box(0);
                                return v___x_2166_;
                            } else {
                                v_val_2167_ = crate::leanh::lean_ctor_get(v___x_2165_, 0);
                                v_isSharedCheck_2175_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2165_)) as u8;
                                if v_isSharedCheck_2175_ == 0 {
                                    v___x_2169_ = v___x_2165_;
                                    v_isShared_2170_ = v_isSharedCheck_2175_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_2167_);
                                    crate::leanh::lean_dec(v___x_2165_);
                                    v___x_2169_ = crate::leanh::lean_box(0);
                                    v_isShared_2170_ = v_isSharedCheck_2175_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v_snd_2171_ = crate::leanh::lean_ctor_get(v_val_2167_, 1);
                crate::leanh::lean_inc(v_snd_2171_);
                crate::leanh::lean_dec(v_val_2167_);
                if v_isShared_2170_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2169_, 0, v_snd_2171_);
                    v___x_2173_ = v___x_2169_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2174_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_snd_2171_);
                    v___x_2173_ = v_reuseFailAlloc_2174_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2173_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MapDeclarationExtension_find_x3f___redArg___boxed(
    mut v_inst_2176_: *mut crate::leanh::LeanObject,
    mut v_ext_2177_: *mut crate::leanh::LeanObject,
    mut v_env_2178_: *mut crate::leanh::LeanObject,
    mut v_declName_2179_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_2180_: *mut crate::leanh::LeanObject,
    mut v_level_2181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_level_boxed_2182_: u8 = 0;
    let mut v_res_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_level_boxed_2182_ = (crate::leanh::lean_unbox(v_level_2181_) as u8);
    v_res_2183_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
        v_inst_2176_,
        v_ext_2177_,
        v_env_2178_,
        v_declName_2179_,
        v_asyncMode_2180_,
        v_level_boxed_2182_,
    );
    crate::leanh::lean_dec(v_asyncMode_2180_);
    crate::leanh::lean_dec_ref(v_ext_2177_);
    return v_res_2183_;
}
pub unsafe fn l_Lean_MapDeclarationExtension_find_x3f(
    mut v_00_u03b1_2184_: *mut crate::leanh::LeanObject,
    mut v_inst_2185_: *mut crate::leanh::LeanObject,
    mut v_ext_2186_: *mut crate::leanh::LeanObject,
    mut v_env_2187_: *mut crate::leanh::LeanObject,
    mut v_declName_2188_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_2189_: *mut crate::leanh::LeanObject,
    mut v_level_2190_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2191_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
        v_inst_2185_,
        v_ext_2186_,
        v_env_2187_,
        v_declName_2188_,
        v_asyncMode_2189_,
        v_level_2190_,
    );
    return v___x_2191_;
}
pub unsafe fn l_Lean_MapDeclarationExtension_find_x3f___boxed(
    mut v_00_u03b1_2192_: *mut crate::leanh::LeanObject,
    mut v_inst_2193_: *mut crate::leanh::LeanObject,
    mut v_ext_2194_: *mut crate::leanh::LeanObject,
    mut v_env_2195_: *mut crate::leanh::LeanObject,
    mut v_declName_2196_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_2197_: *mut crate::leanh::LeanObject,
    mut v_level_2198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_level_boxed_2199_: u8 = 0;
    let mut v_res_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_level_boxed_2199_ = (crate::leanh::lean_unbox(v_level_2198_) as u8);
    v_res_2200_ = l_Lean_MapDeclarationExtension_find_x3f(
        v_00_u03b1_2192_,
        v_inst_2193_,
        v_ext_2194_,
        v_env_2195_,
        v_declName_2196_,
        v_asyncMode_2197_,
        v_level_boxed_2199_,
    );
    crate::leanh::lean_dec(v_asyncMode_2197_);
    crate::leanh::lean_dec_ref(v_ext_2194_);
    return v_res_2200_;
}
pub unsafe fn l_Lean_MapDeclarationExtension_contains___redArg(
    mut v_inst_2202_: *mut crate::leanh::LeanObject,
    mut v_ext_2203_: *mut crate::leanh::LeanObject,
    mut v_env_2204_: *mut crate::leanh::LeanObject,
    mut v_declName_2205_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2206_ = crate::leanh::lean_box(1);
    v___x_2207_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2204_, v_declName_2205_);
    if crate::leanh::lean_obj_tag(v___x_2207_) == 0 {
        let mut v_toEnvExtension_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_asyncMode_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2211_: u8 = 0;
        crate::leanh::lean_dec(v_inst_2202_);
        v_toEnvExtension_2208_ = crate::leanh::lean_ctor_get(v_ext_2203_, 0);
        v_asyncMode_2209_ = crate::leanh::lean_ctor_get(v_toEnvExtension_2208_, 2);
        crate::leanh::lean_inc(v_declName_2205_);
        v___x_2210_ = l_Lean_PersistentEnvExtension_getState___redArg(
            v___x_2206_,
            v_ext_2203_,
            v_env_2204_,
            v_asyncMode_2209_,
            v_declName_2205_,
        );
        v___x_2211_ =
            l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(
                v_declName_2205_,
                v___x_2210_,
            );
        crate::leanh::lean_dec(v___x_2210_);
        crate::leanh::lean_dec(v_declName_2205_);
        return v___x_2211_;
    } else {
        let mut v_val_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2213_: u8 = 0;
        let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2217_: u8 = 0;
        v_val_2212_ = crate::leanh::lean_ctor_get(v___x_2207_, 0);
        crate::leanh::lean_inc(v_val_2212_);
        crate::leanh::lean_dec_ref_known(v___x_2207_, 1);
        v___x_2213_ = 0;
        v___x_2214_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
            v___x_2206_,
            v_ext_2203_,
            v_env_2204_,
            v_val_2212_,
            v___x_2213_,
        );
        crate::leanh::lean_dec(v_val_2212_);
        crate::leanh::lean_dec_ref(v_env_2204_);
        v___x_2215_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2216_ = lean_array_get_size(v___x_2214_);
        v___x_2217_ = lean_nat_dec_lt(v___x_2215_, v___x_2216_);
        if v___x_2217_ == 0 {
            crate::leanh::lean_dec_ref(v___x_2214_);
            crate::leanh::lean_dec(v_declName_2205_);
            crate::leanh::lean_dec(v_inst_2202_);
            return v___x_2217_;
        } else {
            let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2220_: u8 = 0;
            v___x_2218_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_2219_ = lean_nat_sub(v___x_2216_, v___x_2218_);
            v___x_2220_ = lean_nat_dec_le(v___x_2215_, v___x_2219_);
            if v___x_2220_ == 0 {
                crate::leanh::lean_dec(v___x_2219_);
                crate::leanh::lean_dec_ref(v___x_2214_);
                crate::leanh::lean_dec(v_declName_2205_);
                crate::leanh::lean_dec(v_inst_2202_);
                return v___x_2220_;
            } else {
                let mut v___f_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2225_: u8 = 0;
                v___f_2221_ = l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0;
                v___x_2222_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2222_, 0, v_declName_2205_);
                crate::leanh::lean_ctor_set(v___x_2222_, 1, v_inst_2202_);
                v___x_2223_ = l_Lean_MapDeclarationExtension_contains___redArg___closed__0;
                v___x_2224_ = l_Array_binSearchAux___redArg(
                    v___f_2221_,
                    v___x_2223_,
                    v___x_2214_,
                    v___x_2222_,
                    v___x_2215_,
                    v___x_2219_,
                );
                crate::leanh::lean_dec_ref(v___x_2214_);
                v___x_2225_ = (crate::leanh::lean_unbox(v___x_2224_) as u8);
                crate::leanh::lean_dec(v___x_2224_);
                return v___x_2225_;
            }
        }
    }
}
pub unsafe fn l_Lean_MapDeclarationExtension_contains___redArg___boxed(
    mut v_inst_2226_: *mut crate::leanh::LeanObject,
    mut v_ext_2227_: *mut crate::leanh::LeanObject,
    mut v_env_2228_: *mut crate::leanh::LeanObject,
    mut v_declName_2229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2230_: u8 = 0;
    let mut v_r_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2230_ = l_Lean_MapDeclarationExtension_contains___redArg(
        v_inst_2226_,
        v_ext_2227_,
        v_env_2228_,
        v_declName_2229_,
    );
    crate::leanh::lean_dec_ref(v_ext_2227_);
    v_r_2231_ = crate::leanh::lean_box((v_res_2230_) as usize);
    return v_r_2231_;
}
pub unsafe fn l_Lean_MapDeclarationExtension_contains(
    mut v_00_u03b1_2232_: *mut crate::leanh::LeanObject,
    mut v_inst_2233_: *mut crate::leanh::LeanObject,
    mut v_ext_2234_: *mut crate::leanh::LeanObject,
    mut v_env_2235_: *mut crate::leanh::LeanObject,
    mut v_declName_2236_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2237_: u8 = 0;
    v___x_2237_ = l_Lean_MapDeclarationExtension_contains___redArg(
        v_inst_2233_,
        v_ext_2234_,
        v_env_2235_,
        v_declName_2236_,
    );
    return v___x_2237_;
}
pub unsafe fn l_Lean_MapDeclarationExtension_contains___boxed(
    mut v_00_u03b1_2238_: *mut crate::leanh::LeanObject,
    mut v_inst_2239_: *mut crate::leanh::LeanObject,
    mut v_ext_2240_: *mut crate::leanh::LeanObject,
    mut v_env_2241_: *mut crate::leanh::LeanObject,
    mut v_declName_2242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2243_: u8 = 0;
    let mut v_r_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2243_ = l_Lean_MapDeclarationExtension_contains(
        v_00_u03b1_2238_,
        v_inst_2239_,
        v_ext_2240_,
        v_env_2241_,
        v_declName_2242_,
    );
    crate::leanh::lean_dec_ref(v_ext_2240_);
    v_r_2244_ = crate::leanh::lean_box((v_res_2243_) as usize);
    return v_r_2244_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_EnvExtension(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Environment(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_TagDeclarationExtension_instInhabited___aux__1 =
        _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1();
    crate::leanh::lean_mark_persistent(l_Lean_TagDeclarationExtension_instInhabited___aux__1);
    l_Lean_TagDeclarationExtension_instInhabited =
        _init_l_Lean_TagDeclarationExtension_instInhabited();
    crate::leanh::lean_mark_persistent(l_Lean_TagDeclarationExtension_instInhabited);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_EnvExtension(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam =
        _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam();
    crate::leanh::lean_mark_persistent(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam);
    l_Lean_mkTagDeclarationExtension___auto__1 = _init_l_Lean_mkTagDeclarationExtension___auto__1();
    crate::leanh::lean_mark_persistent(l_Lean_mkTagDeclarationExtension___auto__1);
    l_Lean_mkMapDeclarationExtension___auto__3 = _init_l_Lean_mkMapDeclarationExtension___auto__3();
    crate::leanh::lean_mark_persistent(l_Lean_mkMapDeclarationExtension___auto__3);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_EnvExtension(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Environment(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_EnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_EnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_EnvExtension(builtin);
}
