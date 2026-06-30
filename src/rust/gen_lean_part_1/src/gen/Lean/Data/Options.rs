// Lean compiler output
// Module: Lean.Data.Options
// Imports: Lean.ImportingFlag Lean.Data.KVMap Lean.Data.NameMap.Basic Init.Data.ToString.Macro
use crate::ffi::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mul, lean_st_mk_ref, lean_st_ref_get,
    lean_st_ref_set, lean_string_append, lean_string_dec_eq, lean_string_intercalate,
    lean_string_utf8_byte_size,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::ToString::Basic::l_instToStringProd___redArg___lam__0;
use crate::r#gen::Init::Data::ToString::Extra::l_List_toString___redArg;
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_instToString___lam__0,
    l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f, l_Lean_Syntax_mkNameLit,
    l_Lean_TSyntax_getId, l_Lean_quoteNameMk,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getOptional_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4,
    l_Lean_Syntax_node7, l_Lean_addMacroScope, l_Lean_mkAtom, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Lean::Data::KVMap::{
    initialize_Lean_Data_KVMap, l_Lean_KVMap_instValueBool, l_Lean_instBEqDataValue_beq,
    l_Lean_instBEqDataValue_beq___boxed, l_Lean_instInhabitedDataValue_default,
    lean_data_value_to_string, runtime_initialize_Lean_Data_KVMap,
};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl,
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, l_Lean_Name_isPrefixOf,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    initialize_Lean_Data_NameMap_Basic,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
    runtime_initialize_Lean_Data_NameMap_Basic,
};
use crate::r#gen::Lean::ImportingFlag::{
    initialize_Lean_ImportingFlag, l_Lean_initializing, runtime_initialize_Lean_ImportingFlag,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Balancing::l_Std_DTreeMap_Internal_Impl_balance___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_Const_beq___redArg, l_Std_DTreeMap_Internal_Impl_maxView___redArg,
    l_Std_DTreeMap_Internal_Impl_minView___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::{
    l_Std_DTreeMap_Internal_Impl_foldrM___redArg, l_Std_DTreeMap_Internal_Impl_forInStep___redArg,
};
pub static l_Lean_Options_empty___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Options_empty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_empty___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_Options_empty: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_empty___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_Options_instInhabited: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_empty___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Options_instToString___private__1___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Options_instToString___private__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Name_instToString___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Options_instToString___private__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: lean_data_value_to_string as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Options_instToString___private__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__3_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToStringProd___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Options_instToString___private__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__4_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Options_instToString___private__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__5_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Options_instToString___private__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__6_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Options_instToString___private__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__7_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Options_instToString___private__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__8_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Options_instToString___private__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__9_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Options_instToString___private__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__10_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Options_instToString___private__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__11_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Options_instToString___private__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__12_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__11_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Options_instToString___private__1___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__13_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__12_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Options_instToString___private__1___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_instToString___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Options_instToString___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Options_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Options_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_instBEq___private__1___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instBEqDataValue_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Options_instBEq___private__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instBEq___private__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_instBEq___private__1___closed__1_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Options_instBEq___private__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instBEq___private__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_instBEq___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Options_instBEq___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Options_instBEq___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instBEq___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_Options_instBEq: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instBEq___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_Options_instEmptyCollection: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_empty___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Options_insert___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Options_insert___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_insert___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Options_insert___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Options_insert___closed__0_value)
                as *mut leanh::LeanObject,
            14231257465488249300 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Options_insert___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Options_insert___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_instInhabitedOptionDeprecation_default___closed__0_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_instInhabitedOptionDeprecation_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedOptionDeprecation_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instInhabitedOptionDeprecation_default___closed__1_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instInhabitedOptionDeprecation_default___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedOptionDeprecation_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedOptionDeprecation_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedOptionDeprecation_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedOptionDeprecation_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedOptionDeprecation: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedOptionDeprecation_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
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
static mut l_Lean_OptionDecl_declName___autoParam___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
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
static mut l_Lean_OptionDecl_declName___autoParam___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__2_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
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
static mut l_Lean_OptionDecl_declName___autoParam___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__3_value:
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
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_OptionDecl_declName___autoParam___closed__4_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__3_value)
            as *mut leanh::LeanObject,
        8504843326314613972 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__5_value: leanh::LeanArrayObject<
    0,
> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__6_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
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
static mut l_Lean_OptionDecl_declName___autoParam___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_OptionDecl_declName___autoParam___closed__7_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_OptionDecl_declName___autoParam___closed__7_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__7_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_OptionDecl_declName___autoParam___closed__7_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__7_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_OptionDecl_declName___autoParam___closed__7_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__7_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__6_value)
            as *mut leanh::LeanObject,
        17228437386856258271 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__8_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
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
static mut l_Lean_OptionDecl_declName___autoParam___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__9_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__8_value)
            as *mut leanh::LeanObject,
        9855511589286918680 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__10_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
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
static mut l_Lean_OptionDecl_declName___autoParam___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__10_value)
        as *mut leanh::LeanObject;
static l_Lean_OptionDecl_declName___autoParam___closed__11_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_OptionDecl_declName___autoParam___closed__11_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__11_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_OptionDecl_declName___autoParam___closed__11_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__11_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_OptionDecl_declName___autoParam___closed__11_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__11_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__10_value)
            as *mut leanh::LeanObject,
        14997215300048349804 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_OptionDecl_declName___autoParam___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_OptionDecl_declName___autoParam___closed__14_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
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
static mut l_Lean_OptionDecl_declName___autoParam___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__15_value:
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
    m_data: [100, 101, 99, 108, 78, 97, 109, 101, 0],
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__15_value)
        as *mut leanh::LeanObject;
static l_Lean_OptionDecl_declName___autoParam___closed__16_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_OptionDecl_declName___autoParam___closed__16_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__16_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_OptionDecl_declName___autoParam___closed__16_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__16_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__14_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_OptionDecl_declName___autoParam___closed__16_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__16_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__15_value)
            as *mut leanh::LeanObject,
        7677164612348466033 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__17_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
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
static mut l_Lean_OptionDecl_declName___autoParam___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_OptionDecl_declName___autoParam___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__27_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__27: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_OptionDecl_declName___autoParam: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instInhabitedOptionDecl_default___closed__0_value:
    leanh::LeanStringObject<24> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        105, 110, 115, 116, 73, 110, 104, 97, 98, 105, 116, 101, 100, 79, 112, 116, 105, 111, 110,
        68, 101, 99, 108, 0,
    ],
};
static mut l_Lean_instInhabitedOptionDecl_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedOptionDecl_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instInhabitedOptionDecl_default___closed__1_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [100, 101, 102, 97, 117, 108, 116, 0],
};
static mut l_Lean_instInhabitedOptionDecl_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedOptionDecl_default___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_instInhabitedOptionDecl_default___closed__2_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_instInhabitedOptionDecl_default___closed__2_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instInhabitedOptionDecl_default___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instInhabitedOptionDecl_default___closed__0_value)
            as *mut leanh::LeanObject,
        12894178242470612343 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_instInhabitedOptionDecl_default___closed__2_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instInhabitedOptionDecl_default___closed__2_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instInhabitedOptionDecl_default___closed__1_value)
            as *mut leanh::LeanObject,
        7948044940217330697 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedOptionDecl_default___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedOptionDecl_default___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instInhabitedOptionDecl_default___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedOptionDecl_default___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedOptionDecl_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedOptionDecl: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_OptionDecl_fullDescr___closed__0_value: leanh::LeanStringObject<218> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 218,
        m_capacity: 218,
        m_length: 217,
        m_data: [
            84, 104, 105, 115, 32, 105, 115, 32, 97, 32, 98, 97, 99, 107, 119, 97, 114, 100, 115,
            32, 99, 111, 109, 112, 97, 116, 105, 98, 105, 108, 105, 116, 121, 32, 111, 112, 116,
            105, 111, 110, 44, 32, 105, 110, 116, 101, 110, 100, 101, 100, 32, 116, 111, 32, 104,
            101, 108, 112, 32, 109, 105, 103, 114, 97, 116, 105, 110, 103, 32, 116, 111, 32, 110,
            101, 119, 32, 76, 101, 97, 110, 32, 114, 101, 108, 101, 97, 115, 101, 115, 46, 32, 73,
            116, 32, 109, 97, 121, 32, 98, 101, 32, 114, 101, 109, 111, 118, 101, 100, 32, 119,
            105, 116, 104, 111, 117, 116, 32, 102, 117, 114, 116, 104, 101, 114, 32, 110, 111, 116,
            105, 99, 101, 32, 54, 32, 109, 111, 110, 116, 104, 115, 32, 97, 102, 116, 101, 114, 32,
            116, 104, 101, 105, 114, 32, 105, 110, 116, 114, 111, 100, 117, 99, 116, 105, 111, 110,
            46, 32, 80, 108, 101, 97, 115, 101, 32, 114, 101, 112, 111, 114, 116, 32, 97, 110, 32,
            105, 115, 115, 117, 101, 32, 105, 102, 32, 121, 111, 117, 32, 114, 101, 108, 121, 32,
            111, 110, 32, 116, 104, 105, 115, 32, 111, 112, 116, 105, 111, 110, 46, 0,
        ],
    };
static mut l_Lean_OptionDecl_fullDescr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_fullDescr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OptionDecl_fullDescr___closed__1_value: leanh::LeanStringObject<9> =
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
        m_data: [98, 97, 99, 107, 119, 97, 114, 100, 0],
    };
static mut l_Lean_OptionDecl_fullDescr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_fullDescr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OptionDecl_fullDescr___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_fullDescr___closed__1_value)
                as *mut leanh::LeanObject,
            15861075605163525197 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_OptionDecl_fullDescr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_fullDescr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OptionDecl_fullDescr___closed__3_value: leanh::LeanStringObject<3> =
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
        m_data: [10, 10, 0],
    };
static mut l_Lean_OptionDecl_fullDescr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_fullDescr___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedOptionDecls: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Lean_Data_Options_0__Lean_optionDeclsRef: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_registerOption___closed__0_value: leanh::LeanStringObject<80> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 80,
        m_capacity: 80,
        m_length: 79,
        m_data: [
            70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 103, 105, 115, 116, 101, 114,
            32, 111, 112, 116, 105, 111, 110, 58, 32, 79, 112, 116, 105, 111, 110, 115, 32, 99, 97,
            110, 32, 111, 110, 108, 121, 32, 98, 101, 32, 114, 101, 103, 105, 115, 116, 101, 114,
            101, 100, 32, 100, 117, 114, 105, 110, 103, 32, 105, 110, 105, 116, 105, 97, 108, 105,
            122, 97, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_registerOption___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerOption___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_registerOption___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerOption___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_registerOption___closed__2_value: leanh::LeanStringObject<29> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            73, 110, 118, 97, 108, 105, 100, 32, 111, 112, 116, 105, 111, 110, 32, 100, 101, 99,
            108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0,
        ],
    };
static mut l_Lean_registerOption___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerOption___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_registerOption___closed__3_value: leanh::LeanStringObject<25> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            96, 58, 32, 79, 112, 116, 105, 111, 110, 32, 97, 108, 114, 101, 97, 100, 121, 32, 101,
            120, 105, 115, 116, 115, 0,
        ],
    };
static mut l_Lean_registerOption___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerOption___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_getOptionDeclsArray___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Lean_getOptionDeclsArray___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getOptionDeclsArray___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_getOptionDecl___closed__0_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            85, 110, 107, 110, 111, 119, 110, 32, 111, 112, 116, 105, 111, 110, 32, 96, 0,
        ],
    };
static mut l_Lean_getOptionDecl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getOptionDecl___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_getOptionDecl___closed__1_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_getOptionDecl___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getOptionDecl___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_withInPattern___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [95, 105, 110, 80, 97, 116, 116, 101, 114, 110, 0],
};
static mut l_Lean_withInPattern___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_withInPattern___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_withInPattern___redArg___lam__0___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_withInPattern___redArg___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        1702504630968652677 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_withInPattern___redArg___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_withInPattern___redArg___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_withInPattern___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_withInPattern___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Option_register___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Option_registerBuiltinOption___closed__0_value: leanh::LeanStringObject<
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
    m_data: [79, 112, 116, 105, 111, 110, 0],
};
static mut l_Lean_Option_registerBuiltinOption___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__1_value: leanh::LeanStringObject<
    22,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        114, 101, 103, 105, 115, 116, 101, 114, 66, 117, 105, 108, 116, 105, 110, 79, 112, 116,
        105, 111, 110, 0,
    ],
};
static mut l_Lean_Option_registerBuiltinOption___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Option_registerBuiltinOption___closed__2_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Option_registerBuiltinOption___closed__2_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__0_value)
            as *mut leanh::LeanObject,
        3127099019797772086 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Option_registerBuiltinOption___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__2_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__1_value)
                as *mut leanh::LeanObject,
            5912347743684231271 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__3_value: leanh::LeanStringObject<
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
    m_data: [97, 110, 100, 116, 104, 101, 110, 0],
};
static mut l_Lean_Option_registerBuiltinOption___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__3_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__5_value: leanh::LeanStringObject<
    9,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Option_registerBuiltinOption___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__5_value)
                as *mut leanh::LeanObject,
            18170484695678750185 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__7_value: leanh::LeanStringObject<
    11,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Option_registerBuiltinOption___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__7_value)
                as *mut leanh::LeanObject,
            3961966953292576997 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__9_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__11_value: leanh::LeanStringObject<
    11,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [118, 105, 115, 105, 98, 105, 108, 105, 116, 121, 0],
};
static mut l_Lean_Option_registerBuiltinOption___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__11_value)
                as *mut leanh::LeanObject,
            18370519569176055110 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__13_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__14_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__15_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__10_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__16_value: leanh::LeanStringObject<
    24,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        114, 101, 103, 105, 115, 116, 101, 114, 95, 98, 117, 105, 108, 116, 105, 110, 95, 111, 112,
        116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Option_registerBuiltinOption___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__17_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__18_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__17_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__19_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Option_registerBuiltinOption___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__20_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__19_value)
                as *mut leanh::LeanObject,
            5117844058249666356 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__21_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__20_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__22_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__18_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__21_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__23_value: leanh::LeanStringObject<
    4,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Option_registerBuiltinOption___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__24_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__23_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__25_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__22_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__24_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__26_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Option_registerBuiltinOption___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__27_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__26_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__28_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__27_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__29_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__25_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__28_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__30_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Option_registerBuiltinOption___closed__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__30_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__31_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__30_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__31: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__31_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__32_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__29_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__31_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__32_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__33_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__32_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__28_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__33_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__34_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__2_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__33_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__34: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__34_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Option_registerBuiltinOption: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__34_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 75, 101, 121, 119, 111, 114, 100, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__5_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [76, 101, 97, 110, 46, 79, 112, 116, 105, 111, 110, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__5_value) as *mut leanh::LeanObject;
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__0_value) as *mut leanh::LeanObject,3127099019797772086 as *mut leanh::LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__9_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7_value) as *mut leanh::LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__10_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__9_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__10_value) as *mut leanh::LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 144, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 111, 83, 101, 113, 73, 110, 100, 101, 110, 116, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 83, 101, 113, 73, 116, 101, 109, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 111, 69, 120, 112, 114, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__16_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [76, 101, 97, 110, 46, 79, 112, 116, 105, 111, 110, 46, 114, 101, 103, 105, 115, 116, 101, 114, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__18_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [114, 101, 103, 105, 115, 116, 101, 114, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__18_value) as *mut leanh::LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__0_value) as *mut leanh::LeanObject,3127099019797772086 as *mut leanh::LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__18_value) as *mut leanh::LeanObject,11387295883396010367 as *mut leanh::LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__20_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__20_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__20_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25_value) as *mut leanh::LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25_value) as *mut leanh::LeanObject,12014440461648055863 as *mut leanh::LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value) as *mut leanh::LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27_value) as *mut leanh::LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27_value) as *mut leanh::LeanObject,14557702332550915328 as *mut leanh::LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value) as *mut leanh::LeanObject;
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Option_registerOption___closed__0_value: leanh::LeanStringObject<15> =
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
            114, 101, 103, 105, 115, 116, 101, 114, 79, 112, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Option_registerOption___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Option_registerOption___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Option_registerOption___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerOption___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__0_value)
                as *mut leanh::LeanObject,
            3127099019797772086 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Option_registerOption___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerOption___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerOption___closed__0_value)
                as *mut leanh::LeanObject,
            3829388930784714694 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerOption___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerOption___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27_value) as *mut leanh::LeanObject,9573766061812123505 as *mut leanh::LeanObject] };
static mut l_Lean_Option_registerOption___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerOption___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerOption___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerOption___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerOption___closed__4_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            114, 101, 103, 105, 115, 116, 101, 114, 95, 111, 112, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Option_registerOption___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerOption___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerOption___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerOption___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerOption___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerOption___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerOption___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerOption___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerOption___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerOption___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__21_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerOption___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerOption___closed__8_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerOption___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__24_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerOption___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerOption___closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerOption___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__28_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerOption___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerOption___closed__10_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerOption___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__31_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerOption___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerOption___closed__11_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerOption___closed__10_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__28_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerOption___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Option_registerOption___closed__12_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerOption___closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerOption___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Option_registerOption___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__12_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Option_registerOption: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__12_value)
        as *mut leanh::LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0_value) as *mut leanh::LeanObject,387456110215466097 as *mut leanh::LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value) as *mut leanh::LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__14_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2_value) as *mut leanh::LeanObject,4498178684837002829 as *mut leanh::LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value) as *mut leanh::LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__14_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value) as *mut leanh::LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__14_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13_value) as *mut leanh::LeanObject,3326968124746134365 as *mut leanh::LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value) as *mut leanh::LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__14_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14_value) as *mut leanh::LeanObject,940684074193935882 as *mut leanh::LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value) as *mut leanh::LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__14_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15_value) as *mut leanh::LeanObject,5573444893818005634 as *mut leanh::LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value) as *mut leanh::LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__14_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22_value) as *mut leanh::LeanObject,9368229134555052249 as *mut leanh::LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value) as *mut leanh::LeanObject;
pub unsafe fn lean_options_get_empty(
    mut v_x_2240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2241_ = l_Lean_Options_empty;
    return v___x_2241_;
}
pub unsafe fn l_Lean_Options_instToString___private__1___lam__0(
    mut v_x1_2243_: *mut leanh::LeanObject,
    mut v_x2_2244_: *mut leanh::LeanObject,
    mut v_x3_2245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2246_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2246_, 0, v_x1_2243_);
    leanh::lean_ctor_set(v___x_2246_, 1, v_x2_2244_);
    v___x_2247_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2247_, 0, v___x_2246_);
    leanh::lean_ctor_set(v___x_2247_, 1, v_x3_2245_);
    return v___x_2247_;
}
pub unsafe fn l_Lean_Options_instToString___private__1(
    mut v_o_2273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2274_ = leanh::lean_ctor_get(v_o_2273_, 0);
    leanh::lean_inc(v_map_2274_);
    leanh::lean_dec_ref(v_o_2273_);
    v___f_2275_ = l_Lean_Options_instToString___private__1___closed__0;
    v___f_2276_ = l_Lean_Options_instToString___private__1___closed__3;
    v___x_2277_ = leanh::lean_box(0);
    v___x_2278_ = l_Lean_Options_instToString___private__1___closed__13;
    v___x_2279_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_2278_,
        v___f_2275_,
        v___x_2277_,
        v_map_2274_,
    );
    v___x_2280_ = l_List_toString___redArg(v___f_2276_, v___x_2279_);
    return v___x_2280_;
}
pub unsafe fn l_Lean_Options_instToString___lam__1(
    mut v___f_2281_: *mut leanh::LeanObject,
    mut v_o_2282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2283_ = leanh::lean_ctor_get(v_o_2282_, 0);
    leanh::lean_inc(v_map_2283_);
    leanh::lean_dec_ref(v_o_2282_);
    v___f_2284_ = l_Lean_Options_instToString___private__1___closed__3;
    v___x_2285_ = leanh::lean_box(0);
    v___x_2286_ = l_Lean_Options_instToString___private__1___closed__13;
    v___x_2287_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_2286_,
        v___f_2281_,
        v___x_2285_,
        v_map_2283_,
    );
    v___x_2288_ = l_List_toString___redArg(v___f_2284_, v___x_2287_);
    return v___x_2288_;
}
pub unsafe fn l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0(
    mut v_f_2292_: *mut leanh::LeanObject,
    mut v_a_2293_: *mut leanh::LeanObject,
    mut v_b_2294_: *mut leanh::LeanObject,
    mut v_c_2295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2296_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2296_, 0, v_a_2293_);
    leanh::lean_ctor_set(v___x_2296_, 1, v_b_2294_);
    v___x_2297_ = leanh::lean_apply_2(v_f_2292_, v___x_2296_, v_c_2295_);
    return v___x_2297_;
}
pub unsafe fn l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1(
    mut v_toPure_2298_: *mut leanh::LeanObject,
    mut v_____do__lift_2299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_2300_ = leanh::lean_ctor_get(v_____do__lift_2299_, 0);
    leanh::lean_inc(v_a_2300_);
    leanh::lean_dec_ref(v_____do__lift_2299_);
    v___x_2301_ = leanh::lean_apply_2(v_toPure_2298_, leanh::lean_box(0), v_a_2300_);
    return v___x_2301_;
}
pub unsafe fn l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg(
    mut v_inst_2302_: *mut leanh::LeanObject,
    mut v_o_2303_: *mut leanh::LeanObject,
    mut v_init_2304_: *mut leanh::LeanObject,
    mut v_f_2305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2306_ = leanh::lean_ctor_get(v_inst_2302_, 0);
    v_map_2307_ = leanh::lean_ctor_get(v_o_2303_, 0);
    leanh::lean_inc(v_map_2307_);
    leanh::lean_dec_ref(v_o_2303_);
    v_toBind_2308_ = leanh::lean_ctor_get(v_inst_2302_, 1);
    leanh::lean_inc(v_toBind_2308_);
    v_toPure_2309_ = leanh::lean_ctor_get(v_toApplicative_2306_, 1);
    leanh::lean_inc(v_toPure_2309_);
    v___f_2310_ = leanh::lean_alloc_closure(
        l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2310_, 0, v_f_2305_);
    v___x_2311_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2302_,
        v___f_2310_,
        v_init_2304_,
        v_map_2307_,
    );
    v___f_2312_ = leanh::lean_alloc_closure(
        l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2312_, 0, v_toPure_2309_);
    v___x_2313_ = leanh::lean_apply_4(
        v_toBind_2308_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2311_,
        v___f_2312_,
    );
    return v___x_2313_;
}
pub unsafe fn l_Lean_Options_instForInProdNameDataValueOfMonad___private__1(
    mut v_m_2314_: *mut leanh::LeanObject,
    mut v_inst_2315_: *mut leanh::LeanObject,
    mut v_00_u03b2_2316_: *mut leanh::LeanObject,
    mut v_o_2317_: *mut leanh::LeanObject,
    mut v_init_2318_: *mut leanh::LeanObject,
    mut v_f_2319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2320_ = leanh::lean_ctor_get(v_inst_2315_, 0);
    v_map_2321_ = leanh::lean_ctor_get(v_o_2317_, 0);
    leanh::lean_inc(v_map_2321_);
    leanh::lean_dec_ref(v_o_2317_);
    v_toBind_2322_ = leanh::lean_ctor_get(v_inst_2315_, 1);
    leanh::lean_inc(v_toBind_2322_);
    v_toPure_2323_ = leanh::lean_ctor_get(v_toApplicative_2320_, 1);
    leanh::lean_inc(v_toPure_2323_);
    v___f_2324_ = leanh::lean_alloc_closure(
        l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2324_, 0, v_f_2319_);
    v___x_2325_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2315_,
        v___f_2324_,
        v_init_2318_,
        v_map_2321_,
    );
    v___f_2326_ = leanh::lean_alloc_closure(
        l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2326_, 0, v_toPure_2323_);
    v___x_2327_ = leanh::lean_apply_4(
        v_toBind_2322_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2325_,
        v___f_2326_,
    );
    return v___x_2327_;
}
pub unsafe fn l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__2(
    mut v_inst_2328_: *mut leanh::LeanObject,
    mut v_00_u03b2_2329_: *mut leanh::LeanObject,
    mut v_o_2330_: *mut leanh::LeanObject,
    mut v_init_2331_: *mut leanh::LeanObject,
    mut v_f_2332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2333_ = leanh::lean_ctor_get(v_inst_2328_, 0);
    v_map_2334_ = leanh::lean_ctor_get(v_o_2330_, 0);
    leanh::lean_inc(v_map_2334_);
    leanh::lean_dec_ref(v_o_2330_);
    v_toBind_2335_ = leanh::lean_ctor_get(v_inst_2328_, 1);
    leanh::lean_inc(v_toBind_2335_);
    v_toPure_2336_ = leanh::lean_ctor_get(v_toApplicative_2333_, 1);
    leanh::lean_inc(v_toPure_2336_);
    v___f_2337_ = leanh::lean_alloc_closure(
        l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2337_, 0, v_f_2332_);
    v___x_2338_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2328_,
        v___f_2337_,
        v_init_2331_,
        v_map_2334_,
    );
    v___f_2339_ = leanh::lean_alloc_closure(
        l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2339_, 0, v_toPure_2336_);
    v___x_2340_ = leanh::lean_apply_4(
        v_toBind_2335_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2338_,
        v___f_2339_,
    );
    return v___x_2340_;
}
pub unsafe fn l_Lean_Options_instForInProdNameDataValueOfMonad___redArg(
    mut v_inst_2341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2342_ = leanh::lean_alloc_closure(
        l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2342_, 0, v_inst_2341_);
    return v___f_2342_;
}
pub unsafe fn l_Lean_Options_instForInProdNameDataValueOfMonad(
    mut v_m_2343_: *mut leanh::LeanObject,
    mut v_inst_2344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2345_ = leanh::lean_alloc_closure(
        l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2345_, 0, v_inst_2344_);
    return v___f_2345_;
}
pub unsafe fn l_Lean_Options_instBEq___private__1(
    mut v_o1_2348_: *mut leanh::LeanObject,
    mut v_o2_2349_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_map_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: u8 = 0;
    v_map_2350_ = leanh::lean_ctor_get(v_o1_2348_, 0);
    leanh::lean_inc(v_map_2350_);
    leanh::lean_dec_ref(v_o1_2348_);
    v_map_2351_ = leanh::lean_ctor_get(v_o2_2349_, 0);
    leanh::lean_inc(v_map_2351_);
    leanh::lean_dec_ref(v_o2_2349_);
    v___x_2352_ = l_Lean_Options_instBEq___private__1___closed__0;
    v___x_2353_ = l_Lean_Options_instBEq___private__1___closed__1;
    v___x_2354_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(
        v___x_2353_,
        v___x_2352_,
        v_map_2350_,
        v_map_2351_,
    );
    return v___x_2354_;
}
pub unsafe fn l_Lean_Options_instBEq___private__1___boxed(
    mut v_o1_2355_: *mut leanh::LeanObject,
    mut v_o2_2356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2357_: u8 = 0;
    let mut v_r_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2357_ = l_Lean_Options_instBEq___private__1(v_o1_2355_, v_o2_2356_);
    v_r_2358_ = leanh::lean_box((v_res_2357_) as usize);
    return v_r_2358_;
}
pub unsafe fn l_Lean_Options_instBEq___lam__0(
    mut v_o1_2359_: *mut leanh::LeanObject,
    mut v_o2_2360_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_map_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: u8 = 0;
    v_map_2361_ = leanh::lean_ctor_get(v_o1_2359_, 0);
    leanh::lean_inc(v_map_2361_);
    leanh::lean_dec_ref(v_o1_2359_);
    v_map_2362_ = leanh::lean_ctor_get(v_o2_2360_, 0);
    leanh::lean_inc(v_map_2362_);
    leanh::lean_dec_ref(v_o2_2360_);
    v___x_2363_ = l_Lean_Options_instBEq___private__1___closed__0;
    v___x_2364_ = l_Lean_Options_instBEq___private__1___closed__1;
    v___x_2365_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(
        v___x_2364_,
        v___x_2363_,
        v_map_2361_,
        v_map_2362_,
    );
    return v___x_2365_;
}
pub unsafe fn l_Lean_Options_instBEq___lam__0___boxed(
    mut v_o1_2366_: *mut leanh::LeanObject,
    mut v_o2_2367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2368_: u8 = 0;
    let mut v_r_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2368_ = l_Lean_Options_instBEq___lam__0(v_o1_2366_, v_o2_2367_);
    v_r_2369_ = leanh::lean_box((v_res_2368_) as usize);
    return v_r_2369_;
}
pub unsafe fn l_Lean_Options_find_x3f(
    mut v_o_2373_: *mut leanh::LeanObject,
    mut v_k_2374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2375_ = leanh::lean_ctor_get(v_o_2373_, 0);
    v___x_2376_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2375_,
            v_k_2374_,
        );
    return v___x_2376_;
}
pub unsafe fn l_Lean_Options_find_x3f___boxed(
    mut v_o_2377_: *mut leanh::LeanObject,
    mut v_k_2378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2379_ = l_Lean_Options_find_x3f(v_o_2377_, v_k_2378_);
    leanh::lean_dec(v_k_2378_);
    leanh::lean_dec_ref(v_o_2377_);
    return v_res_2379_;
}
pub unsafe fn l_Lean_Options_find(
    mut v_o_2380_: *mut leanh::LeanObject,
    mut v_k_2381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2382_ = leanh::lean_ctor_get(v_o_2380_, 0);
    v___x_2383_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2382_,
            v_k_2381_,
        );
    return v___x_2383_;
}
pub unsafe fn l_Lean_Options_find___boxed(
    mut v_o_2384_: *mut leanh::LeanObject,
    mut v_k_2385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2386_ = l_Lean_Options_find(v_o_2384_, v_k_2385_);
    leanh::lean_dec(v_k_2385_);
    leanh::lean_dec_ref(v_o_2384_);
    return v_res_2386_;
}
pub unsafe fn l_Lean_Options_get_x3f___redArg(
    mut v_inst_2387_: *mut leanh::LeanObject,
    mut v_o_2388_: *mut leanh::LeanObject,
    mut v_k_2389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofDataValue_x3f_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2390_ = leanh::lean_ctor_get(v_o_2388_, 0);
    v_ofDataValue_x3f_2391_ = leanh::lean_ctor_get(v_inst_2387_, 1);
    leanh::lean_inc_ref(v_ofDataValue_x3f_2391_);
    leanh::lean_dec_ref(v_inst_2387_);
    v___x_2392_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2390_,
            v_k_2389_,
        );
    if leanh::lean_obj_tag(v___x_2392_) == 0 {
        let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_ofDataValue_x3f_2391_);
        v___x_2393_ = leanh::lean_box(0);
        return v___x_2393_;
    } else {
        let mut v_val_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2394_ = leanh::lean_ctor_get(v___x_2392_, 0);
        leanh::lean_inc(v_val_2394_);
        leanh::lean_dec_ref_known(v___x_2392_, 1);
        v___x_2395_ = leanh::lean_apply_1(v_ofDataValue_x3f_2391_, v_val_2394_);
        return v___x_2395_;
    }
}
pub unsafe fn l_Lean_Options_get_x3f___redArg___boxed(
    mut v_inst_2396_: *mut leanh::LeanObject,
    mut v_o_2397_: *mut leanh::LeanObject,
    mut v_k_2398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2399_ = l_Lean_Options_get_x3f___redArg(v_inst_2396_, v_o_2397_, v_k_2398_);
    leanh::lean_dec(v_k_2398_);
    leanh::lean_dec_ref(v_o_2397_);
    return v_res_2399_;
}
pub unsafe fn l_Lean_Options_get_x3f(
    mut v_00_u03b1_2400_: *mut leanh::LeanObject,
    mut v_inst_2401_: *mut leanh::LeanObject,
    mut v_o_2402_: *mut leanh::LeanObject,
    mut v_k_2403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofDataValue_x3f_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2404_ = leanh::lean_ctor_get(v_o_2402_, 0);
    v_ofDataValue_x3f_2405_ = leanh::lean_ctor_get(v_inst_2401_, 1);
    leanh::lean_inc_ref(v_ofDataValue_x3f_2405_);
    leanh::lean_dec_ref(v_inst_2401_);
    v___x_2406_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2404_,
            v_k_2403_,
        );
    if leanh::lean_obj_tag(v___x_2406_) == 0 {
        let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_ofDataValue_x3f_2405_);
        v___x_2407_ = leanh::lean_box(0);
        return v___x_2407_;
    } else {
        let mut v_val_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2408_ = leanh::lean_ctor_get(v___x_2406_, 0);
        leanh::lean_inc(v_val_2408_);
        leanh::lean_dec_ref_known(v___x_2406_, 1);
        v___x_2409_ = leanh::lean_apply_1(v_ofDataValue_x3f_2405_, v_val_2408_);
        return v___x_2409_;
    }
}
pub unsafe fn l_Lean_Options_get_x3f___boxed(
    mut v_00_u03b1_2410_: *mut leanh::LeanObject,
    mut v_inst_2411_: *mut leanh::LeanObject,
    mut v_o_2412_: *mut leanh::LeanObject,
    mut v_k_2413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2414_ = l_Lean_Options_get_x3f(v_00_u03b1_2410_, v_inst_2411_, v_o_2412_, v_k_2413_);
    leanh::lean_dec(v_k_2413_);
    leanh::lean_dec_ref(v_o_2412_);
    return v_res_2414_;
}
pub unsafe fn l_Lean_Options_get___redArg(
    mut v_inst_2415_: *mut leanh::LeanObject,
    mut v_o_2416_: *mut leanh::LeanObject,
    mut v_k_2417_: *mut leanh::LeanObject,
    mut v_defVal_2418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofDataValue_x3f_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2419_ = leanh::lean_ctor_get(v_o_2416_, 0);
    v_ofDataValue_x3f_2420_ = leanh::lean_ctor_get(v_inst_2415_, 1);
    leanh::lean_inc_ref(v_ofDataValue_x3f_2420_);
    leanh::lean_dec_ref(v_inst_2415_);
    v___x_2421_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2419_,
            v_k_2417_,
        );
    if leanh::lean_obj_tag(v___x_2421_) == 0 {
        leanh::lean_dec_ref(v_ofDataValue_x3f_2420_);
        leanh::lean_inc(v_defVal_2418_);
        return v_defVal_2418_;
    } else {
        let mut v_val_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2422_ = leanh::lean_ctor_get(v___x_2421_, 0);
        leanh::lean_inc(v_val_2422_);
        leanh::lean_dec_ref_known(v___x_2421_, 1);
        v___x_2423_ = leanh::lean_apply_1(v_ofDataValue_x3f_2420_, v_val_2422_);
        if leanh::lean_obj_tag(v___x_2423_) == 0 {
            leanh::lean_inc(v_defVal_2418_);
            return v_defVal_2418_;
        } else {
            let mut v_val_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_2424_ = leanh::lean_ctor_get(v___x_2423_, 0);
            leanh::lean_inc(v_val_2424_);
            leanh::lean_dec_ref_known(v___x_2423_, 1);
            return v_val_2424_;
        }
    }
}
pub unsafe fn l_Lean_Options_get___redArg___boxed(
    mut v_inst_2425_: *mut leanh::LeanObject,
    mut v_o_2426_: *mut leanh::LeanObject,
    mut v_k_2427_: *mut leanh::LeanObject,
    mut v_defVal_2428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2429_ = l_Lean_Options_get___redArg(v_inst_2425_, v_o_2426_, v_k_2427_, v_defVal_2428_);
    leanh::lean_dec(v_defVal_2428_);
    leanh::lean_dec(v_k_2427_);
    leanh::lean_dec_ref(v_o_2426_);
    return v_res_2429_;
}
pub unsafe fn l_Lean_Options_get(
    mut v_00_u03b1_2430_: *mut leanh::LeanObject,
    mut v_inst_2431_: *mut leanh::LeanObject,
    mut v_o_2432_: *mut leanh::LeanObject,
    mut v_k_2433_: *mut leanh::LeanObject,
    mut v_defVal_2434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofDataValue_x3f_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2435_ = leanh::lean_ctor_get(v_o_2432_, 0);
    v_ofDataValue_x3f_2436_ = leanh::lean_ctor_get(v_inst_2431_, 1);
    leanh::lean_inc_ref(v_ofDataValue_x3f_2436_);
    leanh::lean_dec_ref(v_inst_2431_);
    v___x_2437_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2435_,
            v_k_2433_,
        );
    if leanh::lean_obj_tag(v___x_2437_) == 0 {
        leanh::lean_dec_ref(v_ofDataValue_x3f_2436_);
        leanh::lean_inc(v_defVal_2434_);
        return v_defVal_2434_;
    } else {
        let mut v_val_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2438_ = leanh::lean_ctor_get(v___x_2437_, 0);
        leanh::lean_inc(v_val_2438_);
        leanh::lean_dec_ref_known(v___x_2437_, 1);
        v___x_2439_ = leanh::lean_apply_1(v_ofDataValue_x3f_2436_, v_val_2438_);
        if leanh::lean_obj_tag(v___x_2439_) == 0 {
            leanh::lean_inc(v_defVal_2434_);
            return v_defVal_2434_;
        } else {
            let mut v_val_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_2440_ = leanh::lean_ctor_get(v___x_2439_, 0);
            leanh::lean_inc(v_val_2440_);
            leanh::lean_dec_ref_known(v___x_2439_, 1);
            return v_val_2440_;
        }
    }
}
pub unsafe fn l_Lean_Options_get___boxed(
    mut v_00_u03b1_2441_: *mut leanh::LeanObject,
    mut v_inst_2442_: *mut leanh::LeanObject,
    mut v_o_2443_: *mut leanh::LeanObject,
    mut v_k_2444_: *mut leanh::LeanObject,
    mut v_defVal_2445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2446_ = l_Lean_Options_get(
        v_00_u03b1_2441_,
        v_inst_2442_,
        v_o_2443_,
        v_k_2444_,
        v_defVal_2445_,
    );
    leanh::lean_dec(v_defVal_2445_);
    leanh::lean_dec(v_k_2444_);
    leanh::lean_dec_ref(v_o_2443_);
    return v_res_2446_;
}
pub unsafe fn l_Lean_Options_getBool(
    mut v_o_2447_: *mut leanh::LeanObject,
    mut v_k_2448_: *mut leanh::LeanObject,
    mut v_defVal_2449_: u8,
) -> u8 {
    let mut v_map_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2450_ = leanh::lean_ctor_get(v_o_2447_, 0);
    v___x_2451_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2450_,
            v_k_2448_,
        );
    if leanh::lean_obj_tag(v___x_2451_) == 0 {
        return v_defVal_2449_;
    } else {
        let mut v_val_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2452_ = leanh::lean_ctor_get(v___x_2451_, 0);
        leanh::lean_inc(v_val_2452_);
        leanh::lean_dec_ref_known(v___x_2451_, 1);
        if leanh::lean_obj_tag(v_val_2452_) == 1 {
            let mut v_v_2453_: u8 = 0;
            v_v_2453_ = leanh::lean_ctor_get_uint8(v_val_2452_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_2452_, 0);
            return v_v_2453_;
        } else {
            leanh::lean_dec(v_val_2452_);
            return v_defVal_2449_;
        }
    }
}
pub unsafe fn l_Lean_Options_getBool___boxed(
    mut v_o_2454_: *mut leanh::LeanObject,
    mut v_k_2455_: *mut leanh::LeanObject,
    mut v_defVal_2456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defVal_boxed_2457_: u8 = 0;
    let mut v_res_2458_: u8 = 0;
    let mut v_r_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_defVal_boxed_2457_ = (leanh::lean_unbox(v_defVal_2456_) as u8);
    v_res_2458_ = l_Lean_Options_getBool(v_o_2454_, v_k_2455_, v_defVal_boxed_2457_);
    leanh::lean_dec(v_k_2455_);
    leanh::lean_dec_ref(v_o_2454_);
    v_r_2459_ = leanh::lean_box((v_res_2458_) as usize);
    return v_r_2459_;
}
pub unsafe fn l_Lean_Options_contains(
    mut v_o_2460_: *mut leanh::LeanObject,
    mut v_k_2461_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_map_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: u8 = 0;
    v_map_2462_ = leanh::lean_ctor_get(v_o_2460_, 0);
    v___x_2463_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(
            v_k_2461_,
            v_map_2462_,
        );
    return v___x_2463_;
}
pub unsafe fn l_Lean_Options_contains___boxed(
    mut v_o_2464_: *mut leanh::LeanObject,
    mut v_k_2465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2466_: u8 = 0;
    let mut v_r_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2466_ = l_Lean_Options_contains(v_o_2464_, v_k_2465_);
    leanh::lean_dec(v_k_2465_);
    leanh::lean_dec_ref(v_o_2464_);
    v_r_2467_ = leanh::lean_box((v_res_2466_) as usize);
    return v_r_2467_;
}
pub unsafe fn l_Lean_Options_insert(
    mut v_o_2471_: *mut leanh::LeanObject,
    mut v_k_2472_: *mut leanh::LeanObject,
    mut v_v_2473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2475_: u8 = 0;
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2478_: u8 = 0;
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: u8 = 0;
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_2474_ = leanh::lean_ctor_get(v_o_2471_, 0);
                v_hasTrace_2475_ = leanh::lean_ctor_get_uint8(
                    v_o_2471_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2488_ = (!leanh::lean_is_exclusive(v_o_2471_)) as u8;
                if v_isSharedCheck_2488_ == 0 {
                    v___x_2477_ = v_o_2471_;
                    v_isShared_2478_ = v_isSharedCheck_2488_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_2474_);
                    leanh::lean_dec(v_o_2471_);
                    v___x_2477_ = leanh::lean_box(0);
                    v_isShared_2478_ = v_isSharedCheck_2488_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_k_2472_);
                v___x_2479_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2472_, v_v_2473_, v_map_2474_);
                if v_hasTrace_2475_ == 0 {
                    v___x_2480_ = l_Lean_Options_insert___closed__1;
                    v___x_2481_ = l_Lean_Name_isPrefixOf(v___x_2480_, v_k_2472_);
                    leanh::lean_dec(v_k_2472_);
                    if v_isShared_2478_ == 0 {
                        leanh::lean_ctor_set(v___x_2477_, 0, v___x_2479_);
                        v___x_2483_ = v___x_2477_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2484_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2479_);
                        v___x_2483_ = v_reuseFailAlloc_2484_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_2472_);
                    if v_isShared_2478_ == 0 {
                        leanh::lean_ctor_set(v___x_2477_, 0, v___x_2479_);
                        v___x_2486_ = v___x_2477_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2487_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2479_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2487_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_2475_,
                        );
                        v___x_2486_ = v_reuseFailAlloc_2487_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2483_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2481_,
                );
                return v___x_2483_;
            }
            3 => {
                return v___x_2486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___redArg(
    mut v_inst_2489_: *mut leanh::LeanObject,
    mut v_o_2490_: *mut leanh::LeanObject,
    mut v_k_2491_: *mut leanh::LeanObject,
    mut v_v_2492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toDataValue_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2495_: u8 = 0;
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2498_: u8 = 0;
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: u8 = 0;
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2509_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toDataValue_2493_ = leanh::lean_ctor_get(v_inst_2489_, 0);
                leanh::lean_inc_ref(v_toDataValue_2493_);
                leanh::lean_dec_ref(v_inst_2489_);
                v_map_2494_ = leanh::lean_ctor_get(v_o_2490_, 0);
                v_hasTrace_2495_ = leanh::lean_ctor_get_uint8(
                    v_o_2490_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2509_ = (!leanh::lean_is_exclusive(v_o_2490_)) as u8;
                if v_isSharedCheck_2509_ == 0 {
                    v___x_2497_ = v_o_2490_;
                    v_isShared_2498_ = v_isSharedCheck_2509_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_2494_);
                    leanh::lean_dec(v_o_2490_);
                    v___x_2497_ = leanh::lean_box(0);
                    v_isShared_2498_ = v_isSharedCheck_2509_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2499_ = leanh::lean_apply_1(v_toDataValue_2493_, v_v_2492_);
                leanh::lean_inc(v_k_2491_);
                v___x_2500_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2491_, v___x_2499_, v_map_2494_);
                if v_hasTrace_2495_ == 0 {
                    v___x_2501_ = l_Lean_Options_insert___closed__1;
                    v___x_2502_ = l_Lean_Name_isPrefixOf(v___x_2501_, v_k_2491_);
                    leanh::lean_dec(v_k_2491_);
                    if v_isShared_2498_ == 0 {
                        leanh::lean_ctor_set(v___x_2497_, 0, v___x_2500_);
                        v___x_2504_ = v___x_2497_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2505_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2500_);
                        v___x_2504_ = v_reuseFailAlloc_2505_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_2491_);
                    if v_isShared_2498_ == 0 {
                        leanh::lean_ctor_set(v___x_2497_, 0, v___x_2500_);
                        v___x_2507_ = v___x_2497_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2508_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2500_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2508_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_2495_,
                        );
                        v___x_2507_ = v_reuseFailAlloc_2508_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2504_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2502_,
                );
                return v___x_2504_;
            }
            3 => {
                return v___x_2507_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set(
    mut v_00_u03b1_2510_: *mut leanh::LeanObject,
    mut v_inst_2511_: *mut leanh::LeanObject,
    mut v_o_2512_: *mut leanh::LeanObject,
    mut v_k_2513_: *mut leanh::LeanObject,
    mut v_v_2514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2515_ = l_Lean_Options_set___redArg(v_inst_2511_, v_o_2512_, v_k_2513_, v_v_2514_);
    return v___x_2515_;
}
pub unsafe fn l_Lean_Options_setBool(
    mut v_o_2516_: *mut leanh::LeanObject,
    mut v_k_2517_: *mut leanh::LeanObject,
    mut v_v_2518_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2519_ = l_Lean_KVMap_instValueBool;
    v___x_2520_ = leanh::lean_box((v_v_2518_) as usize);
    v___x_2521_ = l_Lean_Options_set___redArg(v___x_2519_, v_o_2516_, v_k_2517_, v___x_2520_);
    return v___x_2521_;
}
pub unsafe fn l_Lean_Options_setBool___boxed(
    mut v_o_2522_: *mut leanh::LeanObject,
    mut v_k_2523_: *mut leanh::LeanObject,
    mut v_v_2524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_2525_: u8 = 0;
    let mut v_res_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_2525_ = (leanh::lean_unbox(v_v_2524_) as u8);
    v_res_2526_ = l_Lean_Options_setBool(v_o_2522_, v_k_2523_, v_v_boxed_2525_);
    return v_res_2526_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(
    mut v_init_2527_: *mut leanh::LeanObject,
    mut v_x_2528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2528_) == 0 {
                    v_k_2529_ = leanh::lean_ctor_get(v_x_2528_, 1);
                    v_l_2530_ = leanh::lean_ctor_get(v_x_2528_, 3);
                    v_r_2531_ = leanh::lean_ctor_get(v_x_2528_, 4);
                    v___x_2532_ =
                        l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(
                            v_init_2527_,
                            v_r_2531_,
                        );
                    leanh::lean_inc(v_k_2529_);
                    v___x_2533_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2533_, 0, v_k_2529_);
                    leanh::lean_ctor_set(v___x_2533_, 1, v___x_2532_);
                    v_init_2527_ = v___x_2533_;
                    v_x_2528_ = v_l_2530_;
                    state = 0;
                    continue;
                } else {
                    return v_init_2527_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1___boxed(
    mut v_init_2535_: *mut leanh::LeanObject,
    mut v_x_2536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2537_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(
        v_init_2535_,
        v_x_2536_,
    );
    leanh::lean_dec(v_x_2536_);
    return v_res_2537_;
}
pub unsafe fn l_List_any___at___00Lean_Options_erase_spec__2(
    mut v_x_2538_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2539_: u8 = 0;
    let mut v_head_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2538_) == 0 {
                    v___x_2539_ = 0;
                    return v___x_2539_;
                } else {
                    v_head_2540_ = leanh::lean_ctor_get(v_x_2538_, 0);
                    v_tail_2541_ = leanh::lean_ctor_get(v_x_2538_, 1);
                    v___x_2542_ = l_Lean_Options_insert___closed__1;
                    v___x_2543_ = l_Lean_Name_isPrefixOf(v___x_2542_, v_head_2540_);
                    if v___x_2543_ == 0 {
                        v_x_2538_ = v_tail_2541_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2543_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Options_erase_spec__2___boxed(
    mut v_x_2545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2546_: u8 = 0;
    let mut v_r_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2546_ = l_List_any___at___00Lean_Options_erase_spec__2(v_x_2545_);
    leanh::lean_dec(v_x_2545_);
    v_r_2547_ = leanh::lean_box((v_res_2546_) as usize);
    return v_r_2547_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(
    mut v_k_2548_: *mut leanh::LeanObject,
    mut v_t_2549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2556_: u8 = 0;
    let mut v___x_2557_: u8 = 0;
    let mut v_impl_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: u8 = 0;
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2576_: u8 = 0;
    let mut v_size_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: u8 = 0;
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2588_: u8 = 0;
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2613_: u8 = 0;
    let mut v_unused_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2626_: u8 = 0;
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2630_: u8 = 0;
    let mut v_unused_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2637_: u8 = 0;
    let mut v_unused_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2655_: u8 = 0;
    let mut v_size_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2665_: u8 = 0;
    let mut v_unused_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2672_: u8 = 0;
    let mut v_k_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2677_: u8 = 0;
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2688_: u8 = 0;
    let mut v_unused_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2692_: u8 = 0;
    let mut v_unused_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2701_: u8 = 0;
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2709_: u8 = 0;
    let mut v_unused_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2718_: u8 = 0;
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2726_: u8 = 0;
    let mut v_unused_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: u8 = 0;
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2746_: u8 = 0;
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: u8 = 0;
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2762_: u8 = 0;
    let mut v_size_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: u8 = 0;
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2774_: u8 = 0;
    let mut v___x_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2799_: u8 = 0;
    let mut v_unused_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2814_: u8 = 0;
    let mut v_unused_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v_k_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2840_: u8 = 0;
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2851_: u8 = 0;
    let mut v_unused_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2873_: u8 = 0;
    let mut v_unused_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2879_: u8 = 0;
    let mut v_unused_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2887_: u8 = 0;
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: u8 = 0;
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2903_: u8 = 0;
    let mut v_size_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: u8 = 0;
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2915_: u8 = 0;
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2927_: u8 = 0;
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2931_: u8 = 0;
    let mut v_unused_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2950_: u8 = 0;
    let mut v_unused_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2966_: u8 = 0;
    let mut v_unused_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2974_: u8 = 0;
    let mut v_k_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2995_: u8 = 0;
    let mut v_unused_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3003_: u8 = 0;
    let mut v_k_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3010_: u8 = 0;
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3021_: u8 = 0;
    let mut v_unused_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3025_: u8 = 0;
    let mut v_unused_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v_unused_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: u8 = 0;
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3061_: u8 = 0;
    let mut v_size_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: u8 = 0;
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3073_: u8 = 0;
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3099_: u8 = 0;
    let mut v_unused_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3113_: u8 = 0;
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3117_: u8 = 0;
    let mut v_unused_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v_unused_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3142_: u8 = 0;
    let mut v_size_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3152_: u8 = 0;
    let mut v_unused_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3159_: u8 = 0;
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3167_: u8 = 0;
    let mut v_unused_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3176_: u8 = 0;
    let mut v_k_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3181_: u8 = 0;
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3192_: u8 = 0;
    let mut v_unused_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3196_: u8 = 0;
    let mut v_unused_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3207_: u8 = 0;
    let mut v_unused_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_2549_) == 0 {
                    v_k_2550_ = leanh::lean_ctor_get(v_t_2549_, 1);
                    v_v_2551_ = leanh::lean_ctor_get(v_t_2549_, 2);
                    v_l_2552_ = leanh::lean_ctor_get(v_t_2549_, 3);
                    v_r_2553_ = leanh::lean_ctor_get(v_t_2549_, 4);
                    v_isSharedCheck_3207_ = (!leanh::lean_is_exclusive(v_t_2549_)) as u8;
                    if v_isSharedCheck_3207_ == 0 {
                        v_unused_3208_ = leanh::lean_ctor_get(v_t_2549_, 0);
                        leanh::lean_dec(v_unused_3208_);
                        v___x_2555_ = v_t_2549_;
                        v_isShared_2556_ = v_isSharedCheck_3207_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_2553_);
                        leanh::lean_inc(v_l_2552_);
                        leanh::lean_inc(v_v_2551_);
                        leanh::lean_inc(v_k_2550_);
                        leanh::lean_dec(v_t_2549_);
                        v___x_2555_ = leanh::lean_box(0);
                        v_isShared_2556_ = v_isSharedCheck_3207_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_t_2549_;
                }
            }
            1 => {
                v___x_2557_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2548_, v_k_2550_);
                match v___x_2557_ {
                    0 => {
                        v_impl_2558_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_2548_, v_l_2552_);
                        v___x_2559_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_impl_2558_) == 0 {
                            if leanh::lean_obj_tag(v_r_2553_) == 0 {
                                v_size_2560_ = leanh::lean_ctor_get(v_impl_2558_, 0);
                                leanh::lean_inc(v_size_2560_);
                                v_size_2561_ = leanh::lean_ctor_get(v_r_2553_, 0);
                                v_k_2562_ = leanh::lean_ctor_get(v_r_2553_, 1);
                                v_v_2563_ = leanh::lean_ctor_get(v_r_2553_, 2);
                                v_l_2564_ = leanh::lean_ctor_get(v_r_2553_, 3);
                                leanh::lean_inc(v_l_2564_);
                                v_r_2565_ = leanh::lean_ctor_get(v_r_2553_, 4);
                                v___x_2566_ = leanh::lean_unsigned_to_nat(3);
                                v___x_2567_ = lean_nat_mul(v___x_2566_, v_size_2560_);
                                v___x_2568_ = lean_nat_dec_lt(v___x_2567_, v_size_2561_);
                                leanh::lean_dec(v___x_2567_);
                                if v___x_2568_ == 0 {
                                    leanh::lean_dec(v_l_2564_);
                                    v___x_2569_ = lean_nat_add(v___x_2559_, v_size_2560_);
                                    leanh::lean_dec(v_size_2560_);
                                    v___x_2570_ = lean_nat_add(v___x_2569_, v_size_2561_);
                                    leanh::lean_dec(v___x_2569_);
                                    if v_isShared_2556_ == 0 {
                                        leanh::lean_ctor_set(v___x_2555_, 3, v_impl_2558_);
                                        leanh::lean_ctor_set(v___x_2555_, 0, v___x_2570_);
                                        v___x_2572_ = v___x_2555_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2573_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2573_,
                                            0,
                                            v___x_2570_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2573_,
                                            1,
                                            v_k_2550_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2573_,
                                            2,
                                            v_v_2551_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2573_,
                                            3,
                                            v_impl_2558_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2573_,
                                            4,
                                            v_r_2553_,
                                        );
                                        v___x_2572_ = v_reuseFailAlloc_2573_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc(v_r_2565_);
                                    leanh::lean_inc(v_v_2563_);
                                    leanh::lean_inc(v_k_2562_);
                                    leanh::lean_inc(v_size_2561_);
                                    v_isSharedCheck_2637_ =
                                        (!leanh::lean_is_exclusive(v_r_2553_)) as u8;
                                    if v_isSharedCheck_2637_ == 0 {
                                        v_unused_2638_ = leanh::lean_ctor_get(v_r_2553_, 4);
                                        leanh::lean_dec(v_unused_2638_);
                                        v_unused_2639_ = leanh::lean_ctor_get(v_r_2553_, 3);
                                        leanh::lean_dec(v_unused_2639_);
                                        v_unused_2640_ = leanh::lean_ctor_get(v_r_2553_, 2);
                                        leanh::lean_dec(v_unused_2640_);
                                        v_unused_2641_ = leanh::lean_ctor_get(v_r_2553_, 1);
                                        leanh::lean_dec(v_unused_2641_);
                                        v_unused_2642_ = leanh::lean_ctor_get(v_r_2553_, 0);
                                        leanh::lean_dec(v_unused_2642_);
                                        v___x_2575_ = v_r_2553_;
                                        v_isShared_2576_ = v_isSharedCheck_2637_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_r_2553_);
                                        v___x_2575_ = leanh::lean_box(0);
                                        v_isShared_2576_ = v_isSharedCheck_2637_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_2643_ = leanh::lean_ctor_get(v_impl_2558_, 0);
                                leanh::lean_inc(v_size_2643_);
                                v___x_2644_ = lean_nat_add(v___x_2559_, v_size_2643_);
                                leanh::lean_dec(v_size_2643_);
                                if v_isShared_2556_ == 0 {
                                    leanh::lean_ctor_set(v___x_2555_, 3, v_impl_2558_);
                                    leanh::lean_ctor_set(v___x_2555_, 0, v___x_2644_);
                                    v___x_2646_ = v___x_2555_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2647_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2647_,
                                        0,
                                        v___x_2644_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2647_,
                                        1,
                                        v_k_2550_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2647_,
                                        2,
                                        v_v_2551_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2647_,
                                        3,
                                        v_impl_2558_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2647_,
                                        4,
                                        v_r_2553_,
                                    );
                                    v___x_2646_ = v_reuseFailAlloc_2647_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if leanh::lean_obj_tag(v_r_2553_) == 0 {
                                v_l_2648_ = leanh::lean_ctor_get(v_r_2553_, 3);
                                leanh::lean_inc(v_l_2648_);
                                if leanh::lean_obj_tag(v_l_2648_) == 0 {
                                    v_r_2649_ = leanh::lean_ctor_get(v_r_2553_, 4);
                                    leanh::lean_inc(v_r_2649_);
                                    if leanh::lean_obj_tag(v_r_2649_) == 0 {
                                        v_size_2650_ = leanh::lean_ctor_get(v_r_2553_, 0);
                                        v_k_2651_ = leanh::lean_ctor_get(v_r_2553_, 1);
                                        v_v_2652_ = leanh::lean_ctor_get(v_r_2553_, 2);
                                        v_isSharedCheck_2665_ =
                                            (!leanh::lean_is_exclusive(v_r_2553_)) as u8;
                                        if v_isSharedCheck_2665_ == 0 {
                                            v_unused_2666_ =
                                                leanh::lean_ctor_get(v_r_2553_, 4);
                                            leanh::lean_dec(v_unused_2666_);
                                            v_unused_2667_ =
                                                leanh::lean_ctor_get(v_r_2553_, 3);
                                            leanh::lean_dec(v_unused_2667_);
                                            v___x_2654_ = v_r_2553_;
                                            v_isShared_2655_ = v_isSharedCheck_2665_;
                                            state = 14;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_2652_);
                                            leanh::lean_inc(v_k_2651_);
                                            leanh::lean_inc(v_size_2650_);
                                            leanh::lean_dec(v_r_2553_);
                                            v___x_2654_ = leanh::lean_box(0);
                                            v_isShared_2655_ = v_isSharedCheck_2665_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_2668_ = leanh::lean_ctor_get(v_r_2553_, 1);
                                        v_v_2669_ = leanh::lean_ctor_get(v_r_2553_, 2);
                                        v_isSharedCheck_2692_ =
                                            (!leanh::lean_is_exclusive(v_r_2553_)) as u8;
                                        if v_isSharedCheck_2692_ == 0 {
                                            v_unused_2693_ =
                                                leanh::lean_ctor_get(v_r_2553_, 4);
                                            leanh::lean_dec(v_unused_2693_);
                                            v_unused_2694_ =
                                                leanh::lean_ctor_get(v_r_2553_, 3);
                                            leanh::lean_dec(v_unused_2694_);
                                            v_unused_2695_ =
                                                leanh::lean_ctor_get(v_r_2553_, 0);
                                            leanh::lean_dec(v_unused_2695_);
                                            v___x_2671_ = v_r_2553_;
                                            v_isShared_2672_ = v_isSharedCheck_2692_;
                                            state = 17;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_2669_);
                                            leanh::lean_inc(v_k_2668_);
                                            leanh::lean_dec(v_r_2553_);
                                            v___x_2671_ = leanh::lean_box(0);
                                            v_isShared_2672_ = v_isSharedCheck_2692_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_2696_ = leanh::lean_ctor_get(v_r_2553_, 4);
                                    leanh::lean_inc(v_r_2696_);
                                    if leanh::lean_obj_tag(v_r_2696_) == 0 {
                                        v_k_2697_ = leanh::lean_ctor_get(v_r_2553_, 1);
                                        v_v_2698_ = leanh::lean_ctor_get(v_r_2553_, 2);
                                        v_isSharedCheck_2709_ =
                                            (!leanh::lean_is_exclusive(v_r_2553_)) as u8;
                                        if v_isSharedCheck_2709_ == 0 {
                                            v_unused_2710_ =
                                                leanh::lean_ctor_get(v_r_2553_, 4);
                                            leanh::lean_dec(v_unused_2710_);
                                            v_unused_2711_ =
                                                leanh::lean_ctor_get(v_r_2553_, 3);
                                            leanh::lean_dec(v_unused_2711_);
                                            v_unused_2712_ =
                                                leanh::lean_ctor_get(v_r_2553_, 0);
                                            leanh::lean_dec(v_unused_2712_);
                                            v___x_2700_ = v_r_2553_;
                                            v_isShared_2701_ = v_isSharedCheck_2709_;
                                            state = 22;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_2698_);
                                            leanh::lean_inc(v_k_2697_);
                                            leanh::lean_dec(v_r_2553_);
                                            v___x_2700_ = leanh::lean_box(0);
                                            v_isShared_2701_ = v_isSharedCheck_2709_;
                                            state = 22;
                                            continue;
                                        }
                                    } else {
                                        v_size_2713_ = leanh::lean_ctor_get(v_r_2553_, 0);
                                        v_k_2714_ = leanh::lean_ctor_get(v_r_2553_, 1);
                                        v_v_2715_ = leanh::lean_ctor_get(v_r_2553_, 2);
                                        v_isSharedCheck_2726_ =
                                            (!leanh::lean_is_exclusive(v_r_2553_)) as u8;
                                        if v_isSharedCheck_2726_ == 0 {
                                            v_unused_2727_ =
                                                leanh::lean_ctor_get(v_r_2553_, 4);
                                            leanh::lean_dec(v_unused_2727_);
                                            v_unused_2728_ =
                                                leanh::lean_ctor_get(v_r_2553_, 3);
                                            leanh::lean_dec(v_unused_2728_);
                                            v___x_2717_ = v_r_2553_;
                                            v_isShared_2718_ = v_isSharedCheck_2726_;
                                            state = 25;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_2715_);
                                            leanh::lean_inc(v_k_2714_);
                                            leanh::lean_inc(v_size_2713_);
                                            leanh::lean_dec(v_r_2553_);
                                            v___x_2717_ = leanh::lean_box(0);
                                            v_isShared_2718_ = v_isSharedCheck_2726_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_2556_ == 0 {
                                    leanh::lean_ctor_set(v___x_2555_, 3, v_r_2553_);
                                    leanh::lean_ctor_set(v___x_2555_, 0, v___x_2559_);
                                    v___x_2730_ = v___x_2555_;
                                    state = 28;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2731_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2731_,
                                        0,
                                        v___x_2559_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2731_,
                                        1,
                                        v_k_2550_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2731_,
                                        2,
                                        v_v_2551_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2731_,
                                        3,
                                        v_r_2553_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2731_,
                                        4,
                                        v_r_2553_,
                                    );
                                    v___x_2730_ = v_reuseFailAlloc_2731_;
                                    state = 28;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        leanh::lean_del_object(v___x_2555_);
                        leanh::lean_dec(v_v_2551_);
                        leanh::lean_dec(v_k_2550_);
                        if leanh::lean_obj_tag(v_l_2552_) == 0 {
                            if leanh::lean_obj_tag(v_r_2553_) == 0 {
                                v_size_2732_ = leanh::lean_ctor_get(v_l_2552_, 0);
                                v_k_2733_ = leanh::lean_ctor_get(v_l_2552_, 1);
                                v_v_2734_ = leanh::lean_ctor_get(v_l_2552_, 2);
                                v_l_2735_ = leanh::lean_ctor_get(v_l_2552_, 3);
                                v_r_2736_ = leanh::lean_ctor_get(v_l_2552_, 4);
                                leanh::lean_inc(v_r_2736_);
                                v_size_2737_ = leanh::lean_ctor_get(v_r_2553_, 0);
                                v_k_2738_ = leanh::lean_ctor_get(v_r_2553_, 1);
                                v_v_2739_ = leanh::lean_ctor_get(v_r_2553_, 2);
                                v_l_2740_ = leanh::lean_ctor_get(v_r_2553_, 3);
                                leanh::lean_inc(v_l_2740_);
                                v_r_2741_ = leanh::lean_ctor_get(v_r_2553_, 4);
                                v___x_2742_ = leanh::lean_unsigned_to_nat(1);
                                v___x_2743_ = lean_nat_dec_lt(v_size_2732_, v_size_2737_);
                                if v___x_2743_ == 0 {
                                    leanh::lean_inc(v_l_2735_);
                                    leanh::lean_inc(v_v_2734_);
                                    leanh::lean_inc(v_k_2733_);
                                    v_isSharedCheck_2879_ =
                                        (!leanh::lean_is_exclusive(v_l_2552_)) as u8;
                                    if v_isSharedCheck_2879_ == 0 {
                                        v_unused_2880_ = leanh::lean_ctor_get(v_l_2552_, 4);
                                        leanh::lean_dec(v_unused_2880_);
                                        v_unused_2881_ = leanh::lean_ctor_get(v_l_2552_, 3);
                                        leanh::lean_dec(v_unused_2881_);
                                        v_unused_2882_ = leanh::lean_ctor_get(v_l_2552_, 2);
                                        leanh::lean_dec(v_unused_2882_);
                                        v_unused_2883_ = leanh::lean_ctor_get(v_l_2552_, 1);
                                        leanh::lean_dec(v_unused_2883_);
                                        v_unused_2884_ = leanh::lean_ctor_get(v_l_2552_, 0);
                                        leanh::lean_dec(v_unused_2884_);
                                        v___x_2745_ = v_l_2552_;
                                        v_isShared_2746_ = v_isSharedCheck_2879_;
                                        state = 29;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_l_2552_);
                                        v___x_2745_ = leanh::lean_box(0);
                                        v_isShared_2746_ = v_isSharedCheck_2879_;
                                        state = 29;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc(v_r_2741_);
                                    leanh::lean_inc(v_v_2739_);
                                    leanh::lean_inc(v_k_2738_);
                                    v_isSharedCheck_3037_ =
                                        (!leanh::lean_is_exclusive(v_r_2553_)) as u8;
                                    if v_isSharedCheck_3037_ == 0 {
                                        v_unused_3038_ = leanh::lean_ctor_get(v_r_2553_, 4);
                                        leanh::lean_dec(v_unused_3038_);
                                        v_unused_3039_ = leanh::lean_ctor_get(v_r_2553_, 3);
                                        leanh::lean_dec(v_unused_3039_);
                                        v_unused_3040_ = leanh::lean_ctor_get(v_r_2553_, 2);
                                        leanh::lean_dec(v_unused_3040_);
                                        v_unused_3041_ = leanh::lean_ctor_get(v_r_2553_, 1);
                                        leanh::lean_dec(v_unused_3041_);
                                        v_unused_3042_ = leanh::lean_ctor_get(v_r_2553_, 0);
                                        leanh::lean_dec(v_unused_3042_);
                                        v___x_2886_ = v_r_2553_;
                                        v_isShared_2887_ = v_isSharedCheck_3037_;
                                        state = 51;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_r_2553_);
                                        v___x_2886_ = leanh::lean_box(0);
                                        v_isShared_2887_ = v_isSharedCheck_3037_;
                                        state = 51;
                                        continue;
                                    }
                                }
                            } else {
                                return v_l_2552_;
                            }
                        } else {
                            return v_r_2553_;
                        }
                    }
                    _ => {
                        v_impl_3043_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_2548_, v_r_2553_);
                        v___x_3044_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_impl_3043_) == 0 {
                            if leanh::lean_obj_tag(v_l_2552_) == 0 {
                                v_size_3045_ = leanh::lean_ctor_get(v_impl_3043_, 0);
                                leanh::lean_inc(v_size_3045_);
                                v_size_3046_ = leanh::lean_ctor_get(v_l_2552_, 0);
                                v_k_3047_ = leanh::lean_ctor_get(v_l_2552_, 1);
                                v_v_3048_ = leanh::lean_ctor_get(v_l_2552_, 2);
                                v_l_3049_ = leanh::lean_ctor_get(v_l_2552_, 3);
                                v_r_3050_ = leanh::lean_ctor_get(v_l_2552_, 4);
                                leanh::lean_inc(v_r_3050_);
                                v___x_3051_ = leanh::lean_unsigned_to_nat(3);
                                v___x_3052_ = lean_nat_mul(v___x_3051_, v_size_3045_);
                                v___x_3053_ = lean_nat_dec_lt(v___x_3052_, v_size_3046_);
                                leanh::lean_dec(v___x_3052_);
                                if v___x_3053_ == 0 {
                                    leanh::lean_dec(v_r_3050_);
                                    v___x_3054_ = lean_nat_add(v___x_3044_, v_size_3046_);
                                    v___x_3055_ = lean_nat_add(v___x_3054_, v_size_3045_);
                                    leanh::lean_dec(v_size_3045_);
                                    leanh::lean_dec(v___x_3054_);
                                    if v_isShared_2556_ == 0 {
                                        leanh::lean_ctor_set(v___x_2555_, 4, v_impl_3043_);
                                        leanh::lean_ctor_set(v___x_2555_, 0, v___x_3055_);
                                        v___x_3057_ = v___x_2555_;
                                        state = 74;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3058_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3058_,
                                            0,
                                            v___x_3055_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3058_,
                                            1,
                                            v_k_2550_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3058_,
                                            2,
                                            v_v_2551_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3058_,
                                            3,
                                            v_l_2552_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3058_,
                                            4,
                                            v_impl_3043_,
                                        );
                                        v___x_3057_ = v_reuseFailAlloc_3058_;
                                        state = 74;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc(v_l_3049_);
                                    leanh::lean_inc(v_v_3048_);
                                    leanh::lean_inc(v_k_3047_);
                                    leanh::lean_inc(v_size_3046_);
                                    v_isSharedCheck_3124_ =
                                        (!leanh::lean_is_exclusive(v_l_2552_)) as u8;
                                    if v_isSharedCheck_3124_ == 0 {
                                        v_unused_3125_ = leanh::lean_ctor_get(v_l_2552_, 4);
                                        leanh::lean_dec(v_unused_3125_);
                                        v_unused_3126_ = leanh::lean_ctor_get(v_l_2552_, 3);
                                        leanh::lean_dec(v_unused_3126_);
                                        v_unused_3127_ = leanh::lean_ctor_get(v_l_2552_, 2);
                                        leanh::lean_dec(v_unused_3127_);
                                        v_unused_3128_ = leanh::lean_ctor_get(v_l_2552_, 1);
                                        leanh::lean_dec(v_unused_3128_);
                                        v_unused_3129_ = leanh::lean_ctor_get(v_l_2552_, 0);
                                        leanh::lean_dec(v_unused_3129_);
                                        v___x_3060_ = v_l_2552_;
                                        v_isShared_3061_ = v_isSharedCheck_3124_;
                                        state = 75;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_l_2552_);
                                        v___x_3060_ = leanh::lean_box(0);
                                        v_isShared_3061_ = v_isSharedCheck_3124_;
                                        state = 75;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_3130_ = leanh::lean_ctor_get(v_impl_3043_, 0);
                                leanh::lean_inc(v_size_3130_);
                                v___x_3131_ = lean_nat_add(v___x_3044_, v_size_3130_);
                                leanh::lean_dec(v_size_3130_);
                                if v_isShared_2556_ == 0 {
                                    leanh::lean_ctor_set(v___x_2555_, 4, v_impl_3043_);
                                    leanh::lean_ctor_set(v___x_2555_, 0, v___x_3131_);
                                    v___x_3133_ = v___x_2555_;
                                    state = 85;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3134_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3134_,
                                        0,
                                        v___x_3131_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3134_,
                                        1,
                                        v_k_2550_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3134_,
                                        2,
                                        v_v_2551_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3134_,
                                        3,
                                        v_l_2552_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3134_,
                                        4,
                                        v_impl_3043_,
                                    );
                                    v___x_3133_ = v_reuseFailAlloc_3134_;
                                    state = 85;
                                    continue;
                                }
                            }
                        } else {
                            if leanh::lean_obj_tag(v_l_2552_) == 0 {
                                v_l_3135_ = leanh::lean_ctor_get(v_l_2552_, 3);
                                if leanh::lean_obj_tag(v_l_3135_) == 0 {
                                    leanh::lean_inc_ref(v_l_3135_);
                                    v_r_3136_ = leanh::lean_ctor_get(v_l_2552_, 4);
                                    leanh::lean_inc(v_r_3136_);
                                    if leanh::lean_obj_tag(v_r_3136_) == 0 {
                                        v_size_3137_ = leanh::lean_ctor_get(v_l_2552_, 0);
                                        v_k_3138_ = leanh::lean_ctor_get(v_l_2552_, 1);
                                        v_v_3139_ = leanh::lean_ctor_get(v_l_2552_, 2);
                                        v_isSharedCheck_3152_ =
                                            (!leanh::lean_is_exclusive(v_l_2552_)) as u8;
                                        if v_isSharedCheck_3152_ == 0 {
                                            v_unused_3153_ =
                                                leanh::lean_ctor_get(v_l_2552_, 4);
                                            leanh::lean_dec(v_unused_3153_);
                                            v_unused_3154_ =
                                                leanh::lean_ctor_get(v_l_2552_, 3);
                                            leanh::lean_dec(v_unused_3154_);
                                            v___x_3141_ = v_l_2552_;
                                            v_isShared_3142_ = v_isSharedCheck_3152_;
                                            state = 86;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_3139_);
                                            leanh::lean_inc(v_k_3138_);
                                            leanh::lean_inc(v_size_3137_);
                                            leanh::lean_dec(v_l_2552_);
                                            v___x_3141_ = leanh::lean_box(0);
                                            v_isShared_3142_ = v_isSharedCheck_3152_;
                                            state = 86;
                                            continue;
                                        }
                                    } else {
                                        v_k_3155_ = leanh::lean_ctor_get(v_l_2552_, 1);
                                        v_v_3156_ = leanh::lean_ctor_get(v_l_2552_, 2);
                                        v_isSharedCheck_3167_ =
                                            (!leanh::lean_is_exclusive(v_l_2552_)) as u8;
                                        if v_isSharedCheck_3167_ == 0 {
                                            v_unused_3168_ =
                                                leanh::lean_ctor_get(v_l_2552_, 4);
                                            leanh::lean_dec(v_unused_3168_);
                                            v_unused_3169_ =
                                                leanh::lean_ctor_get(v_l_2552_, 3);
                                            leanh::lean_dec(v_unused_3169_);
                                            v_unused_3170_ =
                                                leanh::lean_ctor_get(v_l_2552_, 0);
                                            leanh::lean_dec(v_unused_3170_);
                                            v___x_3158_ = v_l_2552_;
                                            v_isShared_3159_ = v_isSharedCheck_3167_;
                                            state = 89;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_3156_);
                                            leanh::lean_inc(v_k_3155_);
                                            leanh::lean_dec(v_l_2552_);
                                            v___x_3158_ = leanh::lean_box(0);
                                            v_isShared_3159_ = v_isSharedCheck_3167_;
                                            state = 89;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_3171_ = leanh::lean_ctor_get(v_l_2552_, 4);
                                    leanh::lean_inc(v_r_3171_);
                                    if leanh::lean_obj_tag(v_r_3171_) == 0 {
                                        leanh::lean_inc(v_l_3135_);
                                        v_k_3172_ = leanh::lean_ctor_get(v_l_2552_, 1);
                                        v_v_3173_ = leanh::lean_ctor_get(v_l_2552_, 2);
                                        v_isSharedCheck_3196_ =
                                            (!leanh::lean_is_exclusive(v_l_2552_)) as u8;
                                        if v_isSharedCheck_3196_ == 0 {
                                            v_unused_3197_ =
                                                leanh::lean_ctor_get(v_l_2552_, 4);
                                            leanh::lean_dec(v_unused_3197_);
                                            v_unused_3198_ =
                                                leanh::lean_ctor_get(v_l_2552_, 3);
                                            leanh::lean_dec(v_unused_3198_);
                                            v_unused_3199_ =
                                                leanh::lean_ctor_get(v_l_2552_, 0);
                                            leanh::lean_dec(v_unused_3199_);
                                            v___x_3175_ = v_l_2552_;
                                            v_isShared_3176_ = v_isSharedCheck_3196_;
                                            state = 92;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_3173_);
                                            leanh::lean_inc(v_k_3172_);
                                            leanh::lean_dec(v_l_2552_);
                                            v___x_3175_ = leanh::lean_box(0);
                                            v_isShared_3176_ = v_isSharedCheck_3196_;
                                            state = 92;
                                            continue;
                                        }
                                    } else {
                                        v___x_3200_ = leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_2556_ == 0 {
                                            leanh::lean_ctor_set(v___x_2555_, 4, v_r_3171_);
                                            leanh::lean_ctor_set(
                                                v___x_2555_,
                                                0,
                                                v___x_3200_,
                                            );
                                            v___x_3202_ = v___x_2555_;
                                            state = 97;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3203_ =
                                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3203_,
                                                0,
                                                v___x_3200_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3203_,
                                                1,
                                                v_k_2550_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3203_,
                                                2,
                                                v_v_2551_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3203_,
                                                3,
                                                v_l_2552_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3203_,
                                                4,
                                                v_r_3171_,
                                            );
                                            v___x_3202_ = v_reuseFailAlloc_3203_;
                                            state = 97;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_2556_ == 0 {
                                    leanh::lean_ctor_set(v___x_2555_, 4, v_l_2552_);
                                    leanh::lean_ctor_set(v___x_2555_, 0, v___x_3044_);
                                    v___x_3205_ = v___x_2555_;
                                    state = 98;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3206_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3206_,
                                        0,
                                        v___x_3044_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3206_,
                                        1,
                                        v_k_2550_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3206_,
                                        2,
                                        v_v_2551_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3206_,
                                        3,
                                        v_l_2552_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3206_,
                                        4,
                                        v_l_2552_,
                                    );
                                    v___x_3205_ = v_reuseFailAlloc_3206_;
                                    state = 98;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_2572_;
            }
            3 => {
                v_size_2577_ = leanh::lean_ctor_get(v_l_2564_, 0);
                v_k_2578_ = leanh::lean_ctor_get(v_l_2564_, 1);
                v_v_2579_ = leanh::lean_ctor_get(v_l_2564_, 2);
                v_l_2580_ = leanh::lean_ctor_get(v_l_2564_, 3);
                v_r_2581_ = leanh::lean_ctor_get(v_l_2564_, 4);
                v_size_2582_ = leanh::lean_ctor_get(v_r_2565_, 0);
                v___x_2583_ = leanh::lean_unsigned_to_nat(2);
                v___x_2584_ = lean_nat_mul(v___x_2583_, v_size_2582_);
                v___x_2585_ = lean_nat_dec_lt(v_size_2577_, v___x_2584_);
                leanh::lean_dec(v___x_2584_);
                if v___x_2585_ == 0 {
                    leanh::lean_inc(v_r_2581_);
                    leanh::lean_inc(v_l_2580_);
                    leanh::lean_inc(v_v_2579_);
                    leanh::lean_inc(v_k_2578_);
                    v_isSharedCheck_2613_ = (!leanh::lean_is_exclusive(v_l_2564_)) as u8;
                    if v_isSharedCheck_2613_ == 0 {
                        v_unused_2614_ = leanh::lean_ctor_get(v_l_2564_, 4);
                        leanh::lean_dec(v_unused_2614_);
                        v_unused_2615_ = leanh::lean_ctor_get(v_l_2564_, 3);
                        leanh::lean_dec(v_unused_2615_);
                        v_unused_2616_ = leanh::lean_ctor_get(v_l_2564_, 2);
                        leanh::lean_dec(v_unused_2616_);
                        v_unused_2617_ = leanh::lean_ctor_get(v_l_2564_, 1);
                        leanh::lean_dec(v_unused_2617_);
                        v_unused_2618_ = leanh::lean_ctor_get(v_l_2564_, 0);
                        leanh::lean_dec(v_unused_2618_);
                        v___x_2587_ = v_l_2564_;
                        v_isShared_2588_ = v_isSharedCheck_2613_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_2564_);
                        v___x_2587_ = leanh::lean_box(0);
                        v_isShared_2588_ = v_isSharedCheck_2613_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2555_);
                    v___x_2619_ = lean_nat_add(v___x_2559_, v_size_2560_);
                    leanh::lean_dec(v_size_2560_);
                    v___x_2620_ = lean_nat_add(v___x_2619_, v_size_2561_);
                    leanh::lean_dec(v_size_2561_);
                    v___x_2621_ = lean_nat_add(v___x_2619_, v_size_2577_);
                    leanh::lean_dec(v___x_2619_);
                    leanh::lean_inc_ref(v_impl_2558_);
                    if v_isShared_2576_ == 0 {
                        leanh::lean_ctor_set(v___x_2575_, 4, v_l_2564_);
                        leanh::lean_ctor_set(v___x_2575_, 3, v_impl_2558_);
                        leanh::lean_ctor_set(v___x_2575_, 2, v_v_2551_);
                        leanh::lean_ctor_set(v___x_2575_, 1, v_k_2550_);
                        leanh::lean_ctor_set(v___x_2575_, 0, v___x_2621_);
                        v___x_2623_ = v___x_2575_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2636_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2621_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_k_2550_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2636_, 2, v_v_2551_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2636_, 3, v_impl_2558_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2636_, 4, v_l_2564_);
                        v___x_2623_ = v_reuseFailAlloc_2636_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2589_ = lean_nat_add(v___x_2559_, v_size_2560_);
                leanh::lean_dec(v_size_2560_);
                v___x_2590_ = lean_nat_add(v___x_2589_, v_size_2561_);
                leanh::lean_dec(v_size_2561_);
                if leanh::lean_obj_tag(v_l_2580_) == 0 {
                    v_size_2611_ = leanh::lean_ctor_get(v_l_2580_, 0);
                    leanh::lean_inc(v_size_2611_);
                    v___y_2603_ = v_size_2611_;
                    state = 8;
                    continue;
                } else {
                    v___x_2612_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2603_ = v___x_2612_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2595_ = lean_nat_add(v___y_2592_, v___y_2594_);
                leanh::lean_dec(v___y_2594_);
                leanh::lean_dec(v___y_2592_);
                if v_isShared_2588_ == 0 {
                    leanh::lean_ctor_set(v___x_2587_, 4, v_r_2565_);
                    leanh::lean_ctor_set(v___x_2587_, 3, v_r_2581_);
                    leanh::lean_ctor_set(v___x_2587_, 2, v_v_2563_);
                    leanh::lean_ctor_set(v___x_2587_, 1, v_k_2562_);
                    leanh::lean_ctor_set(v___x_2587_, 0, v___x_2595_);
                    v___x_2597_ = v___x_2587_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2601_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2595_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_k_2562_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2601_, 2, v_v_2563_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2601_, 3, v_r_2581_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2601_, 4, v_r_2565_);
                    v___x_2597_ = v_reuseFailAlloc_2601_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2576_ == 0 {
                    leanh::lean_ctor_set(v___x_2575_, 4, v___x_2597_);
                    leanh::lean_ctor_set(v___x_2575_, 3, v___y_2593_);
                    leanh::lean_ctor_set(v___x_2575_, 2, v_v_2579_);
                    leanh::lean_ctor_set(v___x_2575_, 1, v_k_2578_);
                    leanh::lean_ctor_set(v___x_2575_, 0, v___x_2590_);
                    v___x_2599_ = v___x_2575_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2600_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2590_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2600_, 1, v_k_2578_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2600_, 2, v_v_2579_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2600_, 3, v___y_2593_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2600_, 4, v___x_2597_);
                    v___x_2599_ = v_reuseFailAlloc_2600_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2599_;
            }
            8 => {
                v___x_2604_ = lean_nat_add(v___x_2589_, v___y_2603_);
                leanh::lean_dec(v___y_2603_);
                leanh::lean_dec(v___x_2589_);
                if v_isShared_2556_ == 0 {
                    leanh::lean_ctor_set(v___x_2555_, 4, v_l_2580_);
                    leanh::lean_ctor_set(v___x_2555_, 3, v_impl_2558_);
                    leanh::lean_ctor_set(v___x_2555_, 0, v___x_2604_);
                    v___x_2606_ = v___x_2555_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2610_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2604_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_k_2550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 2, v_v_2551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 3, v_impl_2558_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 4, v_l_2580_);
                    v___x_2606_ = v_reuseFailAlloc_2610_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2607_ = lean_nat_add(v___x_2559_, v_size_2582_);
                if leanh::lean_obj_tag(v_r_2581_) == 0 {
                    v_size_2608_ = leanh::lean_ctor_get(v_r_2581_, 0);
                    leanh::lean_inc(v_size_2608_);
                    v___y_2592_ = v___x_2607_;
                    v___y_2593_ = v___x_2606_;
                    v___y_2594_ = v_size_2608_;
                    state = 5;
                    continue;
                } else {
                    v___x_2609_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2592_ = v___x_2607_;
                    v___y_2593_ = v___x_2606_;
                    v___y_2594_ = v___x_2609_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2630_ = (!leanh::lean_is_exclusive(v_impl_2558_)) as u8;
                if v_isSharedCheck_2630_ == 0 {
                    v_unused_2631_ = leanh::lean_ctor_get(v_impl_2558_, 4);
                    leanh::lean_dec(v_unused_2631_);
                    v_unused_2632_ = leanh::lean_ctor_get(v_impl_2558_, 3);
                    leanh::lean_dec(v_unused_2632_);
                    v_unused_2633_ = leanh::lean_ctor_get(v_impl_2558_, 2);
                    leanh::lean_dec(v_unused_2633_);
                    v_unused_2634_ = leanh::lean_ctor_get(v_impl_2558_, 1);
                    leanh::lean_dec(v_unused_2634_);
                    v_unused_2635_ = leanh::lean_ctor_get(v_impl_2558_, 0);
                    leanh::lean_dec(v_unused_2635_);
                    v___x_2625_ = v_impl_2558_;
                    v_isShared_2626_ = v_isSharedCheck_2630_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_impl_2558_);
                    v___x_2625_ = leanh::lean_box(0);
                    v_isShared_2626_ = v_isSharedCheck_2630_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2626_ == 0 {
                    leanh::lean_ctor_set(v___x_2625_, 4, v_r_2565_);
                    leanh::lean_ctor_set(v___x_2625_, 3, v___x_2623_);
                    leanh::lean_ctor_set(v___x_2625_, 2, v_v_2563_);
                    leanh::lean_ctor_set(v___x_2625_, 1, v_k_2562_);
                    leanh::lean_ctor_set(v___x_2625_, 0, v___x_2620_);
                    v___x_2628_ = v___x_2625_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2629_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2620_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_k_2562_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2629_, 2, v_v_2563_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2629_, 3, v___x_2623_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2629_, 4, v_r_2565_);
                    v___x_2628_ = v_reuseFailAlloc_2629_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2628_;
            }
            13 => {
                return v___x_2646_;
            }
            14 => {
                v_size_2656_ = leanh::lean_ctor_get(v_l_2648_, 0);
                v___x_2657_ = lean_nat_add(v___x_2559_, v_size_2650_);
                leanh::lean_dec(v_size_2650_);
                v___x_2658_ = lean_nat_add(v___x_2559_, v_size_2656_);
                if v_isShared_2655_ == 0 {
                    leanh::lean_ctor_set(v___x_2654_, 4, v_l_2648_);
                    leanh::lean_ctor_set(v___x_2654_, 3, v_impl_2558_);
                    leanh::lean_ctor_set(v___x_2654_, 2, v_v_2551_);
                    leanh::lean_ctor_set(v___x_2654_, 1, v_k_2550_);
                    leanh::lean_ctor_set(v___x_2654_, 0, v___x_2658_);
                    v___x_2660_ = v___x_2654_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2664_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2658_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 1, v_k_2550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 2, v_v_2551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 3, v_impl_2558_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 4, v_l_2648_);
                    v___x_2660_ = v_reuseFailAlloc_2664_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_2556_ == 0 {
                    leanh::lean_ctor_set(v___x_2555_, 4, v_r_2649_);
                    leanh::lean_ctor_set(v___x_2555_, 3, v___x_2660_);
                    leanh::lean_ctor_set(v___x_2555_, 2, v_v_2652_);
                    leanh::lean_ctor_set(v___x_2555_, 1, v_k_2651_);
                    leanh::lean_ctor_set(v___x_2555_, 0, v___x_2657_);
                    v___x_2662_ = v___x_2555_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2663_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2657_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_k_2651_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2663_, 2, v_v_2652_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2663_, 3, v___x_2660_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2663_, 4, v_r_2649_);
                    v___x_2662_ = v_reuseFailAlloc_2663_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2662_;
            }
            17 => {
                v_k_2673_ = leanh::lean_ctor_get(v_l_2648_, 1);
                v_v_2674_ = leanh::lean_ctor_get(v_l_2648_, 2);
                v_isSharedCheck_2688_ = (!leanh::lean_is_exclusive(v_l_2648_)) as u8;
                if v_isSharedCheck_2688_ == 0 {
                    v_unused_2689_ = leanh::lean_ctor_get(v_l_2648_, 4);
                    leanh::lean_dec(v_unused_2689_);
                    v_unused_2690_ = leanh::lean_ctor_get(v_l_2648_, 3);
                    leanh::lean_dec(v_unused_2690_);
                    v_unused_2691_ = leanh::lean_ctor_get(v_l_2648_, 0);
                    leanh::lean_dec(v_unused_2691_);
                    v___x_2676_ = v_l_2648_;
                    v_isShared_2677_ = v_isSharedCheck_2688_;
                    state = 18;
                    continue;
                } else {
                    leanh::lean_inc(v_v_2674_);
                    leanh::lean_inc(v_k_2673_);
                    leanh::lean_dec(v_l_2648_);
                    v___x_2676_ = leanh::lean_box(0);
                    v_isShared_2677_ = v_isSharedCheck_2688_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_2678_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_2677_ == 0 {
                    leanh::lean_ctor_set(v___x_2676_, 4, v_r_2649_);
                    leanh::lean_ctor_set(v___x_2676_, 3, v_r_2649_);
                    leanh::lean_ctor_set(v___x_2676_, 2, v_v_2551_);
                    leanh::lean_ctor_set(v___x_2676_, 1, v_k_2550_);
                    leanh::lean_ctor_set(v___x_2676_, 0, v___x_2559_);
                    v___x_2680_ = v___x_2676_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2687_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2559_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_k_2550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 2, v_v_2551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 3, v_r_2649_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 4, v_r_2649_);
                    v___x_2680_ = v_reuseFailAlloc_2687_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2672_ == 0 {
                    leanh::lean_ctor_set(v___x_2671_, 3, v_r_2649_);
                    leanh::lean_ctor_set(v___x_2671_, 0, v___x_2559_);
                    v___x_2682_ = v___x_2671_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2686_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2559_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2686_, 1, v_k_2668_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2686_, 2, v_v_2669_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2686_, 3, v_r_2649_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2686_, 4, v_r_2649_);
                    v___x_2682_ = v_reuseFailAlloc_2686_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_2556_ == 0 {
                    leanh::lean_ctor_set(v___x_2555_, 4, v___x_2682_);
                    leanh::lean_ctor_set(v___x_2555_, 3, v___x_2680_);
                    leanh::lean_ctor_set(v___x_2555_, 2, v_v_2674_);
                    leanh::lean_ctor_set(v___x_2555_, 1, v_k_2673_);
                    leanh::lean_ctor_set(v___x_2555_, 0, v___x_2678_);
                    v___x_2684_ = v___x_2555_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2685_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2678_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_k_2673_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2685_, 2, v_v_2674_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2685_, 3, v___x_2680_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2685_, 4, v___x_2682_);
                    v___x_2684_ = v_reuseFailAlloc_2685_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2684_;
            }
            22 => {
                v___x_2702_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_2701_ == 0 {
                    leanh::lean_ctor_set(v___x_2700_, 4, v_l_2648_);
                    leanh::lean_ctor_set(v___x_2700_, 2, v_v_2551_);
                    leanh::lean_ctor_set(v___x_2700_, 1, v_k_2550_);
                    leanh::lean_ctor_set(v___x_2700_, 0, v___x_2559_);
                    v___x_2704_ = v___x_2700_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2708_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2559_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_k_2550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2708_, 2, v_v_2551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2708_, 3, v_l_2648_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2708_, 4, v_l_2648_);
                    v___x_2704_ = v_reuseFailAlloc_2708_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_2556_ == 0 {
                    leanh::lean_ctor_set(v___x_2555_, 4, v_r_2696_);
                    leanh::lean_ctor_set(v___x_2555_, 3, v___x_2704_);
                    leanh::lean_ctor_set(v___x_2555_, 2, v_v_2698_);
                    leanh::lean_ctor_set(v___x_2555_, 1, v_k_2697_);
                    leanh::lean_ctor_set(v___x_2555_, 0, v___x_2702_);
                    v___x_2706_ = v___x_2555_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2707_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_k_2697_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 2, v_v_2698_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 3, v___x_2704_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 4, v_r_2696_);
                    v___x_2706_ = v_reuseFailAlloc_2707_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2706_;
            }
            25 => {
                if v_isShared_2718_ == 0 {
                    leanh::lean_ctor_set(v___x_2717_, 3, v_r_2696_);
                    v___x_2720_ = v___x_2717_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2725_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_size_2713_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_k_2714_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 2, v_v_2715_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 3, v_r_2696_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 4, v_r_2696_);
                    v___x_2720_ = v_reuseFailAlloc_2725_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_2721_ = leanh::lean_unsigned_to_nat(2);
                if v_isShared_2556_ == 0 {
                    leanh::lean_ctor_set(v___x_2555_, 4, v___x_2720_);
                    leanh::lean_ctor_set(v___x_2555_, 3, v_r_2696_);
                    leanh::lean_ctor_set(v___x_2555_, 0, v___x_2721_);
                    v___x_2723_ = v___x_2555_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2724_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2721_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_k_2550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2724_, 2, v_v_2551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2724_, 3, v_r_2696_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2724_, 4, v___x_2720_);
                    v___x_2723_ = v_reuseFailAlloc_2724_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_2723_;
            }
            28 => {
                return v___x_2730_;
            }
            29 => {
                v___x_2747_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(
                    v_k_2733_, v_v_2734_, v_l_2735_, v_r_2736_,
                );
                v_tree_2748_ = leanh::lean_ctor_get(v___x_2747_, 2);
                leanh::lean_inc(v_tree_2748_);
                if leanh::lean_obj_tag(v_tree_2748_) == 0 {
                    v_k_2749_ = leanh::lean_ctor_get(v___x_2747_, 0);
                    leanh::lean_inc(v_k_2749_);
                    v_v_2750_ = leanh::lean_ctor_get(v___x_2747_, 1);
                    leanh::lean_inc(v_v_2750_);
                    leanh::lean_dec_ref(v___x_2747_);
                    v_size_2751_ = leanh::lean_ctor_get(v_tree_2748_, 0);
                    v___x_2752_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2753_ = lean_nat_mul(v___x_2752_, v_size_2751_);
                    v___x_2754_ = lean_nat_dec_lt(v___x_2753_, v_size_2737_);
                    leanh::lean_dec(v___x_2753_);
                    if v___x_2754_ == 0 {
                        leanh::lean_dec(v_l_2740_);
                        v___x_2755_ = lean_nat_add(v___x_2742_, v_size_2751_);
                        v___x_2756_ = lean_nat_add(v___x_2755_, v_size_2737_);
                        leanh::lean_dec(v___x_2755_);
                        if v_isShared_2746_ == 0 {
                            leanh::lean_ctor_set(v___x_2745_, 4, v_r_2553_);
                            leanh::lean_ctor_set(v___x_2745_, 3, v_tree_2748_);
                            leanh::lean_ctor_set(v___x_2745_, 2, v_v_2750_);
                            leanh::lean_ctor_set(v___x_2745_, 1, v_k_2749_);
                            leanh::lean_ctor_set(v___x_2745_, 0, v___x_2756_);
                            v___x_2758_ = v___x_2745_;
                            state = 30;
                            continue;
                        } else {
                            v_reuseFailAlloc_2759_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2756_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2759_, 1, v_k_2749_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2759_, 2, v_v_2750_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2759_, 3, v_tree_2748_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2759_, 4, v_r_2553_);
                            v___x_2758_ = v_reuseFailAlloc_2759_;
                            state = 30;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_r_2741_);
                        leanh::lean_inc(v_v_2739_);
                        leanh::lean_inc(v_k_2738_);
                        leanh::lean_inc(v_size_2737_);
                        v_isSharedCheck_2814_ = (!leanh::lean_is_exclusive(v_r_2553_)) as u8;
                        if v_isSharedCheck_2814_ == 0 {
                            v_unused_2815_ = leanh::lean_ctor_get(v_r_2553_, 4);
                            leanh::lean_dec(v_unused_2815_);
                            v_unused_2816_ = leanh::lean_ctor_get(v_r_2553_, 3);
                            leanh::lean_dec(v_unused_2816_);
                            v_unused_2817_ = leanh::lean_ctor_get(v_r_2553_, 2);
                            leanh::lean_dec(v_unused_2817_);
                            v_unused_2818_ = leanh::lean_ctor_get(v_r_2553_, 1);
                            leanh::lean_dec(v_unused_2818_);
                            v_unused_2819_ = leanh::lean_ctor_get(v_r_2553_, 0);
                            leanh::lean_dec(v_unused_2819_);
                            v___x_2761_ = v_r_2553_;
                            v_isShared_2762_ = v_isSharedCheck_2814_;
                            state = 31;
                            continue;
                        } else {
                            leanh::lean_dec(v_r_2553_);
                            v___x_2761_ = leanh::lean_box(0);
                            v_isShared_2762_ = v_isSharedCheck_2814_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_r_2741_);
                    leanh::lean_inc(v_v_2739_);
                    leanh::lean_inc(v_k_2738_);
                    leanh::lean_inc(v_size_2737_);
                    v_isSharedCheck_2873_ = (!leanh::lean_is_exclusive(v_r_2553_)) as u8;
                    if v_isSharedCheck_2873_ == 0 {
                        v_unused_2874_ = leanh::lean_ctor_get(v_r_2553_, 4);
                        leanh::lean_dec(v_unused_2874_);
                        v_unused_2875_ = leanh::lean_ctor_get(v_r_2553_, 3);
                        leanh::lean_dec(v_unused_2875_);
                        v_unused_2876_ = leanh::lean_ctor_get(v_r_2553_, 2);
                        leanh::lean_dec(v_unused_2876_);
                        v_unused_2877_ = leanh::lean_ctor_get(v_r_2553_, 1);
                        leanh::lean_dec(v_unused_2877_);
                        v_unused_2878_ = leanh::lean_ctor_get(v_r_2553_, 0);
                        leanh::lean_dec(v_unused_2878_);
                        v___x_2821_ = v_r_2553_;
                        v_isShared_2822_ = v_isSharedCheck_2873_;
                        state = 40;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_2553_);
                        v___x_2821_ = leanh::lean_box(0);
                        v_isShared_2822_ = v_isSharedCheck_2873_;
                        state = 40;
                        continue;
                    }
                }
            }
            30 => {
                return v___x_2758_;
            }
            31 => {
                v_size_2763_ = leanh::lean_ctor_get(v_l_2740_, 0);
                v_k_2764_ = leanh::lean_ctor_get(v_l_2740_, 1);
                v_v_2765_ = leanh::lean_ctor_get(v_l_2740_, 2);
                v_l_2766_ = leanh::lean_ctor_get(v_l_2740_, 3);
                v_r_2767_ = leanh::lean_ctor_get(v_l_2740_, 4);
                v_size_2768_ = leanh::lean_ctor_get(v_r_2741_, 0);
                v___x_2769_ = leanh::lean_unsigned_to_nat(2);
                v___x_2770_ = lean_nat_mul(v___x_2769_, v_size_2768_);
                v___x_2771_ = lean_nat_dec_lt(v_size_2763_, v___x_2770_);
                leanh::lean_dec(v___x_2770_);
                if v___x_2771_ == 0 {
                    leanh::lean_inc(v_r_2767_);
                    leanh::lean_inc(v_l_2766_);
                    leanh::lean_inc(v_v_2765_);
                    leanh::lean_inc(v_k_2764_);
                    v_isSharedCheck_2799_ = (!leanh::lean_is_exclusive(v_l_2740_)) as u8;
                    if v_isSharedCheck_2799_ == 0 {
                        v_unused_2800_ = leanh::lean_ctor_get(v_l_2740_, 4);
                        leanh::lean_dec(v_unused_2800_);
                        v_unused_2801_ = leanh::lean_ctor_get(v_l_2740_, 3);
                        leanh::lean_dec(v_unused_2801_);
                        v_unused_2802_ = leanh::lean_ctor_get(v_l_2740_, 2);
                        leanh::lean_dec(v_unused_2802_);
                        v_unused_2803_ = leanh::lean_ctor_get(v_l_2740_, 1);
                        leanh::lean_dec(v_unused_2803_);
                        v_unused_2804_ = leanh::lean_ctor_get(v_l_2740_, 0);
                        leanh::lean_dec(v_unused_2804_);
                        v___x_2773_ = v_l_2740_;
                        v_isShared_2774_ = v_isSharedCheck_2799_;
                        state = 32;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_2740_);
                        v___x_2773_ = leanh::lean_box(0);
                        v_isShared_2774_ = v_isSharedCheck_2799_;
                        state = 32;
                        continue;
                    }
                } else {
                    v___x_2805_ = lean_nat_add(v___x_2742_, v_size_2751_);
                    v___x_2806_ = lean_nat_add(v___x_2805_, v_size_2737_);
                    leanh::lean_dec(v_size_2737_);
                    v___x_2807_ = lean_nat_add(v___x_2805_, v_size_2763_);
                    leanh::lean_dec(v___x_2805_);
                    if v_isShared_2762_ == 0 {
                        leanh::lean_ctor_set(v___x_2761_, 4, v_l_2740_);
                        leanh::lean_ctor_set(v___x_2761_, 3, v_tree_2748_);
                        leanh::lean_ctor_set(v___x_2761_, 2, v_v_2750_);
                        leanh::lean_ctor_set(v___x_2761_, 1, v_k_2749_);
                        leanh::lean_ctor_set(v___x_2761_, 0, v___x_2807_);
                        v___x_2809_ = v___x_2761_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_2813_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2807_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_k_2749_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 2, v_v_2750_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 3, v_tree_2748_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 4, v_l_2740_);
                        v___x_2809_ = v_reuseFailAlloc_2813_;
                        state = 38;
                        continue;
                    }
                }
            }
            32 => {
                v___x_2775_ = lean_nat_add(v___x_2742_, v_size_2751_);
                v___x_2776_ = lean_nat_add(v___x_2775_, v_size_2737_);
                leanh::lean_dec(v_size_2737_);
                if leanh::lean_obj_tag(v_l_2766_) == 0 {
                    v_size_2797_ = leanh::lean_ctor_get(v_l_2766_, 0);
                    leanh::lean_inc(v_size_2797_);
                    v___y_2789_ = v_size_2797_;
                    state = 36;
                    continue;
                } else {
                    v___x_2798_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2789_ = v___x_2798_;
                    state = 36;
                    continue;
                }
            }
            33 => {
                v___x_2781_ = lean_nat_add(v___y_2778_, v___y_2780_);
                leanh::lean_dec(v___y_2780_);
                leanh::lean_dec(v___y_2778_);
                if v_isShared_2774_ == 0 {
                    leanh::lean_ctor_set(v___x_2773_, 4, v_r_2741_);
                    leanh::lean_ctor_set(v___x_2773_, 3, v_r_2767_);
                    leanh::lean_ctor_set(v___x_2773_, 2, v_v_2739_);
                    leanh::lean_ctor_set(v___x_2773_, 1, v_k_2738_);
                    leanh::lean_ctor_set(v___x_2773_, 0, v___x_2781_);
                    v___x_2783_ = v___x_2773_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2787_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2781_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2787_, 1, v_k_2738_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2787_, 2, v_v_2739_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2787_, 3, v_r_2767_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2787_, 4, v_r_2741_);
                    v___x_2783_ = v_reuseFailAlloc_2787_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_2762_ == 0 {
                    leanh::lean_ctor_set(v___x_2761_, 4, v___x_2783_);
                    leanh::lean_ctor_set(v___x_2761_, 3, v___y_2779_);
                    leanh::lean_ctor_set(v___x_2761_, 2, v_v_2765_);
                    leanh::lean_ctor_set(v___x_2761_, 1, v_k_2764_);
                    leanh::lean_ctor_set(v___x_2761_, 0, v___x_2776_);
                    v___x_2785_ = v___x_2761_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2786_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2776_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_k_2764_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2786_, 2, v_v_2765_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2786_, 3, v___y_2779_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2786_, 4, v___x_2783_);
                    v___x_2785_ = v_reuseFailAlloc_2786_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_2785_;
            }
            36 => {
                v___x_2790_ = lean_nat_add(v___x_2775_, v___y_2789_);
                leanh::lean_dec(v___y_2789_);
                leanh::lean_dec(v___x_2775_);
                if v_isShared_2746_ == 0 {
                    leanh::lean_ctor_set(v___x_2745_, 4, v_l_2766_);
                    leanh::lean_ctor_set(v___x_2745_, 3, v_tree_2748_);
                    leanh::lean_ctor_set(v___x_2745_, 2, v_v_2750_);
                    leanh::lean_ctor_set(v___x_2745_, 1, v_k_2749_);
                    leanh::lean_ctor_set(v___x_2745_, 0, v___x_2790_);
                    v___x_2792_ = v___x_2745_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2796_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2790_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2796_, 1, v_k_2749_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2796_, 2, v_v_2750_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2796_, 3, v_tree_2748_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2796_, 4, v_l_2766_);
                    v___x_2792_ = v_reuseFailAlloc_2796_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_2793_ = lean_nat_add(v___x_2742_, v_size_2768_);
                if leanh::lean_obj_tag(v_r_2767_) == 0 {
                    v_size_2794_ = leanh::lean_ctor_get(v_r_2767_, 0);
                    leanh::lean_inc(v_size_2794_);
                    v___y_2778_ = v___x_2793_;
                    v___y_2779_ = v___x_2792_;
                    v___y_2780_ = v_size_2794_;
                    state = 33;
                    continue;
                } else {
                    v___x_2795_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2778_ = v___x_2793_;
                    v___y_2779_ = v___x_2792_;
                    v___y_2780_ = v___x_2795_;
                    state = 33;
                    continue;
                }
            }
            38 => {
                if v_isShared_2746_ == 0 {
                    leanh::lean_ctor_set(v___x_2745_, 4, v_r_2741_);
                    leanh::lean_ctor_set(v___x_2745_, 3, v___x_2809_);
                    leanh::lean_ctor_set(v___x_2745_, 2, v_v_2739_);
                    leanh::lean_ctor_set(v___x_2745_, 1, v_k_2738_);
                    leanh::lean_ctor_set(v___x_2745_, 0, v___x_2806_);
                    v___x_2811_ = v___x_2745_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2812_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2806_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_k_2738_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2812_, 2, v_v_2739_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2812_, 3, v___x_2809_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2812_, 4, v_r_2741_);
                    v___x_2811_ = v_reuseFailAlloc_2812_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_2811_;
            }
            40 => {
                if leanh::lean_obj_tag(v_l_2740_) == 0 {
                    if leanh::lean_obj_tag(v_r_2741_) == 0 {
                        v_k_2823_ = leanh::lean_ctor_get(v___x_2747_, 0);
                        leanh::lean_inc(v_k_2823_);
                        v_v_2824_ = leanh::lean_ctor_get(v___x_2747_, 1);
                        leanh::lean_inc(v_v_2824_);
                        leanh::lean_dec_ref(v___x_2747_);
                        v_size_2825_ = leanh::lean_ctor_get(v_l_2740_, 0);
                        v___x_2826_ = lean_nat_add(v___x_2742_, v_size_2737_);
                        leanh::lean_dec(v_size_2737_);
                        v___x_2827_ = lean_nat_add(v___x_2742_, v_size_2825_);
                        if v_isShared_2822_ == 0 {
                            leanh::lean_ctor_set(v___x_2821_, 4, v_l_2740_);
                            leanh::lean_ctor_set(v___x_2821_, 3, v_tree_2748_);
                            leanh::lean_ctor_set(v___x_2821_, 2, v_v_2824_);
                            leanh::lean_ctor_set(v___x_2821_, 1, v_k_2823_);
                            leanh::lean_ctor_set(v___x_2821_, 0, v___x_2827_);
                            v___x_2829_ = v___x_2821_;
                            state = 41;
                            continue;
                        } else {
                            v_reuseFailAlloc_2833_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2827_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_k_2823_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 2, v_v_2824_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 3, v_tree_2748_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 4, v_l_2740_);
                            v___x_2829_ = v_reuseFailAlloc_2833_;
                            state = 41;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_size_2737_);
                        v_k_2834_ = leanh::lean_ctor_get(v___x_2747_, 0);
                        leanh::lean_inc(v_k_2834_);
                        v_v_2835_ = leanh::lean_ctor_get(v___x_2747_, 1);
                        leanh::lean_inc(v_v_2835_);
                        leanh::lean_dec_ref(v___x_2747_);
                        v_k_2836_ = leanh::lean_ctor_get(v_l_2740_, 1);
                        v_v_2837_ = leanh::lean_ctor_get(v_l_2740_, 2);
                        v_isSharedCheck_2851_ = (!leanh::lean_is_exclusive(v_l_2740_)) as u8;
                        if v_isSharedCheck_2851_ == 0 {
                            v_unused_2852_ = leanh::lean_ctor_get(v_l_2740_, 4);
                            leanh::lean_dec(v_unused_2852_);
                            v_unused_2853_ = leanh::lean_ctor_get(v_l_2740_, 3);
                            leanh::lean_dec(v_unused_2853_);
                            v_unused_2854_ = leanh::lean_ctor_get(v_l_2740_, 0);
                            leanh::lean_dec(v_unused_2854_);
                            v___x_2839_ = v_l_2740_;
                            v_isShared_2840_ = v_isSharedCheck_2851_;
                            state = 43;
                            continue;
                        } else {
                            leanh::lean_inc(v_v_2837_);
                            leanh::lean_inc(v_k_2836_);
                            leanh::lean_dec(v_l_2740_);
                            v___x_2839_ = leanh::lean_box(0);
                            v_isShared_2840_ = v_isSharedCheck_2851_;
                            state = 43;
                            continue;
                        }
                    }
                } else {
                    if leanh::lean_obj_tag(v_r_2741_) == 0 {
                        leanh::lean_dec(v_size_2737_);
                        v_k_2855_ = leanh::lean_ctor_get(v___x_2747_, 0);
                        leanh::lean_inc(v_k_2855_);
                        v_v_2856_ = leanh::lean_ctor_get(v___x_2747_, 1);
                        leanh::lean_inc(v_v_2856_);
                        leanh::lean_dec_ref(v___x_2747_);
                        v___x_2857_ = leanh::lean_unsigned_to_nat(3);
                        if v_isShared_2822_ == 0 {
                            leanh::lean_ctor_set(v___x_2821_, 4, v_l_2740_);
                            leanh::lean_ctor_set(v___x_2821_, 2, v_v_2856_);
                            leanh::lean_ctor_set(v___x_2821_, 1, v_k_2855_);
                            leanh::lean_ctor_set(v___x_2821_, 0, v___x_2742_);
                            v___x_2859_ = v___x_2821_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_2863_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2742_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_k_2855_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 2, v_v_2856_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 3, v_l_2740_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 4, v_l_2740_);
                            v___x_2859_ = v_reuseFailAlloc_2863_;
                            state = 47;
                            continue;
                        }
                    } else {
                        v_k_2864_ = leanh::lean_ctor_get(v___x_2747_, 0);
                        leanh::lean_inc(v_k_2864_);
                        v_v_2865_ = leanh::lean_ctor_get(v___x_2747_, 1);
                        leanh::lean_inc(v_v_2865_);
                        leanh::lean_dec_ref(v___x_2747_);
                        if v_isShared_2822_ == 0 {
                            leanh::lean_ctor_set(v___x_2821_, 3, v_r_2741_);
                            v___x_2867_ = v___x_2821_;
                            state = 49;
                            continue;
                        } else {
                            v_reuseFailAlloc_2872_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_size_2737_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_k_2738_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2872_, 2, v_v_2739_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2872_, 3, v_r_2741_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2872_, 4, v_r_2741_);
                            v___x_2867_ = v_reuseFailAlloc_2872_;
                            state = 49;
                            continue;
                        }
                    }
                }
            }
            41 => {
                if v_isShared_2746_ == 0 {
                    leanh::lean_ctor_set(v___x_2745_, 4, v_r_2741_);
                    leanh::lean_ctor_set(v___x_2745_, 3, v___x_2829_);
                    leanh::lean_ctor_set(v___x_2745_, 2, v_v_2739_);
                    leanh::lean_ctor_set(v___x_2745_, 1, v_k_2738_);
                    leanh::lean_ctor_set(v___x_2745_, 0, v___x_2826_);
                    v___x_2831_ = v___x_2745_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_2832_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2826_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_k_2738_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2832_, 2, v_v_2739_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2832_, 3, v___x_2829_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2832_, 4, v_r_2741_);
                    v___x_2831_ = v_reuseFailAlloc_2832_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_2831_;
            }
            43 => {
                v___x_2841_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_2840_ == 0 {
                    leanh::lean_ctor_set(v___x_2839_, 4, v_r_2741_);
                    leanh::lean_ctor_set(v___x_2839_, 3, v_r_2741_);
                    leanh::lean_ctor_set(v___x_2839_, 2, v_v_2835_);
                    leanh::lean_ctor_set(v___x_2839_, 1, v_k_2834_);
                    leanh::lean_ctor_set(v___x_2839_, 0, v___x_2742_);
                    v___x_2843_ = v___x_2839_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2850_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2742_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_k_2834_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 2, v_v_2835_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 3, v_r_2741_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 4, v_r_2741_);
                    v___x_2843_ = v_reuseFailAlloc_2850_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_2822_ == 0 {
                    leanh::lean_ctor_set(v___x_2821_, 3, v_r_2741_);
                    leanh::lean_ctor_set(v___x_2821_, 0, v___x_2742_);
                    v___x_2845_ = v___x_2821_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2849_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2742_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 1, v_k_2738_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 2, v_v_2739_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 3, v_r_2741_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 4, v_r_2741_);
                    v___x_2845_ = v_reuseFailAlloc_2849_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_2746_ == 0 {
                    leanh::lean_ctor_set(v___x_2745_, 4, v___x_2845_);
                    leanh::lean_ctor_set(v___x_2745_, 3, v___x_2843_);
                    leanh::lean_ctor_set(v___x_2745_, 2, v_v_2837_);
                    leanh::lean_ctor_set(v___x_2745_, 1, v_k_2836_);
                    leanh::lean_ctor_set(v___x_2745_, 0, v___x_2841_);
                    v___x_2847_ = v___x_2745_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2848_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2841_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_k_2836_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2848_, 2, v_v_2837_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2848_, 3, v___x_2843_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2848_, 4, v___x_2845_);
                    v___x_2847_ = v_reuseFailAlloc_2848_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_2847_;
            }
            47 => {
                if v_isShared_2746_ == 0 {
                    leanh::lean_ctor_set(v___x_2745_, 4, v_r_2741_);
                    leanh::lean_ctor_set(v___x_2745_, 3, v___x_2859_);
                    leanh::lean_ctor_set(v___x_2745_, 2, v_v_2739_);
                    leanh::lean_ctor_set(v___x_2745_, 1, v_k_2738_);
                    leanh::lean_ctor_set(v___x_2745_, 0, v___x_2857_);
                    v___x_2861_ = v___x_2745_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_2862_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2857_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2862_, 1, v_k_2738_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2862_, 2, v_v_2739_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2862_, 3, v___x_2859_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2862_, 4, v_r_2741_);
                    v___x_2861_ = v_reuseFailAlloc_2862_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_2861_;
            }
            49 => {
                v___x_2868_ = leanh::lean_unsigned_to_nat(2);
                if v_isShared_2746_ == 0 {
                    leanh::lean_ctor_set(v___x_2745_, 4, v___x_2867_);
                    leanh::lean_ctor_set(v___x_2745_, 3, v_r_2741_);
                    leanh::lean_ctor_set(v___x_2745_, 2, v_v_2865_);
                    leanh::lean_ctor_set(v___x_2745_, 1, v_k_2864_);
                    leanh::lean_ctor_set(v___x_2745_, 0, v___x_2868_);
                    v___x_2870_ = v___x_2745_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_2871_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2868_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_k_2864_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2871_, 2, v_v_2865_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2871_, 3, v_r_2741_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2871_, 4, v___x_2867_);
                    v___x_2870_ = v_reuseFailAlloc_2871_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_2870_;
            }
            51 => {
                v___x_2888_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(
                    v_k_2738_, v_v_2739_, v_l_2740_, v_r_2741_,
                );
                v_tree_2889_ = leanh::lean_ctor_get(v___x_2888_, 2);
                leanh::lean_inc(v_tree_2889_);
                if leanh::lean_obj_tag(v_tree_2889_) == 0 {
                    v_k_2890_ = leanh::lean_ctor_get(v___x_2888_, 0);
                    leanh::lean_inc(v_k_2890_);
                    v_v_2891_ = leanh::lean_ctor_get(v___x_2888_, 1);
                    leanh::lean_inc(v_v_2891_);
                    leanh::lean_dec_ref(v___x_2888_);
                    v_size_2892_ = leanh::lean_ctor_get(v_tree_2889_, 0);
                    v___x_2893_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2894_ = lean_nat_mul(v___x_2893_, v_size_2892_);
                    v___x_2895_ = lean_nat_dec_lt(v___x_2894_, v_size_2732_);
                    leanh::lean_dec(v___x_2894_);
                    if v___x_2895_ == 0 {
                        leanh::lean_dec(v_r_2736_);
                        v___x_2896_ = lean_nat_add(v___x_2742_, v_size_2732_);
                        v___x_2897_ = lean_nat_add(v___x_2896_, v_size_2892_);
                        leanh::lean_dec(v___x_2896_);
                        if v_isShared_2887_ == 0 {
                            leanh::lean_ctor_set(v___x_2886_, 4, v_tree_2889_);
                            leanh::lean_ctor_set(v___x_2886_, 3, v_l_2552_);
                            leanh::lean_ctor_set(v___x_2886_, 2, v_v_2891_);
                            leanh::lean_ctor_set(v___x_2886_, 1, v_k_2890_);
                            leanh::lean_ctor_set(v___x_2886_, 0, v___x_2897_);
                            v___x_2899_ = v___x_2886_;
                            state = 52;
                            continue;
                        } else {
                            v_reuseFailAlloc_2900_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2897_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_k_2890_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 2, v_v_2891_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 3, v_l_2552_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 4, v_tree_2889_);
                            v___x_2899_ = v_reuseFailAlloc_2900_;
                            state = 52;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_l_2735_);
                        leanh::lean_inc(v_v_2734_);
                        leanh::lean_inc(v_k_2733_);
                        leanh::lean_inc(v_size_2732_);
                        v_isSharedCheck_2966_ = (!leanh::lean_is_exclusive(v_l_2552_)) as u8;
                        if v_isSharedCheck_2966_ == 0 {
                            v_unused_2967_ = leanh::lean_ctor_get(v_l_2552_, 4);
                            leanh::lean_dec(v_unused_2967_);
                            v_unused_2968_ = leanh::lean_ctor_get(v_l_2552_, 3);
                            leanh::lean_dec(v_unused_2968_);
                            v_unused_2969_ = leanh::lean_ctor_get(v_l_2552_, 2);
                            leanh::lean_dec(v_unused_2969_);
                            v_unused_2970_ = leanh::lean_ctor_get(v_l_2552_, 1);
                            leanh::lean_dec(v_unused_2970_);
                            v_unused_2971_ = leanh::lean_ctor_get(v_l_2552_, 0);
                            leanh::lean_dec(v_unused_2971_);
                            v___x_2902_ = v_l_2552_;
                            v_isShared_2903_ = v_isSharedCheck_2966_;
                            state = 53;
                            continue;
                        } else {
                            leanh::lean_dec(v_l_2552_);
                            v___x_2902_ = leanh::lean_box(0);
                            v_isShared_2903_ = v_isSharedCheck_2966_;
                            state = 53;
                            continue;
                        }
                    }
                } else {
                    if leanh::lean_obj_tag(v_l_2735_) == 0 {
                        leanh::lean_inc_ref(v_l_2735_);
                        leanh::lean_inc(v_v_2734_);
                        leanh::lean_inc(v_k_2733_);
                        leanh::lean_inc(v_size_2732_);
                        v_isSharedCheck_2995_ = (!leanh::lean_is_exclusive(v_l_2552_)) as u8;
                        if v_isSharedCheck_2995_ == 0 {
                            v_unused_2996_ = leanh::lean_ctor_get(v_l_2552_, 4);
                            leanh::lean_dec(v_unused_2996_);
                            v_unused_2997_ = leanh::lean_ctor_get(v_l_2552_, 3);
                            leanh::lean_dec(v_unused_2997_);
                            v_unused_2998_ = leanh::lean_ctor_get(v_l_2552_, 2);
                            leanh::lean_dec(v_unused_2998_);
                            v_unused_2999_ = leanh::lean_ctor_get(v_l_2552_, 1);
                            leanh::lean_dec(v_unused_2999_);
                            v_unused_3000_ = leanh::lean_ctor_get(v_l_2552_, 0);
                            leanh::lean_dec(v_unused_3000_);
                            v___x_2973_ = v_l_2552_;
                            v_isShared_2974_ = v_isSharedCheck_2995_;
                            state = 63;
                            continue;
                        } else {
                            leanh::lean_dec(v_l_2552_);
                            v___x_2973_ = leanh::lean_box(0);
                            v_isShared_2974_ = v_isSharedCheck_2995_;
                            state = 63;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v_r_2736_) == 0 {
                            leanh::lean_inc(v_l_2735_);
                            leanh::lean_inc(v_v_2734_);
                            leanh::lean_inc(v_k_2733_);
                            v_isSharedCheck_3025_ =
                                (!leanh::lean_is_exclusive(v_l_2552_)) as u8;
                            if v_isSharedCheck_3025_ == 0 {
                                v_unused_3026_ = leanh::lean_ctor_get(v_l_2552_, 4);
                                leanh::lean_dec(v_unused_3026_);
                                v_unused_3027_ = leanh::lean_ctor_get(v_l_2552_, 3);
                                leanh::lean_dec(v_unused_3027_);
                                v_unused_3028_ = leanh::lean_ctor_get(v_l_2552_, 2);
                                leanh::lean_dec(v_unused_3028_);
                                v_unused_3029_ = leanh::lean_ctor_get(v_l_2552_, 1);
                                leanh::lean_dec(v_unused_3029_);
                                v_unused_3030_ = leanh::lean_ctor_get(v_l_2552_, 0);
                                leanh::lean_dec(v_unused_3030_);
                                v___x_3002_ = v_l_2552_;
                                v_isShared_3003_ = v_isSharedCheck_3025_;
                                state = 68;
                                continue;
                            } else {
                                leanh::lean_dec(v_l_2552_);
                                v___x_3002_ = leanh::lean_box(0);
                                v_isShared_3003_ = v_isSharedCheck_3025_;
                                state = 68;
                                continue;
                            }
                        } else {
                            v_k_3031_ = leanh::lean_ctor_get(v___x_2888_, 0);
                            leanh::lean_inc(v_k_3031_);
                            v_v_3032_ = leanh::lean_ctor_get(v___x_2888_, 1);
                            leanh::lean_inc(v_v_3032_);
                            leanh::lean_dec_ref(v___x_2888_);
                            v___x_3033_ = leanh::lean_unsigned_to_nat(2);
                            if v_isShared_2887_ == 0 {
                                leanh::lean_ctor_set(v___x_2886_, 4, v_r_2736_);
                                leanh::lean_ctor_set(v___x_2886_, 3, v_l_2552_);
                                leanh::lean_ctor_set(v___x_2886_, 2, v_v_3032_);
                                leanh::lean_ctor_set(v___x_2886_, 1, v_k_3031_);
                                leanh::lean_ctor_set(v___x_2886_, 0, v___x_3033_);
                                v___x_3035_ = v___x_2886_;
                                state = 73;
                                continue;
                            } else {
                                v_reuseFailAlloc_3036_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_k_3031_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 2, v_v_3032_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 3, v_l_2552_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 4, v_r_2736_);
                                v___x_3035_ = v_reuseFailAlloc_3036_;
                                state = 73;
                                continue;
                            }
                        }
                    }
                }
            }
            52 => {
                return v___x_2899_;
            }
            53 => {
                v_size_2904_ = leanh::lean_ctor_get(v_l_2735_, 0);
                v_size_2905_ = leanh::lean_ctor_get(v_r_2736_, 0);
                v_k_2906_ = leanh::lean_ctor_get(v_r_2736_, 1);
                v_v_2907_ = leanh::lean_ctor_get(v_r_2736_, 2);
                v_l_2908_ = leanh::lean_ctor_get(v_r_2736_, 3);
                v_r_2909_ = leanh::lean_ctor_get(v_r_2736_, 4);
                v___x_2910_ = leanh::lean_unsigned_to_nat(2);
                v___x_2911_ = lean_nat_mul(v___x_2910_, v_size_2904_);
                v___x_2912_ = lean_nat_dec_lt(v_size_2905_, v___x_2911_);
                leanh::lean_dec(v___x_2911_);
                if v___x_2912_ == 0 {
                    leanh::lean_inc(v_r_2909_);
                    leanh::lean_inc(v_l_2908_);
                    leanh::lean_inc(v_v_2907_);
                    leanh::lean_inc(v_k_2906_);
                    leanh::lean_del_object(v___x_2902_);
                    v_isSharedCheck_2950_ = (!leanh::lean_is_exclusive(v_r_2736_)) as u8;
                    if v_isSharedCheck_2950_ == 0 {
                        v_unused_2951_ = leanh::lean_ctor_get(v_r_2736_, 4);
                        leanh::lean_dec(v_unused_2951_);
                        v_unused_2952_ = leanh::lean_ctor_get(v_r_2736_, 3);
                        leanh::lean_dec(v_unused_2952_);
                        v_unused_2953_ = leanh::lean_ctor_get(v_r_2736_, 2);
                        leanh::lean_dec(v_unused_2953_);
                        v_unused_2954_ = leanh::lean_ctor_get(v_r_2736_, 1);
                        leanh::lean_dec(v_unused_2954_);
                        v_unused_2955_ = leanh::lean_ctor_get(v_r_2736_, 0);
                        leanh::lean_dec(v_unused_2955_);
                        v___x_2914_ = v_r_2736_;
                        v_isShared_2915_ = v_isSharedCheck_2950_;
                        state = 54;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_2736_);
                        v___x_2914_ = leanh::lean_box(0);
                        v_isShared_2915_ = v_isSharedCheck_2950_;
                        state = 54;
                        continue;
                    }
                } else {
                    v___x_2956_ = lean_nat_add(v___x_2742_, v_size_2732_);
                    leanh::lean_dec(v_size_2732_);
                    v___x_2957_ = lean_nat_add(v___x_2956_, v_size_2892_);
                    leanh::lean_dec(v___x_2956_);
                    v___x_2958_ = lean_nat_add(v___x_2742_, v_size_2892_);
                    v___x_2959_ = lean_nat_add(v___x_2958_, v_size_2905_);
                    leanh::lean_dec(v___x_2958_);
                    if v_isShared_2887_ == 0 {
                        leanh::lean_ctor_set(v___x_2886_, 4, v_tree_2889_);
                        leanh::lean_ctor_set(v___x_2886_, 3, v_r_2736_);
                        leanh::lean_ctor_set(v___x_2886_, 2, v_v_2891_);
                        leanh::lean_ctor_set(v___x_2886_, 1, v_k_2890_);
                        leanh::lean_ctor_set(v___x_2886_, 0, v___x_2959_);
                        v___x_2961_ = v___x_2886_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_2965_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2959_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_k_2890_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2965_, 2, v_v_2891_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2965_, 3, v_r_2736_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2965_, 4, v_tree_2889_);
                        v___x_2961_ = v_reuseFailAlloc_2965_;
                        state = 61;
                        continue;
                    }
                }
            }
            54 => {
                v___x_2916_ = lean_nat_add(v___x_2742_, v_size_2732_);
                leanh::lean_dec(v_size_2732_);
                v___x_2917_ = lean_nat_add(v___x_2916_, v_size_2892_);
                leanh::lean_dec(v___x_2916_);
                v___x_2938_ = lean_nat_add(v___x_2742_, v_size_2904_);
                if leanh::lean_obj_tag(v_l_2908_) == 0 {
                    v_size_2948_ = leanh::lean_ctor_get(v_l_2908_, 0);
                    leanh::lean_inc(v_size_2948_);
                    v___y_2940_ = v_size_2948_;
                    state = 59;
                    continue;
                } else {
                    v___x_2949_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2940_ = v___x_2949_;
                    state = 59;
                    continue;
                }
            }
            55 => {
                v___x_2922_ = lean_nat_add(v___y_2920_, v___y_2921_);
                leanh::lean_dec(v___y_2921_);
                leanh::lean_dec(v___y_2920_);
                leanh::lean_inc_ref(v_tree_2889_);
                if v_isShared_2915_ == 0 {
                    leanh::lean_ctor_set(v___x_2914_, 4, v_tree_2889_);
                    leanh::lean_ctor_set(v___x_2914_, 3, v_r_2909_);
                    leanh::lean_ctor_set(v___x_2914_, 2, v_v_2891_);
                    leanh::lean_ctor_set(v___x_2914_, 1, v_k_2890_);
                    leanh::lean_ctor_set(v___x_2914_, 0, v___x_2922_);
                    v___x_2924_ = v___x_2914_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_2937_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2937_, 0, v___x_2922_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2937_, 1, v_k_2890_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2937_, 2, v_v_2891_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2937_, 3, v_r_2909_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2937_, 4, v_tree_2889_);
                    v___x_2924_ = v_reuseFailAlloc_2937_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                v_isSharedCheck_2931_ = (!leanh::lean_is_exclusive(v_tree_2889_)) as u8;
                if v_isSharedCheck_2931_ == 0 {
                    v_unused_2932_ = leanh::lean_ctor_get(v_tree_2889_, 4);
                    leanh::lean_dec(v_unused_2932_);
                    v_unused_2933_ = leanh::lean_ctor_get(v_tree_2889_, 3);
                    leanh::lean_dec(v_unused_2933_);
                    v_unused_2934_ = leanh::lean_ctor_get(v_tree_2889_, 2);
                    leanh::lean_dec(v_unused_2934_);
                    v_unused_2935_ = leanh::lean_ctor_get(v_tree_2889_, 1);
                    leanh::lean_dec(v_unused_2935_);
                    v_unused_2936_ = leanh::lean_ctor_get(v_tree_2889_, 0);
                    leanh::lean_dec(v_unused_2936_);
                    v___x_2926_ = v_tree_2889_;
                    v_isShared_2927_ = v_isSharedCheck_2931_;
                    state = 57;
                    continue;
                } else {
                    leanh::lean_dec(v_tree_2889_);
                    v___x_2926_ = leanh::lean_box(0);
                    v_isShared_2927_ = v_isSharedCheck_2931_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                if v_isShared_2927_ == 0 {
                    leanh::lean_ctor_set(v___x_2926_, 4, v___x_2924_);
                    leanh::lean_ctor_set(v___x_2926_, 3, v___y_2919_);
                    leanh::lean_ctor_set(v___x_2926_, 2, v_v_2907_);
                    leanh::lean_ctor_set(v___x_2926_, 1, v_k_2906_);
                    leanh::lean_ctor_set(v___x_2926_, 0, v___x_2917_);
                    v___x_2929_ = v___x_2926_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_2930_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2917_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_k_2906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 2, v_v_2907_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 3, v___y_2919_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 4, v___x_2924_);
                    v___x_2929_ = v_reuseFailAlloc_2930_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_2929_;
            }
            59 => {
                v___x_2941_ = lean_nat_add(v___x_2938_, v___y_2940_);
                leanh::lean_dec(v___y_2940_);
                leanh::lean_dec(v___x_2938_);
                if v_isShared_2887_ == 0 {
                    leanh::lean_ctor_set(v___x_2886_, 4, v_l_2908_);
                    leanh::lean_ctor_set(v___x_2886_, 3, v_l_2735_);
                    leanh::lean_ctor_set(v___x_2886_, 2, v_v_2734_);
                    leanh::lean_ctor_set(v___x_2886_, 1, v_k_2733_);
                    leanh::lean_ctor_set(v___x_2886_, 0, v___x_2941_);
                    v___x_2943_ = v___x_2886_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2947_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2941_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 1, v_k_2733_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 2, v_v_2734_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 3, v_l_2735_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 4, v_l_2908_);
                    v___x_2943_ = v_reuseFailAlloc_2947_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                v___x_2944_ = lean_nat_add(v___x_2742_, v_size_2892_);
                if leanh::lean_obj_tag(v_r_2909_) == 0 {
                    v_size_2945_ = leanh::lean_ctor_get(v_r_2909_, 0);
                    leanh::lean_inc(v_size_2945_);
                    v___y_2919_ = v___x_2943_;
                    v___y_2920_ = v___x_2944_;
                    v___y_2921_ = v_size_2945_;
                    state = 55;
                    continue;
                } else {
                    v___x_2946_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2919_ = v___x_2943_;
                    v___y_2920_ = v___x_2944_;
                    v___y_2921_ = v___x_2946_;
                    state = 55;
                    continue;
                }
            }
            61 => {
                if v_isShared_2903_ == 0 {
                    leanh::lean_ctor_set(v___x_2902_, 4, v___x_2961_);
                    leanh::lean_ctor_set(v___x_2902_, 0, v___x_2957_);
                    v___x_2963_ = v___x_2902_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_2964_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_k_2733_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2964_, 2, v_v_2734_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2964_, 3, v_l_2735_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2964_, 4, v___x_2961_);
                    v___x_2963_ = v_reuseFailAlloc_2964_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_2963_;
            }
            63 => {
                if leanh::lean_obj_tag(v_r_2736_) == 0 {
                    v_k_2975_ = leanh::lean_ctor_get(v___x_2888_, 0);
                    leanh::lean_inc(v_k_2975_);
                    v_v_2976_ = leanh::lean_ctor_get(v___x_2888_, 1);
                    leanh::lean_inc(v_v_2976_);
                    leanh::lean_dec_ref(v___x_2888_);
                    v_size_2977_ = leanh::lean_ctor_get(v_r_2736_, 0);
                    v___x_2978_ = lean_nat_add(v___x_2742_, v_size_2732_);
                    leanh::lean_dec(v_size_2732_);
                    v___x_2979_ = lean_nat_add(v___x_2742_, v_size_2977_);
                    if v_isShared_2887_ == 0 {
                        leanh::lean_ctor_set(v___x_2886_, 4, v_tree_2889_);
                        leanh::lean_ctor_set(v___x_2886_, 3, v_r_2736_);
                        leanh::lean_ctor_set(v___x_2886_, 2, v_v_2976_);
                        leanh::lean_ctor_set(v___x_2886_, 1, v_k_2975_);
                        leanh::lean_ctor_set(v___x_2886_, 0, v___x_2979_);
                        v___x_2981_ = v___x_2886_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_2985_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2979_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_k_2975_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 2, v_v_2976_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 3, v_r_2736_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 4, v_tree_2889_);
                        v___x_2981_ = v_reuseFailAlloc_2985_;
                        state = 64;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_size_2732_);
                    v_k_2986_ = leanh::lean_ctor_get(v___x_2888_, 0);
                    leanh::lean_inc(v_k_2986_);
                    v_v_2987_ = leanh::lean_ctor_get(v___x_2888_, 1);
                    leanh::lean_inc(v_v_2987_);
                    leanh::lean_dec_ref(v___x_2888_);
                    v___x_2988_ = leanh::lean_unsigned_to_nat(3);
                    if v_isShared_2887_ == 0 {
                        leanh::lean_ctor_set(v___x_2886_, 4, v_r_2736_);
                        leanh::lean_ctor_set(v___x_2886_, 3, v_r_2736_);
                        leanh::lean_ctor_set(v___x_2886_, 2, v_v_2987_);
                        leanh::lean_ctor_set(v___x_2886_, 1, v_k_2986_);
                        leanh::lean_ctor_set(v___x_2886_, 0, v___x_2742_);
                        v___x_2990_ = v___x_2886_;
                        state = 66;
                        continue;
                    } else {
                        v_reuseFailAlloc_2994_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2742_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_k_2986_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 2, v_v_2987_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 3, v_r_2736_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 4, v_r_2736_);
                        v___x_2990_ = v_reuseFailAlloc_2994_;
                        state = 66;
                        continue;
                    }
                }
            }
            64 => {
                if v_isShared_2974_ == 0 {
                    leanh::lean_ctor_set(v___x_2973_, 4, v___x_2981_);
                    leanh::lean_ctor_set(v___x_2973_, 0, v___x_2978_);
                    v___x_2983_ = v___x_2973_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_2984_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2978_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_k_2733_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 2, v_v_2734_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 3, v_l_2735_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 4, v___x_2981_);
                    v___x_2983_ = v_reuseFailAlloc_2984_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_2983_;
            }
            66 => {
                if v_isShared_2974_ == 0 {
                    leanh::lean_ctor_set(v___x_2973_, 4, v___x_2990_);
                    leanh::lean_ctor_set(v___x_2973_, 0, v___x_2988_);
                    v___x_2992_ = v___x_2973_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_2993_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_k_2733_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 2, v_v_2734_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 3, v_l_2735_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 4, v___x_2990_);
                    v___x_2992_ = v_reuseFailAlloc_2993_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_2992_;
            }
            68 => {
                v_k_3004_ = leanh::lean_ctor_get(v___x_2888_, 0);
                leanh::lean_inc(v_k_3004_);
                v_v_3005_ = leanh::lean_ctor_get(v___x_2888_, 1);
                leanh::lean_inc(v_v_3005_);
                leanh::lean_dec_ref(v___x_2888_);
                v_k_3006_ = leanh::lean_ctor_get(v_r_2736_, 1);
                v_v_3007_ = leanh::lean_ctor_get(v_r_2736_, 2);
                v_isSharedCheck_3021_ = (!leanh::lean_is_exclusive(v_r_2736_)) as u8;
                if v_isSharedCheck_3021_ == 0 {
                    v_unused_3022_ = leanh::lean_ctor_get(v_r_2736_, 4);
                    leanh::lean_dec(v_unused_3022_);
                    v_unused_3023_ = leanh::lean_ctor_get(v_r_2736_, 3);
                    leanh::lean_dec(v_unused_3023_);
                    v_unused_3024_ = leanh::lean_ctor_get(v_r_2736_, 0);
                    leanh::lean_dec(v_unused_3024_);
                    v___x_3009_ = v_r_2736_;
                    v_isShared_3010_ = v_isSharedCheck_3021_;
                    state = 69;
                    continue;
                } else {
                    leanh::lean_inc(v_v_3007_);
                    leanh::lean_inc(v_k_3006_);
                    leanh::lean_dec(v_r_2736_);
                    v___x_3009_ = leanh::lean_box(0);
                    v_isShared_3010_ = v_isSharedCheck_3021_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                v___x_3011_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_3010_ == 0 {
                    leanh::lean_ctor_set(v___x_3009_, 4, v_l_2735_);
                    leanh::lean_ctor_set(v___x_3009_, 3, v_l_2735_);
                    leanh::lean_ctor_set(v___x_3009_, 2, v_v_2734_);
                    leanh::lean_ctor_set(v___x_3009_, 1, v_k_2733_);
                    leanh::lean_ctor_set(v___x_3009_, 0, v___x_2742_);
                    v___x_3013_ = v___x_3009_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_3020_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_2742_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3020_, 1, v_k_2733_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3020_, 2, v_v_2734_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3020_, 3, v_l_2735_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3020_, 4, v_l_2735_);
                    v___x_3013_ = v_reuseFailAlloc_3020_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                if v_isShared_2887_ == 0 {
                    leanh::lean_ctor_set(v___x_2886_, 4, v_l_2735_);
                    leanh::lean_ctor_set(v___x_2886_, 3, v_l_2735_);
                    leanh::lean_ctor_set(v___x_2886_, 2, v_v_3005_);
                    leanh::lean_ctor_set(v___x_2886_, 1, v_k_3004_);
                    leanh::lean_ctor_set(v___x_2886_, 0, v___x_2742_);
                    v___x_3015_ = v___x_2886_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_3019_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_2742_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 1, v_k_3004_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 2, v_v_3005_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 3, v_l_2735_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 4, v_l_2735_);
                    v___x_3015_ = v_reuseFailAlloc_3019_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_3003_ == 0 {
                    leanh::lean_ctor_set(v___x_3002_, 4, v___x_3015_);
                    leanh::lean_ctor_set(v___x_3002_, 3, v___x_3013_);
                    leanh::lean_ctor_set(v___x_3002_, 2, v_v_3007_);
                    leanh::lean_ctor_set(v___x_3002_, 1, v_k_3006_);
                    leanh::lean_ctor_set(v___x_3002_, 0, v___x_3011_);
                    v___x_3017_ = v___x_3002_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_3018_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3011_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_k_3006_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 2, v_v_3007_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 3, v___x_3013_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 4, v___x_3015_);
                    v___x_3017_ = v_reuseFailAlloc_3018_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                return v___x_3017_;
            }
            73 => {
                return v___x_3035_;
            }
            74 => {
                return v___x_3057_;
            }
            75 => {
                v_size_3062_ = leanh::lean_ctor_get(v_l_3049_, 0);
                v_size_3063_ = leanh::lean_ctor_get(v_r_3050_, 0);
                v_k_3064_ = leanh::lean_ctor_get(v_r_3050_, 1);
                v_v_3065_ = leanh::lean_ctor_get(v_r_3050_, 2);
                v_l_3066_ = leanh::lean_ctor_get(v_r_3050_, 3);
                v_r_3067_ = leanh::lean_ctor_get(v_r_3050_, 4);
                v___x_3068_ = leanh::lean_unsigned_to_nat(2);
                v___x_3069_ = lean_nat_mul(v___x_3068_, v_size_3062_);
                v___x_3070_ = lean_nat_dec_lt(v_size_3063_, v___x_3069_);
                leanh::lean_dec(v___x_3069_);
                if v___x_3070_ == 0 {
                    leanh::lean_inc(v_r_3067_);
                    leanh::lean_inc(v_l_3066_);
                    leanh::lean_inc(v_v_3065_);
                    leanh::lean_inc(v_k_3064_);
                    v_isSharedCheck_3099_ = (!leanh::lean_is_exclusive(v_r_3050_)) as u8;
                    if v_isSharedCheck_3099_ == 0 {
                        v_unused_3100_ = leanh::lean_ctor_get(v_r_3050_, 4);
                        leanh::lean_dec(v_unused_3100_);
                        v_unused_3101_ = leanh::lean_ctor_get(v_r_3050_, 3);
                        leanh::lean_dec(v_unused_3101_);
                        v_unused_3102_ = leanh::lean_ctor_get(v_r_3050_, 2);
                        leanh::lean_dec(v_unused_3102_);
                        v_unused_3103_ = leanh::lean_ctor_get(v_r_3050_, 1);
                        leanh::lean_dec(v_unused_3103_);
                        v_unused_3104_ = leanh::lean_ctor_get(v_r_3050_, 0);
                        leanh::lean_dec(v_unused_3104_);
                        v___x_3072_ = v_r_3050_;
                        v_isShared_3073_ = v_isSharedCheck_3099_;
                        state = 76;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_3050_);
                        v___x_3072_ = leanh::lean_box(0);
                        v_isShared_3073_ = v_isSharedCheck_3099_;
                        state = 76;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2555_);
                    v___x_3105_ = lean_nat_add(v___x_3044_, v_size_3046_);
                    leanh::lean_dec(v_size_3046_);
                    v___x_3106_ = lean_nat_add(v___x_3105_, v_size_3045_);
                    leanh::lean_dec(v___x_3105_);
                    v___x_3107_ = lean_nat_add(v___x_3044_, v_size_3045_);
                    leanh::lean_dec(v_size_3045_);
                    v___x_3108_ = lean_nat_add(v___x_3107_, v_size_3063_);
                    leanh::lean_dec(v___x_3107_);
                    leanh::lean_inc_ref(v_impl_3043_);
                    if v_isShared_3061_ == 0 {
                        leanh::lean_ctor_set(v___x_3060_, 4, v_impl_3043_);
                        leanh::lean_ctor_set(v___x_3060_, 3, v_r_3050_);
                        leanh::lean_ctor_set(v___x_3060_, 2, v_v_2551_);
                        leanh::lean_ctor_set(v___x_3060_, 1, v_k_2550_);
                        leanh::lean_ctor_set(v___x_3060_, 0, v___x_3108_);
                        v___x_3110_ = v___x_3060_;
                        state = 82;
                        continue;
                    } else {
                        v_reuseFailAlloc_3123_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3108_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3123_, 1, v_k_2550_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3123_, 2, v_v_2551_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3123_, 3, v_r_3050_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3123_, 4, v_impl_3043_);
                        v___x_3110_ = v_reuseFailAlloc_3123_;
                        state = 82;
                        continue;
                    }
                }
            }
            76 => {
                v___x_3074_ = lean_nat_add(v___x_3044_, v_size_3046_);
                leanh::lean_dec(v_size_3046_);
                v___x_3075_ = lean_nat_add(v___x_3074_, v_size_3045_);
                leanh::lean_dec(v___x_3074_);
                v___x_3087_ = lean_nat_add(v___x_3044_, v_size_3062_);
                if leanh::lean_obj_tag(v_l_3066_) == 0 {
                    v_size_3097_ = leanh::lean_ctor_get(v_l_3066_, 0);
                    leanh::lean_inc(v_size_3097_);
                    v___y_3089_ = v_size_3097_;
                    state = 80;
                    continue;
                } else {
                    v___x_3098_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3089_ = v___x_3098_;
                    state = 80;
                    continue;
                }
            }
            77 => {
                v___x_3080_ = lean_nat_add(v___y_3078_, v___y_3079_);
                leanh::lean_dec(v___y_3079_);
                leanh::lean_dec(v___y_3078_);
                if v_isShared_3073_ == 0 {
                    leanh::lean_ctor_set(v___x_3072_, 4, v_impl_3043_);
                    leanh::lean_ctor_set(v___x_3072_, 3, v_r_3067_);
                    leanh::lean_ctor_set(v___x_3072_, 2, v_v_2551_);
                    leanh::lean_ctor_set(v___x_3072_, 1, v_k_2550_);
                    leanh::lean_ctor_set(v___x_3072_, 0, v___x_3080_);
                    v___x_3082_ = v___x_3072_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_3086_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3080_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3086_, 1, v_k_2550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3086_, 2, v_v_2551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3086_, 3, v_r_3067_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3086_, 4, v_impl_3043_);
                    v___x_3082_ = v_reuseFailAlloc_3086_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                if v_isShared_3061_ == 0 {
                    leanh::lean_ctor_set(v___x_3060_, 4, v___x_3082_);
                    leanh::lean_ctor_set(v___x_3060_, 3, v___y_3077_);
                    leanh::lean_ctor_set(v___x_3060_, 2, v_v_3065_);
                    leanh::lean_ctor_set(v___x_3060_, 1, v_k_3064_);
                    leanh::lean_ctor_set(v___x_3060_, 0, v___x_3075_);
                    v___x_3084_ = v___x_3060_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_3085_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 1, v_k_3064_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 2, v_v_3065_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 3, v___y_3077_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 4, v___x_3082_);
                    v___x_3084_ = v_reuseFailAlloc_3085_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                return v___x_3084_;
            }
            80 => {
                v___x_3090_ = lean_nat_add(v___x_3087_, v___y_3089_);
                leanh::lean_dec(v___y_3089_);
                leanh::lean_dec(v___x_3087_);
                if v_isShared_2556_ == 0 {
                    leanh::lean_ctor_set(v___x_2555_, 4, v_l_3066_);
                    leanh::lean_ctor_set(v___x_2555_, 3, v_l_3049_);
                    leanh::lean_ctor_set(v___x_2555_, 2, v_v_3048_);
                    leanh::lean_ctor_set(v___x_2555_, 1, v_k_3047_);
                    leanh::lean_ctor_set(v___x_2555_, 0, v___x_3090_);
                    v___x_3092_ = v___x_2555_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_3096_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3090_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_k_3047_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 2, v_v_3048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 3, v_l_3049_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 4, v_l_3066_);
                    v___x_3092_ = v_reuseFailAlloc_3096_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                v___x_3093_ = lean_nat_add(v___x_3044_, v_size_3045_);
                leanh::lean_dec(v_size_3045_);
                if leanh::lean_obj_tag(v_r_3067_) == 0 {
                    v_size_3094_ = leanh::lean_ctor_get(v_r_3067_, 0);
                    leanh::lean_inc(v_size_3094_);
                    v___y_3077_ = v___x_3092_;
                    v___y_3078_ = v___x_3093_;
                    v___y_3079_ = v_size_3094_;
                    state = 77;
                    continue;
                } else {
                    v___x_3095_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3077_ = v___x_3092_;
                    v___y_3078_ = v___x_3093_;
                    v___y_3079_ = v___x_3095_;
                    state = 77;
                    continue;
                }
            }
            82 => {
                v_isSharedCheck_3117_ = (!leanh::lean_is_exclusive(v_impl_3043_)) as u8;
                if v_isSharedCheck_3117_ == 0 {
                    v_unused_3118_ = leanh::lean_ctor_get(v_impl_3043_, 4);
                    leanh::lean_dec(v_unused_3118_);
                    v_unused_3119_ = leanh::lean_ctor_get(v_impl_3043_, 3);
                    leanh::lean_dec(v_unused_3119_);
                    v_unused_3120_ = leanh::lean_ctor_get(v_impl_3043_, 2);
                    leanh::lean_dec(v_unused_3120_);
                    v_unused_3121_ = leanh::lean_ctor_get(v_impl_3043_, 1);
                    leanh::lean_dec(v_unused_3121_);
                    v_unused_3122_ = leanh::lean_ctor_get(v_impl_3043_, 0);
                    leanh::lean_dec(v_unused_3122_);
                    v___x_3112_ = v_impl_3043_;
                    v_isShared_3113_ = v_isSharedCheck_3117_;
                    state = 83;
                    continue;
                } else {
                    leanh::lean_dec(v_impl_3043_);
                    v___x_3112_ = leanh::lean_box(0);
                    v_isShared_3113_ = v_isSharedCheck_3117_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                if v_isShared_3113_ == 0 {
                    leanh::lean_ctor_set(v___x_3112_, 4, v___x_3110_);
                    leanh::lean_ctor_set(v___x_3112_, 3, v_l_3049_);
                    leanh::lean_ctor_set(v___x_3112_, 2, v_v_3048_);
                    leanh::lean_ctor_set(v___x_3112_, 1, v_k_3047_);
                    leanh::lean_ctor_set(v___x_3112_, 0, v___x_3106_);
                    v___x_3115_ = v___x_3112_;
                    state = 84;
                    continue;
                } else {
                    v_reuseFailAlloc_3116_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3106_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3116_, 1, v_k_3047_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3116_, 2, v_v_3048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3116_, 3, v_l_3049_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3116_, 4, v___x_3110_);
                    v___x_3115_ = v_reuseFailAlloc_3116_;
                    state = 84;
                    continue;
                }
            }
            84 => {
                return v___x_3115_;
            }
            85 => {
                return v___x_3133_;
            }
            86 => {
                v_size_3143_ = leanh::lean_ctor_get(v_r_3136_, 0);
                v___x_3144_ = lean_nat_add(v___x_3044_, v_size_3137_);
                leanh::lean_dec(v_size_3137_);
                v___x_3145_ = lean_nat_add(v___x_3044_, v_size_3143_);
                if v_isShared_3142_ == 0 {
                    leanh::lean_ctor_set(v___x_3141_, 4, v_impl_3043_);
                    leanh::lean_ctor_set(v___x_3141_, 3, v_r_3136_);
                    leanh::lean_ctor_set(v___x_3141_, 2, v_v_2551_);
                    leanh::lean_ctor_set(v___x_3141_, 1, v_k_2550_);
                    leanh::lean_ctor_set(v___x_3141_, 0, v___x_3145_);
                    v___x_3147_ = v___x_3141_;
                    state = 87;
                    continue;
                } else {
                    v_reuseFailAlloc_3151_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3145_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3151_, 1, v_k_2550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3151_, 2, v_v_2551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3151_, 3, v_r_3136_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3151_, 4, v_impl_3043_);
                    v___x_3147_ = v_reuseFailAlloc_3151_;
                    state = 87;
                    continue;
                }
            }
            87 => {
                if v_isShared_2556_ == 0 {
                    leanh::lean_ctor_set(v___x_2555_, 4, v___x_3147_);
                    leanh::lean_ctor_set(v___x_2555_, 3, v_l_3135_);
                    leanh::lean_ctor_set(v___x_2555_, 2, v_v_3139_);
                    leanh::lean_ctor_set(v___x_2555_, 1, v_k_3138_);
                    leanh::lean_ctor_set(v___x_2555_, 0, v___x_3144_);
                    v___x_3149_ = v___x_2555_;
                    state = 88;
                    continue;
                } else {
                    v_reuseFailAlloc_3150_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3144_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 1, v_k_3138_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 2, v_v_3139_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 3, v_l_3135_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 4, v___x_3147_);
                    v___x_3149_ = v_reuseFailAlloc_3150_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                return v___x_3149_;
            }
            89 => {
                v___x_3160_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_3159_ == 0 {
                    leanh::lean_ctor_set(v___x_3158_, 3, v_r_3136_);
                    leanh::lean_ctor_set(v___x_3158_, 2, v_v_2551_);
                    leanh::lean_ctor_set(v___x_3158_, 1, v_k_2550_);
                    leanh::lean_ctor_set(v___x_3158_, 0, v___x_3044_);
                    v___x_3162_ = v___x_3158_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_3166_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3044_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3166_, 1, v_k_2550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3166_, 2, v_v_2551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3166_, 3, v_r_3136_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3166_, 4, v_r_3136_);
                    v___x_3162_ = v_reuseFailAlloc_3166_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_2556_ == 0 {
                    leanh::lean_ctor_set(v___x_2555_, 4, v___x_3162_);
                    leanh::lean_ctor_set(v___x_2555_, 3, v_l_3135_);
                    leanh::lean_ctor_set(v___x_2555_, 2, v_v_3156_);
                    leanh::lean_ctor_set(v___x_2555_, 1, v_k_3155_);
                    leanh::lean_ctor_set(v___x_2555_, 0, v___x_3160_);
                    v___x_3164_ = v___x_2555_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_3165_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3160_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_k_3155_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3165_, 2, v_v_3156_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3165_, 3, v_l_3135_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3165_, 4, v___x_3162_);
                    v___x_3164_ = v_reuseFailAlloc_3165_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_3164_;
            }
            92 => {
                v_k_3177_ = leanh::lean_ctor_get(v_r_3171_, 1);
                v_v_3178_ = leanh::lean_ctor_get(v_r_3171_, 2);
                v_isSharedCheck_3192_ = (!leanh::lean_is_exclusive(v_r_3171_)) as u8;
                if v_isSharedCheck_3192_ == 0 {
                    v_unused_3193_ = leanh::lean_ctor_get(v_r_3171_, 4);
                    leanh::lean_dec(v_unused_3193_);
                    v_unused_3194_ = leanh::lean_ctor_get(v_r_3171_, 3);
                    leanh::lean_dec(v_unused_3194_);
                    v_unused_3195_ = leanh::lean_ctor_get(v_r_3171_, 0);
                    leanh::lean_dec(v_unused_3195_);
                    v___x_3180_ = v_r_3171_;
                    v_isShared_3181_ = v_isSharedCheck_3192_;
                    state = 93;
                    continue;
                } else {
                    leanh::lean_inc(v_v_3178_);
                    leanh::lean_inc(v_k_3177_);
                    leanh::lean_dec(v_r_3171_);
                    v___x_3180_ = leanh::lean_box(0);
                    v_isShared_3181_ = v_isSharedCheck_3192_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                v___x_3182_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_3181_ == 0 {
                    leanh::lean_ctor_set(v___x_3180_, 4, v_l_3135_);
                    leanh::lean_ctor_set(v___x_3180_, 3, v_l_3135_);
                    leanh::lean_ctor_set(v___x_3180_, 2, v_v_3173_);
                    leanh::lean_ctor_set(v___x_3180_, 1, v_k_3172_);
                    leanh::lean_ctor_set(v___x_3180_, 0, v___x_3044_);
                    v___x_3184_ = v___x_3180_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_3191_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3044_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3191_, 1, v_k_3172_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3191_, 2, v_v_3173_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3191_, 3, v_l_3135_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3191_, 4, v_l_3135_);
                    v___x_3184_ = v_reuseFailAlloc_3191_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                if v_isShared_3176_ == 0 {
                    leanh::lean_ctor_set(v___x_3175_, 4, v_l_3135_);
                    leanh::lean_ctor_set(v___x_3175_, 2, v_v_2551_);
                    leanh::lean_ctor_set(v___x_3175_, 1, v_k_2550_);
                    leanh::lean_ctor_set(v___x_3175_, 0, v___x_3044_);
                    v___x_3186_ = v___x_3175_;
                    state = 95;
                    continue;
                } else {
                    v_reuseFailAlloc_3190_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3044_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_k_2550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3190_, 2, v_v_2551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3190_, 3, v_l_3135_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3190_, 4, v_l_3135_);
                    v___x_3186_ = v_reuseFailAlloc_3190_;
                    state = 95;
                    continue;
                }
            }
            95 => {
                if v_isShared_2556_ == 0 {
                    leanh::lean_ctor_set(v___x_2555_, 4, v___x_3186_);
                    leanh::lean_ctor_set(v___x_2555_, 3, v___x_3184_);
                    leanh::lean_ctor_set(v___x_2555_, 2, v_v_3178_);
                    leanh::lean_ctor_set(v___x_2555_, 1, v_k_3177_);
                    leanh::lean_ctor_set(v___x_2555_, 0, v___x_3182_);
                    v___x_3188_ = v___x_2555_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_3189_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3182_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3189_, 1, v_k_3177_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3189_, 2, v_v_3178_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3189_, 3, v___x_3184_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3189_, 4, v___x_3186_);
                    v___x_3188_ = v_reuseFailAlloc_3189_;
                    state = 96;
                    continue;
                }
            }
            96 => {
                return v___x_3188_;
            }
            97 => {
                return v___x_3202_;
            }
            98 => {
                return v___x_3205_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg___boxed(
    mut v_k_3209_: *mut leanh::LeanObject,
    mut v_t_3210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3211_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(
        v_k_3209_, v_t_3210_,
    );
    leanh::lean_dec(v_k_3209_);
    return v_res_3211_;
}
pub unsafe fn l_Lean_Options_erase(
    mut v_o_3212_: *mut leanh::LeanObject,
    mut v_k_3213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3217_: u8 = 0;
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: u8 = 0;
    let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3214_ = leanh::lean_ctor_get(v_o_3212_, 0);
                v_isSharedCheck_3225_ = (!leanh::lean_is_exclusive(v_o_3212_)) as u8;
                if v_isSharedCheck_3225_ == 0 {
                    v___x_3216_ = v_o_3212_;
                    v_isShared_3217_ = v_isSharedCheck_3225_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_3214_);
                    leanh::lean_dec(v_o_3212_);
                    v___x_3216_ = leanh::lean_box(0);
                    v_isShared_3217_ = v_isSharedCheck_3225_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_map_3214_);
                v___x_3218_ =
                    l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(
                        v_k_3213_,
                        v_map_3214_,
                    );
                v___x_3219_ = leanh::lean_box(0);
                v___x_3220_ =
                    l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(
                        v___x_3219_,
                        v_map_3214_,
                    );
                leanh::lean_dec(v_map_3214_);
                v___x_3221_ = l_List_any___at___00Lean_Options_erase_spec__2(v___x_3220_);
                leanh::lean_dec(v___x_3220_);
                if v_isShared_3217_ == 0 {
                    leanh::lean_ctor_set(v___x_3216_, 0, v___x_3218_);
                    v___x_3223_ = v___x_3216_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3224_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3218_);
                    v___x_3223_ = v_reuseFailAlloc_3224_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3223_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3221_,
                );
                return v___x_3223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_erase___boxed(
    mut v_o_3226_: *mut leanh::LeanObject,
    mut v_k_3227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3228_ = l_Lean_Options_erase(v_o_3226_, v_k_3227_);
    leanh::lean_dec(v_k_3227_);
    return v_res_3228_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0(
    mut v_00_u03b2_3229_: *mut leanh::LeanObject,
    mut v_k_3230_: *mut leanh::LeanObject,
    mut v_t_3231_: *mut leanh::LeanObject,
    mut v_h_3232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3233_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(
        v_k_3230_, v_t_3231_,
    );
    return v___x_3233_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___boxed(
    mut v_00_u03b2_3234_: *mut leanh::LeanObject,
    mut v_k_3235_: *mut leanh::LeanObject,
    mut v_t_3236_: *mut leanh::LeanObject,
    mut v_h_3237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3238_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0(
        v_00_u03b2_3234_,
        v_k_3235_,
        v_t_3236_,
        v_h_3237_,
    );
    leanh::lean_dec(v_k_3235_);
    return v_res_3238_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(
    mut v_b_u2082_3239_: *mut leanh::LeanObject,
    mut v_f_3240_: *mut leanh::LeanObject,
    mut v_a_3241_: *mut leanh::LeanObject,
    mut v_x_3242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3247_: u8 = 0;
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3252_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3242_) == 0 {
                    leanh::lean_dec(v_a_3241_);
                    leanh::lean_dec_ref(v_f_3240_);
                    v___x_3243_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3243_, 0, v_b_u2082_3239_);
                    return v___x_3243_;
                } else {
                    v_val_3244_ = leanh::lean_ctor_get(v_x_3242_, 0);
                    v_isSharedCheck_3252_ = (!leanh::lean_is_exclusive(v_x_3242_)) as u8;
                    if v_isSharedCheck_3252_ == 0 {
                        v___x_3246_ = v_x_3242_;
                        v_isShared_3247_ = v_isSharedCheck_3252_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3244_);
                        leanh::lean_dec(v_x_3242_);
                        v___x_3246_ = leanh::lean_box(0);
                        v_isShared_3247_ = v_isSharedCheck_3252_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3248_ =
                    leanh::lean_apply_3(v_f_3240_, v_a_3241_, v_val_3244_, v_b_u2082_3239_);
                if v_isShared_3247_ == 0 {
                    leanh::lean_ctor_set(v___x_3246_, 0, v___x_3248_);
                    v___x_3250_ = v___x_3246_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3251_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
                    v___x_3250_ = v_reuseFailAlloc_3251_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(
    mut v_b_u2082_3253_: *mut leanh::LeanObject,
    mut v_f_3254_: *mut leanh::LeanObject,
    mut v_a_3255_: *mut leanh::LeanObject,
    mut v_k_3256_: *mut leanh::LeanObject,
    mut v_t_3257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3265_: u8 = 0;
    let mut v___x_3266_: u8 = 0;
    let mut v_impl_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3277_: u8 = 0;
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_3257_) == 0 {
                    v_size_3258_ = leanh::lean_ctor_get(v_t_3257_, 0);
                    v_k_3259_ = leanh::lean_ctor_get(v_t_3257_, 1);
                    v_v_3260_ = leanh::lean_ctor_get(v_t_3257_, 2);
                    v_l_3261_ = leanh::lean_ctor_get(v_t_3257_, 3);
                    v_r_3262_ = leanh::lean_ctor_get(v_t_3257_, 4);
                    v_isSharedCheck_3277_ = (!leanh::lean_is_exclusive(v_t_3257_)) as u8;
                    if v_isSharedCheck_3277_ == 0 {
                        v___x_3264_ = v_t_3257_;
                        v_isShared_3265_ = v_isSharedCheck_3277_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_3262_);
                        leanh::lean_inc(v_l_3261_);
                        leanh::lean_inc(v_v_3260_);
                        leanh::lean_inc(v_k_3259_);
                        leanh::lean_inc(v_size_3258_);
                        leanh::lean_dec(v_t_3257_);
                        v___x_3264_ = leanh::lean_box(0);
                        v_isShared_3265_ = v_isSharedCheck_3277_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3278_ = leanh::lean_box(0);
                    v___x_3279_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(v_b_u2082_3253_, v_f_3254_, v_a_3255_, v___x_3278_);
                    v_val_3280_ = leanh::lean_ctor_get(v___x_3279_, 0);
                    leanh::lean_inc(v_val_3280_);
                    leanh::lean_dec(v___x_3279_);
                    v___x_3281_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3282_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_3282_, 0, v___x_3281_);
                    leanh::lean_ctor_set(v___x_3282_, 1, v_k_3256_);
                    leanh::lean_ctor_set(v___x_3282_, 2, v_val_3280_);
                    leanh::lean_ctor_set(v___x_3282_, 3, v_t_3257_);
                    leanh::lean_ctor_set(v___x_3282_, 4, v_t_3257_);
                    return v___x_3282_;
                }
            }
            1 => {
                v___x_3266_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3256_, v_k_3259_);
                match v___x_3266_ {
                    0 => {
                        leanh::lean_del_object(v___x_3264_);
                        leanh::lean_dec(v_size_3258_);
                        v_impl_3267_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_b_u2082_3253_, v_f_3254_, v_a_3255_, v_k_3256_, v_l_3261_);
                        v___x_3268_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                            v_k_3259_,
                            v_v_3260_,
                            v_impl_3267_,
                            v_r_3262_,
                        );
                        return v___x_3268_;
                    }
                    1 => {
                        leanh::lean_dec(v_k_3259_);
                        v___x_3269_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3269_, 0, v_v_3260_);
                        v___x_3270_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(v_b_u2082_3253_, v_f_3254_, v_a_3255_, v___x_3269_);
                        v_val_3271_ = leanh::lean_ctor_get(v___x_3270_, 0);
                        leanh::lean_inc(v_val_3271_);
                        leanh::lean_dec(v___x_3270_);
                        if v_isShared_3265_ == 0 {
                            leanh::lean_ctor_set(v___x_3264_, 2, v_val_3271_);
                            leanh::lean_ctor_set(v___x_3264_, 1, v_k_3256_);
                            v___x_3273_ = v___x_3264_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3274_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_size_3258_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_k_3256_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3274_, 2, v_val_3271_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3274_, 3, v_l_3261_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3274_, 4, v_r_3262_);
                            v___x_3273_ = v_reuseFailAlloc_3274_;
                            state = 2;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_del_object(v___x_3264_);
                        leanh::lean_dec(v_size_3258_);
                        v_impl_3275_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_b_u2082_3253_, v_f_3254_, v_a_3255_, v_k_3256_, v_r_3262_);
                        v___x_3276_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                            v_k_3259_,
                            v_v_3260_,
                            v_l_3261_,
                            v_impl_3275_,
                        );
                        return v___x_3276_;
                    }
                }
            }
            2 => {
                return v___x_3273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(
    mut v_f_3283_: *mut leanh::LeanObject,
    mut v_init_3284_: *mut leanh::LeanObject,
    mut v_x_3285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3285_) == 0 {
                    v_k_3286_ = leanh::lean_ctor_get(v_x_3285_, 1);
                    leanh::lean_inc_n(v_k_3286_, 2);
                    v_v_3287_ = leanh::lean_ctor_get(v_x_3285_, 2);
                    leanh::lean_inc(v_v_3287_);
                    v_l_3288_ = leanh::lean_ctor_get(v_x_3285_, 3);
                    leanh::lean_inc(v_l_3288_);
                    v_r_3289_ = leanh::lean_ctor_get(v_x_3285_, 4);
                    leanh::lean_inc(v_r_3289_);
                    leanh::lean_dec_ref_known(v_x_3285_, 5);
                    leanh::lean_inc_ref_n(v_f_3283_, 2);
                    v___x_3290_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_3283_, v_init_3284_, v_l_3288_);
                    v___x_3291_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_v_3287_, v_f_3283_, v_k_3286_, v_k_3286_, v___x_3290_);
                    v_init_3284_ = v___x_3291_;
                    v_x_3285_ = v_r_3289_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_f_3283_);
                    return v_init_3284_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_mergeBy(
    mut v_f_3293_: *mut leanh::LeanObject,
    mut v_o1_3294_: *mut leanh::LeanObject,
    mut v_o2_3295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3297_: u8 = 0;
    let mut v_map_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3299_: u8 = 0;
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3302_: u8 = 0;
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3296_ = leanh::lean_ctor_get(v_o1_3294_, 0);
                leanh::lean_inc(v_map_3296_);
                v_hasTrace_3297_ = leanh::lean_ctor_get_uint8(
                    v_o1_3294_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_dec_ref(v_o1_3294_);
                v_map_3298_ = leanh::lean_ctor_get(v_o2_3295_, 0);
                v_hasTrace_3299_ = leanh::lean_ctor_get_uint8(
                    v_o2_3295_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3310_ = (!leanh::lean_is_exclusive(v_o2_3295_)) as u8;
                if v_isSharedCheck_3310_ == 0 {
                    v___x_3301_ = v_o2_3295_;
                    v_isShared_3302_ = v_isSharedCheck_3310_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_3298_);
                    leanh::lean_dec(v_o2_3295_);
                    v___x_3301_ = leanh::lean_box(0);
                    v_isShared_3302_ = v_isSharedCheck_3310_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3303_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_3293_, v_map_3296_, v_map_3298_);
                if v_hasTrace_3297_ == 0 {
                    if v_isShared_3302_ == 0 {
                        leanh::lean_ctor_set(v___x_3301_, 0, v___x_3303_);
                        v___x_3305_ = v___x_3301_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3306_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3303_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_3306_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_3299_,
                        );
                        v___x_3305_ = v_reuseFailAlloc_3306_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_3302_ == 0 {
                        leanh::lean_ctor_set(v___x_3301_, 0, v___x_3303_);
                        v___x_3308_ = v___x_3301_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3309_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3303_);
                        v___x_3308_ = v_reuseFailAlloc_3309_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3305_;
            }
            3 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3308_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_hasTrace_3297_,
                );
                return v___x_3308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0(
    mut v_b_u2082_3311_: *mut leanh::LeanObject,
    mut v_f_3312_: *mut leanh::LeanObject,
    mut v_a_3313_: *mut leanh::LeanObject,
    mut v_k_3314_: *mut leanh::LeanObject,
    mut v_t_3315_: *mut leanh::LeanObject,
    mut v_hl_3316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3317_ =
        l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(
            v_b_u2082_3311_,
            v_f_3312_,
            v_a_3313_,
            v_k_3314_,
            v_t_3315_,
        );
    return v___x_3317_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1(
    mut v_f_3318_: *mut leanh::LeanObject,
    mut v_init_3319_: *mut leanh::LeanObject,
    mut v_t_3320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3321_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_3318_, v_init_3319_, v_t_3320_);
    return v___x_3321_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3354_ = l_Lean_OptionDecl_declName___autoParam___closed__10;
    v___x_3355_ = l_Lean_mkAtom(v___x_3354_);
    return v___x_3355_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3356_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__12),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__12_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__12,
    );
    v___x_3357_ = l_Lean_OptionDecl_declName___autoParam___closed__5;
    v___x_3358_ = lean_array_push(v___x_3357_, v___x_3356_);
    return v___x_3358_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3367_ = l_Lean_OptionDecl_declName___autoParam___closed__17;
    v___x_3368_ = l_Lean_mkAtom(v___x_3367_);
    return v___x_3368_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3369_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__18),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__18_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__18,
    );
    v___x_3370_ = l_Lean_OptionDecl_declName___autoParam___closed__5;
    v___x_3371_ = lean_array_push(v___x_3370_, v___x_3369_);
    return v___x_3371_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3372_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__19),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__19_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__19,
    );
    v___x_3373_ = l_Lean_OptionDecl_declName___autoParam___closed__16;
    v___x_3374_ = leanh::lean_box(2);
    v___x_3375_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3375_, 0, v___x_3374_);
    leanh::lean_ctor_set(v___x_3375_, 1, v___x_3373_);
    leanh::lean_ctor_set(v___x_3375_, 2, v___x_3372_);
    return v___x_3375_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3376_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__20),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__20_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__20,
    );
    v___x_3377_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__13),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__13_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__13,
    );
    v___x_3378_ = lean_array_push(v___x_3377_, v___x_3376_);
    return v___x_3378_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3379_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__21),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__21_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__21,
    );
    v___x_3380_ = l_Lean_OptionDecl_declName___autoParam___closed__11;
    v___x_3381_ = leanh::lean_box(2);
    v___x_3382_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3382_, 0, v___x_3381_);
    leanh::lean_ctor_set(v___x_3382_, 1, v___x_3380_);
    leanh::lean_ctor_set(v___x_3382_, 2, v___x_3379_);
    return v___x_3382_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3383_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__22),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__22_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__22,
    );
    v___x_3384_ = l_Lean_OptionDecl_declName___autoParam___closed__5;
    v___x_3385_ = lean_array_push(v___x_3384_, v___x_3383_);
    return v___x_3385_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3386_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__23),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__23_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__23,
    );
    v___x_3387_ = l_Lean_OptionDecl_declName___autoParam___closed__9;
    v___x_3388_ = leanh::lean_box(2);
    v___x_3389_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3389_, 0, v___x_3388_);
    leanh::lean_ctor_set(v___x_3389_, 1, v___x_3387_);
    leanh::lean_ctor_set(v___x_3389_, 2, v___x_3386_);
    return v___x_3389_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3390_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__24),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__24_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__24,
    );
    v___x_3391_ = l_Lean_OptionDecl_declName___autoParam___closed__5;
    v___x_3392_ = lean_array_push(v___x_3391_, v___x_3390_);
    return v___x_3392_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3393_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__25),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__25_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__25,
    );
    v___x_3394_ = l_Lean_OptionDecl_declName___autoParam___closed__7;
    v___x_3395_ = leanh::lean_box(2);
    v___x_3396_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3396_, 0, v___x_3395_);
    leanh::lean_ctor_set(v___x_3396_, 1, v___x_3394_);
    leanh::lean_ctor_set(v___x_3396_, 2, v___x_3393_);
    return v___x_3396_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3397_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__26),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__26_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__26,
    );
    v___x_3398_ = l_Lean_OptionDecl_declName___autoParam___closed__5;
    v___x_3399_ = lean_array_push(v___x_3398_, v___x_3397_);
    return v___x_3399_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3400_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__27),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__27_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__27,
    );
    v___x_3401_ = l_Lean_OptionDecl_declName___autoParam___closed__4;
    v___x_3402_ = leanh::lean_box(2);
    v___x_3403_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3403_, 0, v___x_3402_);
    leanh::lean_ctor_set(v___x_3403_, 1, v___x_3401_);
    leanh::lean_ctor_set(v___x_3403_, 2, v___x_3400_);
    return v___x_3403_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam() -> *mut leanh::LeanObject {
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3404_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__28),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__28_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__28,
    );
    return v___x_3404_;
}
pub unsafe fn _init_l_Lean_instInhabitedOptionDecl_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3411_ = leanh::lean_box(0);
    v___x_3412_ = l_Lean_instInhabitedOptionDeprecation_default___closed__0;
    v___x_3413_ = l_Lean_instInhabitedDataValue_default;
    v___x_3414_ = l_Lean_instInhabitedOptionDecl_default___closed__2;
    v___x_3415_ = leanh::lean_box(0);
    v___x_3416_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3416_, 0, v___x_3415_);
    leanh::lean_ctor_set(v___x_3416_, 1, v___x_3414_);
    leanh::lean_ctor_set(v___x_3416_, 2, v___x_3413_);
    leanh::lean_ctor_set(v___x_3416_, 3, v___x_3412_);
    leanh::lean_ctor_set(v___x_3416_, 4, v___x_3411_);
    return v___x_3416_;
}
pub unsafe fn _init_l_Lean_instInhabitedOptionDecl_default() -> *mut leanh::LeanObject {
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3417_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedOptionDecl_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedOptionDecl_default___closed__3_once),
        _init_l_Lean_instInhabitedOptionDecl_default___closed__3,
    );
    return v___x_3417_;
}
pub unsafe fn _init_l_Lean_instInhabitedOptionDecl() -> *mut leanh::LeanObject {
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3418_ = l_Lean_instInhabitedOptionDecl_default;
    return v___x_3418_;
}
pub unsafe fn l_Lean_OptionDecl_fullDescr(
    mut v_self_3424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_descr_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: u8 = 0;
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: u8 = 0;
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3429_ = leanh::lean_ctor_get(v_self_3424_, 0);
                leanh::lean_inc(v_name_3429_);
                v_descr_3430_ = leanh::lean_ctor_get(v_self_3424_, 3);
                leanh::lean_inc_ref(v_descr_3430_);
                leanh::lean_dec_ref(v_self_3424_);
                v___x_3431_ = l_Lean_OptionDecl_fullDescr___closed__2;
                v___x_3432_ = l_Lean_Name_isPrefixOf(v___x_3431_, v_name_3429_);
                leanh::lean_dec(v_name_3429_);
                if v___x_3432_ == 0 {
                    return v_descr_3430_;
                } else {
                    v___x_3433_ = lean_string_utf8_byte_size(v_descr_3430_);
                    v___x_3434_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3435_ = lean_nat_dec_eq(v___x_3433_, v___x_3434_);
                    if v___x_3435_ == 0 {
                        v___x_3436_ = l_Lean_OptionDecl_fullDescr___closed__3;
                        v_descr_3437_ = lean_string_append(v_descr_3430_, v___x_3436_);
                        v_descr_3426_ = v_descr_3437_;
                        state = 1;
                        continue;
                    } else {
                        v_descr_3426_ = v_descr_3430_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3427_ = l_Lean_OptionDecl_fullDescr___closed__0;
                v_descr_3428_ = lean_string_append(v_descr_3426_, v___x_3427_);
                return v_descr_3428_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_instInhabitedOptionDecls() -> *mut leanh::LeanObject {
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3438_ = leanh::lean_box(1);
    return v___x_3438_;
}
pub unsafe fn l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3440_ = leanh::lean_box(1);
    v___x_3441_ = lean_st_mk_ref(v___x_3440_);
    v___x_3442_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3442_, 0, v___x_3441_);
    return v___x_3442_;
}
pub unsafe fn l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2____boxed(
    mut v_a_3443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3444_ = l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_();
    return v_res_3444_;
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Data_Options_0__Lean_OptionDecl_sameDecl_spec__0(
    mut v_x_3445_: *mut leanh::LeanObject,
    mut v_x_3446_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_3445_) == 0 {
        if leanh::lean_obj_tag(v_x_3446_) == 0 {
            let mut v___x_3447_: u8 = 0;
            v___x_3447_ = 1;
            return v___x_3447_;
        } else {
            let mut v___x_3448_: u8 = 0;
            v___x_3448_ = 0;
            return v___x_3448_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_3446_) == 0 {
            let mut v___x_3449_: u8 = 0;
            v___x_3449_ = 0;
            return v___x_3449_;
        } else {
            let mut v_val_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3452_: u8 = 0;
            v_val_3450_ = leanh::lean_ctor_get(v_x_3445_, 0);
            v_val_3451_ = leanh::lean_ctor_get(v_x_3446_, 0);
            v___x_3452_ = lean_string_dec_eq(v_val_3450_, v_val_3451_);
            return v___x_3452_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Data_Options_0__Lean_OptionDecl_sameDecl_spec__0___boxed(
    mut v_x_3453_: *mut leanh::LeanObject,
    mut v_x_3454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3455_: u8 = 0;
    let mut v_r_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3455_ = l_Option_instBEq_beq___at___00__private_Lean_Data_Options_0__Lean_OptionDecl_sameDecl_spec__0(v_x_3453_, v_x_3454_);
    leanh::lean_dec(v_x_3454_);
    leanh::lean_dec(v_x_3453_);
    v_r_3456_ = leanh::lean_box((v_res_3455_) as usize);
    return v_r_3456_;
}
pub unsafe fn l___private_Lean_Data_Options_0__Lean_OptionDecl_sameDecl(
    mut v_a_3457_: *mut leanh::LeanObject,
    mut v_b_3458_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3468_: u8 = 0;
    let mut v___x_3469_: u8 = 0;
    let mut v___x_3470_: u8 = 0;
    let mut v_val_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_since_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_since_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: u8 = 0;
    let mut v___x_3478_: u8 = 0;
    let mut v___x_3479_: u8 = 0;
    let mut v___x_3480_: u8 = 0;
    let mut v___x_3481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3459_ = leanh::lean_ctor_get(v_a_3457_, 0);
                leanh::lean_inc(v_name_3459_);
                v_defValue_3460_ = leanh::lean_ctor_get(v_a_3457_, 2);
                leanh::lean_inc_ref(v_defValue_3460_);
                v_descr_3461_ = leanh::lean_ctor_get(v_a_3457_, 3);
                leanh::lean_inc_ref(v_descr_3461_);
                v_deprecation_x3f_3462_ = leanh::lean_ctor_get(v_a_3457_, 4);
                leanh::lean_inc(v_deprecation_x3f_3462_);
                leanh::lean_dec_ref(v_a_3457_);
                v_name_3463_ = leanh::lean_ctor_get(v_b_3458_, 0);
                leanh::lean_inc(v_name_3463_);
                v_defValue_3464_ = leanh::lean_ctor_get(v_b_3458_, 2);
                leanh::lean_inc_ref(v_defValue_3464_);
                v_descr_3465_ = leanh::lean_ctor_get(v_b_3458_, 3);
                leanh::lean_inc_ref(v_descr_3465_);
                v_deprecation_x3f_3466_ = leanh::lean_ctor_get(v_b_3458_, 4);
                leanh::lean_inc(v_deprecation_x3f_3466_);
                leanh::lean_dec_ref(v_b_3458_);
                v___x_3480_ = lean_name_eq(v_name_3459_, v_name_3463_);
                leanh::lean_dec(v_name_3463_);
                leanh::lean_dec(v_name_3459_);
                if v___x_3480_ == 0 {
                    leanh::lean_dec_ref(v_defValue_3464_);
                    leanh::lean_dec_ref(v_defValue_3460_);
                    v___y_3468_ = v___x_3480_;
                    state = 1;
                    continue;
                } else {
                    v___x_3481_ = l_Lean_instBEqDataValue_beq(v_defValue_3460_, v_defValue_3464_);
                    v___y_3468_ = v___x_3481_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_3468_ == 0 {
                    leanh::lean_dec(v_deprecation_x3f_3466_);
                    leanh::lean_dec_ref(v_descr_3465_);
                    leanh::lean_dec(v_deprecation_x3f_3462_);
                    leanh::lean_dec_ref(v_descr_3461_);
                    return v___y_3468_;
                } else {
                    v___x_3469_ = lean_string_dec_eq(v_descr_3461_, v_descr_3465_);
                    leanh::lean_dec_ref(v_descr_3465_);
                    leanh::lean_dec_ref(v_descr_3461_);
                    if v___x_3469_ == 0 {
                        leanh::lean_dec(v_deprecation_x3f_3466_);
                        leanh::lean_dec(v_deprecation_x3f_3462_);
                        return v___x_3469_;
                    } else {
                        if leanh::lean_obj_tag(v_deprecation_x3f_3462_) == 0 {
                            if leanh::lean_obj_tag(v_deprecation_x3f_3466_) == 0 {
                                return v___x_3469_;
                            } else {
                                leanh::lean_dec(v_deprecation_x3f_3466_);
                                v___x_3470_ = 0;
                                return v___x_3470_;
                            }
                        } else {
                            if leanh::lean_obj_tag(v_deprecation_x3f_3466_) == 1 {
                                v_val_3471_ =
                                    leanh::lean_ctor_get(v_deprecation_x3f_3462_, 0);
                                leanh::lean_inc(v_val_3471_);
                                leanh::lean_dec_ref_known(v_deprecation_x3f_3462_, 1);
                                v_val_3472_ =
                                    leanh::lean_ctor_get(v_deprecation_x3f_3466_, 0);
                                leanh::lean_inc(v_val_3472_);
                                leanh::lean_dec_ref_known(v_deprecation_x3f_3466_, 1);
                                v_since_3473_ = leanh::lean_ctor_get(v_val_3471_, 0);
                                leanh::lean_inc_ref(v_since_3473_);
                                v_text_x3f_3474_ = leanh::lean_ctor_get(v_val_3471_, 1);
                                leanh::lean_inc(v_text_x3f_3474_);
                                leanh::lean_dec(v_val_3471_);
                                v_since_3475_ = leanh::lean_ctor_get(v_val_3472_, 0);
                                leanh::lean_inc_ref(v_since_3475_);
                                v_text_x3f_3476_ = leanh::lean_ctor_get(v_val_3472_, 1);
                                leanh::lean_inc(v_text_x3f_3476_);
                                leanh::lean_dec(v_val_3472_);
                                v___x_3477_ = lean_string_dec_eq(v_since_3473_, v_since_3475_);
                                leanh::lean_dec_ref(v_since_3475_);
                                leanh::lean_dec_ref(v_since_3473_);
                                if v___x_3477_ == 0 {
                                    leanh::lean_dec(v_text_x3f_3476_);
                                    leanh::lean_dec(v_text_x3f_3474_);
                                    return v___x_3477_;
                                } else {
                                    v___x_3478_ = l_Option_instBEq_beq___at___00__private_Lean_Data_Options_0__Lean_OptionDecl_sameDecl_spec__0(v_text_x3f_3474_, v_text_x3f_3476_);
                                    leanh::lean_dec(v_text_x3f_3476_);
                                    leanh::lean_dec(v_text_x3f_3474_);
                                    return v___x_3478_;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v_deprecation_x3f_3462_, 1);
                                leanh::lean_dec(v_deprecation_x3f_3466_);
                                v___x_3479_ = 0;
                                return v___x_3479_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Options_0__Lean_OptionDecl_sameDecl___boxed(
    mut v_a_3482_: *mut leanh::LeanObject,
    mut v_b_3483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3484_: u8 = 0;
    let mut v_r_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3484_ = l___private_Lean_Data_Options_0__Lean_OptionDecl_sameDecl(v_a_3482_, v_b_3483_);
    v_r_3485_ = leanh::lean_box((v_res_3484_) as usize);
    return v_r_3485_;
}
pub unsafe fn _init_l_Lean_registerOption___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3487_ = l_Lean_registerOption___closed__0;
    v___x_3488_ = lean_mk_io_user_error(v___x_3487_);
    return v___x_3488_;
}
pub unsafe fn lean_register_option(
    mut v_name_3491_: *mut leanh::LeanObject,
    mut v_decl_3492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v___x_3499_: u8 = 0;
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: u8 = 0;
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: u8 = 0;
    let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3528_: u8 = 0;
    let mut v_a_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3532_: u8 = 0;
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3536_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3494_ = l_Lean_initializing();
                if leanh::lean_obj_tag(v___x_3494_) == 0 {
                    v_a_3495_ = leanh::lean_ctor_get(v___x_3494_, 0);
                    v_isSharedCheck_3528_ = (!leanh::lean_is_exclusive(v___x_3494_)) as u8;
                    if v_isSharedCheck_3528_ == 0 {
                        v___x_3497_ = v___x_3494_;
                        v_isShared_3498_ = v_isSharedCheck_3528_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3495_);
                        leanh::lean_dec(v___x_3494_);
                        v___x_3497_ = leanh::lean_box(0);
                        v_isShared_3498_ = v_isSharedCheck_3528_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_decl_3492_);
                    leanh::lean_dec(v_name_3491_);
                    v_a_3529_ = leanh::lean_ctor_get(v___x_3494_, 0);
                    v_isSharedCheck_3536_ = (!leanh::lean_is_exclusive(v___x_3494_)) as u8;
                    if v_isSharedCheck_3536_ == 0 {
                        v___x_3531_ = v___x_3494_;
                        v_isShared_3532_ = v_isSharedCheck_3536_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3529_);
                        leanh::lean_dec(v___x_3494_);
                        v___x_3531_ = leanh::lean_box(0);
                        v_isShared_3532_ = v_isSharedCheck_3536_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3499_ = (leanh::lean_unbox(v_a_3495_) as u8);
                if v___x_3499_ == 0 {
                    leanh::lean_dec(v_a_3495_);
                    leanh::lean_dec_ref(v_decl_3492_);
                    leanh::lean_dec(v_name_3491_);
                    v___x_3500_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_registerOption___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_registerOption___closed__1_once),
                        _init_l_Lean_registerOption___closed__1,
                    );
                    if v_isShared_3498_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3497_, 1);
                        leanh::lean_ctor_set(v___x_3497_, 0, v___x_3500_);
                        v___x_3502_ = v___x_3497_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3503_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3500_);
                        v___x_3502_ = v_reuseFailAlloc_3503_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3504_ = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
                    v___x_3505_ = lean_st_ref_get(v___x_3504_);
                    v___x_3506_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3505_, v_name_3491_);
                    if leanh::lean_obj_tag(v___x_3506_) == 1 {
                        leanh::lean_dec(v___x_3505_);
                        v_val_3507_ = leanh::lean_ctor_get(v___x_3506_, 0);
                        leanh::lean_inc(v_val_3507_);
                        leanh::lean_dec_ref_known(v___x_3506_, 1);
                        v___x_3508_ = l___private_Lean_Data_Options_0__Lean_OptionDecl_sameDecl(
                            v_decl_3492_,
                            v_val_3507_,
                        );
                        if v___x_3508_ == 0 {
                            v___x_3509_ = l_Lean_registerOption___closed__2;
                            v___x_3510_ = (leanh::lean_unbox(v_a_3495_) as u8);
                            leanh::lean_dec(v_a_3495_);
                            v___x_3511_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_name_3491_,
                                    v___x_3510_,
                                );
                            v___x_3512_ = lean_string_append(v___x_3509_, v___x_3511_);
                            leanh::lean_dec_ref(v___x_3511_);
                            v___x_3513_ = l_Lean_registerOption___closed__3;
                            v___x_3514_ = lean_string_append(v___x_3512_, v___x_3513_);
                            v___x_3515_ = lean_mk_io_user_error(v___x_3514_);
                            if v_isShared_3498_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_3497_, 1);
                                leanh::lean_ctor_set(v___x_3497_, 0, v___x_3515_);
                                v___x_3517_ = v___x_3497_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3518_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3515_);
                                v___x_3517_ = v_reuseFailAlloc_3518_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3495_);
                            leanh::lean_dec(v_name_3491_);
                            v___x_3519_ = leanh::lean_box(0);
                            if v_isShared_3498_ == 0 {
                                leanh::lean_ctor_set(v___x_3497_, 0, v___x_3519_);
                                v___x_3521_ = v___x_3497_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_3522_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3522_, 0, v___x_3519_);
                                v___x_3521_ = v_reuseFailAlloc_3522_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_3506_);
                        leanh::lean_dec(v_a_3495_);
                        v___x_3523_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_3491_, v_decl_3492_, v___x_3505_);
                        v___x_3524_ = lean_st_ref_set(v___x_3504_, v___x_3523_);
                        if v_isShared_3498_ == 0 {
                            leanh::lean_ctor_set(v___x_3497_, 0, v___x_3524_);
                            v___x_3526_ = v___x_3497_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3527_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
                            v___x_3526_ = v_reuseFailAlloc_3527_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3502_;
            }
            3 => {
                return v___x_3517_;
            }
            4 => {
                return v___x_3521_;
            }
            5 => {
                return v___x_3526_;
            }
            6 => {
                if v_isShared_3532_ == 0 {
                    v___x_3534_ = v___x_3531_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3535_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
                    v___x_3534_ = v_reuseFailAlloc_3535_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3534_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_registerOption___boxed(
    mut v_name_3537_: *mut leanh::LeanObject,
    mut v_decl_3538_: *mut leanh::LeanObject,
    mut v_a_3539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3540_ = lean_register_option(v_name_3537_, v_decl_3538_);
    return v_res_3540_;
}
pub unsafe fn l_Lean_getOptionDecls() -> *mut leanh::LeanObject {
    let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3542_ = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
    v___x_3543_ = lean_st_ref_get(v___x_3542_);
    v___x_3544_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3544_, 0, v___x_3543_);
    return v___x_3544_;
}
pub unsafe fn l_Lean_getOptionDecls___boxed(
    mut v_a_3545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3546_ = l_Lean_getOptionDecls();
    return v_res_3546_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(
    mut v_init_3547_: *mut leanh::LeanObject,
    mut v_x_3548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3548_) == 0 {
                    v_k_3549_ = leanh::lean_ctor_get(v_x_3548_, 1);
                    v_v_3550_ = leanh::lean_ctor_get(v_x_3548_, 2);
                    v_l_3551_ = leanh::lean_ctor_get(v_x_3548_, 3);
                    v_r_3552_ = leanh::lean_ctor_get(v_x_3548_, 4);
                    v___x_3553_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_3547_, v_l_3551_);
                    leanh::lean_inc(v_v_3550_);
                    leanh::lean_inc(v_k_3549_);
                    v___x_3554_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3554_, 0, v_k_3549_);
                    leanh::lean_ctor_set(v___x_3554_, 1, v_v_3550_);
                    v___x_3555_ = lean_array_push(v___x_3553_, v___x_3554_);
                    v_init_3547_ = v___x_3555_;
                    v_x_3548_ = v_r_3552_;
                    state = 0;
                    continue;
                } else {
                    return v_init_3547_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0___boxed(
    mut v_init_3557_: *mut leanh::LeanObject,
    mut v_x_3558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3559_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_3557_, v_x_3558_);
    leanh::lean_dec(v_x_3558_);
    return v_res_3559_;
}
pub unsafe fn lean_get_option_decls_array() -> *mut leanh::LeanObject {
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3567_: u8 = 0;
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3573_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3563_ = l_Lean_getOptionDecls();
                v_a_3564_ = leanh::lean_ctor_get(v___x_3563_, 0);
                v_isSharedCheck_3573_ = (!leanh::lean_is_exclusive(v___x_3563_)) as u8;
                if v_isSharedCheck_3573_ == 0 {
                    v___x_3566_ = v___x_3563_;
                    v_isShared_3567_ = v_isSharedCheck_3573_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3564_);
                    leanh::lean_dec(v___x_3563_);
                    v___x_3566_ = leanh::lean_box(0);
                    v_isShared_3567_ = v_isSharedCheck_3573_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3568_ = l_Lean_getOptionDeclsArray___closed__0;
                v___x_3569_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v___x_3568_, v_a_3564_);
                leanh::lean_dec(v_a_3564_);
                if v_isShared_3567_ == 0 {
                    leanh::lean_ctor_set(v___x_3566_, 0, v___x_3569_);
                    v___x_3571_ = v___x_3566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3572_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3569_);
                    v___x_3571_ = v_reuseFailAlloc_3572_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3571_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getOptionDeclsArray___boxed(
    mut v_a_3574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3575_ = lean_get_option_decls_array();
    return v_res_3575_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(
    mut v_init_3576_: *mut leanh::LeanObject,
    mut v_t_3577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3578_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_3576_, v_t_3577_);
    return v___x_3578_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0___boxed(
    mut v_init_3579_: *mut leanh::LeanObject,
    mut v_t_3580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3581_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(
        v_init_3579_,
        v_t_3580_,
    );
    leanh::lean_dec(v_t_3580_);
    return v_res_3581_;
}
pub unsafe fn l_Lean_getOptionDecl(
    mut v_name_3584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3590_: u8 = 0;
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: u8 = 0;
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3586_ = l_Lean_getOptionDecls();
                v_a_3587_ = leanh::lean_ctor_get(v___x_3586_, 0);
                v_isSharedCheck_3606_ = (!leanh::lean_is_exclusive(v___x_3586_)) as u8;
                if v_isSharedCheck_3606_ == 0 {
                    v___x_3589_ = v___x_3586_;
                    v_isShared_3590_ = v_isSharedCheck_3606_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3587_);
                    leanh::lean_dec(v___x_3586_);
                    v___x_3589_ = leanh::lean_box(0);
                    v_isShared_3590_ = v_isSharedCheck_3606_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3591_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_3587_, v_name_3584_);
                leanh::lean_dec(v_a_3587_);
                if leanh::lean_obj_tag(v___x_3591_) == 1 {
                    leanh::lean_dec(v_name_3584_);
                    v_val_3592_ = leanh::lean_ctor_get(v___x_3591_, 0);
                    leanh::lean_inc(v_val_3592_);
                    leanh::lean_dec_ref_known(v___x_3591_, 1);
                    if v_isShared_3590_ == 0 {
                        leanh::lean_ctor_set(v___x_3589_, 0, v_val_3592_);
                        v___x_3594_ = v___x_3589_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3595_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_val_3592_);
                        v___x_3594_ = v_reuseFailAlloc_3595_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3591_);
                    v___x_3596_ = l_Lean_getOptionDecl___closed__0;
                    v___x_3597_ = 1;
                    v___x_3598_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_3584_,
                        v___x_3597_,
                    );
                    v___x_3599_ = lean_string_append(v___x_3596_, v___x_3598_);
                    leanh::lean_dec_ref(v___x_3598_);
                    v___x_3600_ = l_Lean_getOptionDecl___closed__1;
                    v___x_3601_ = lean_string_append(v___x_3599_, v___x_3600_);
                    v___x_3602_ = lean_mk_io_user_error(v___x_3601_);
                    if v_isShared_3590_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3589_, 1);
                        leanh::lean_ctor_set(v___x_3589_, 0, v___x_3602_);
                        v___x_3604_ = v___x_3589_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3605_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3602_);
                        v___x_3604_ = v_reuseFailAlloc_3605_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3594_;
            }
            3 => {
                return v___x_3604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getOptionDecl___boxed(
    mut v_name_3607_: *mut leanh::LeanObject,
    mut v_a_3608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3609_ = l_Lean_getOptionDecl(v_name_3607_);
    return v_res_3609_;
}
pub unsafe fn l_Lean_getOptionDefaultValue(
    mut v_name_3610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3616_: u8 = 0;
    let mut v_defValue_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3621_: u8 = 0;
    let mut v_a_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3625_: u8 = 0;
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3629_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3612_ = l_Lean_getOptionDecl(v_name_3610_);
                if leanh::lean_obj_tag(v___x_3612_) == 0 {
                    v_a_3613_ = leanh::lean_ctor_get(v___x_3612_, 0);
                    v_isSharedCheck_3621_ = (!leanh::lean_is_exclusive(v___x_3612_)) as u8;
                    if v_isSharedCheck_3621_ == 0 {
                        v___x_3615_ = v___x_3612_;
                        v_isShared_3616_ = v_isSharedCheck_3621_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3613_);
                        leanh::lean_dec(v___x_3612_);
                        v___x_3615_ = leanh::lean_box(0);
                        v_isShared_3616_ = v_isSharedCheck_3621_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3622_ = leanh::lean_ctor_get(v___x_3612_, 0);
                    v_isSharedCheck_3629_ = (!leanh::lean_is_exclusive(v___x_3612_)) as u8;
                    if v_isSharedCheck_3629_ == 0 {
                        v___x_3624_ = v___x_3612_;
                        v_isShared_3625_ = v_isSharedCheck_3629_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3622_);
                        leanh::lean_dec(v___x_3612_);
                        v___x_3624_ = leanh::lean_box(0);
                        v_isShared_3625_ = v_isSharedCheck_3629_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_defValue_3617_ = leanh::lean_ctor_get(v_a_3613_, 2);
                leanh::lean_inc_ref(v_defValue_3617_);
                leanh::lean_dec(v_a_3613_);
                if v_isShared_3616_ == 0 {
                    leanh::lean_ctor_set(v___x_3615_, 0, v_defValue_3617_);
                    v___x_3619_ = v___x_3615_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3620_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_defValue_3617_);
                    v___x_3619_ = v_reuseFailAlloc_3620_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3619_;
            }
            3 => {
                if v_isShared_3625_ == 0 {
                    v___x_3627_ = v___x_3624_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3628_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
                    v___x_3627_ = v_reuseFailAlloc_3628_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3627_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getOptionDefaultValue___boxed(
    mut v_name_3630_: *mut leanh::LeanObject,
    mut v_a_3631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3632_ = l_Lean_getOptionDefaultValue(v_name_3630_);
    return v_res_3632_;
}
pub unsafe fn l_Lean_getOptionDescr(
    mut v_name_3633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3639_: u8 = 0;
    let mut v_descr_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3644_: u8 = 0;
    let mut v_a_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3648_: u8 = 0;
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3652_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3635_ = l_Lean_getOptionDecl(v_name_3633_);
                if leanh::lean_obj_tag(v___x_3635_) == 0 {
                    v_a_3636_ = leanh::lean_ctor_get(v___x_3635_, 0);
                    v_isSharedCheck_3644_ = (!leanh::lean_is_exclusive(v___x_3635_)) as u8;
                    if v_isSharedCheck_3644_ == 0 {
                        v___x_3638_ = v___x_3635_;
                        v_isShared_3639_ = v_isSharedCheck_3644_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3636_);
                        leanh::lean_dec(v___x_3635_);
                        v___x_3638_ = leanh::lean_box(0);
                        v_isShared_3639_ = v_isSharedCheck_3644_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3645_ = leanh::lean_ctor_get(v___x_3635_, 0);
                    v_isSharedCheck_3652_ = (!leanh::lean_is_exclusive(v___x_3635_)) as u8;
                    if v_isSharedCheck_3652_ == 0 {
                        v___x_3647_ = v___x_3635_;
                        v_isShared_3648_ = v_isSharedCheck_3652_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3645_);
                        leanh::lean_dec(v___x_3635_);
                        v___x_3647_ = leanh::lean_box(0);
                        v_isShared_3648_ = v_isSharedCheck_3652_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_descr_3640_ = leanh::lean_ctor_get(v_a_3636_, 3);
                leanh::lean_inc_ref(v_descr_3640_);
                leanh::lean_dec(v_a_3636_);
                if v_isShared_3639_ == 0 {
                    leanh::lean_ctor_set(v___x_3638_, 0, v_descr_3640_);
                    v___x_3642_ = v___x_3638_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3643_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_descr_3640_);
                    v___x_3642_ = v_reuseFailAlloc_3643_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3642_;
            }
            3 => {
                if v_isShared_3648_ == 0 {
                    v___x_3650_ = v___x_3647_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3651_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
                    v___x_3650_ = v_reuseFailAlloc_3651_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3650_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getOptionDescr___boxed(
    mut v_name_3653_: *mut leanh::LeanObject,
    mut v_a_3654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3655_ = l_Lean_getOptionDescr(v_name_3653_);
    return v_res_3655_;
}
pub unsafe fn l_Lean_instMonadOptionsOfMonadLift___redArg(
    mut v_inst_3656_: *mut leanh::LeanObject,
    mut v_inst_3657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3658_ = leanh::lean_apply_2(v_inst_3656_, leanh::lean_box(0), v_inst_3657_);
    return v___x_3658_;
}
pub unsafe fn l_Lean_instMonadOptionsOfMonadLift(
    mut v_m_3659_: *mut leanh::LeanObject,
    mut v_n_3660_: *mut leanh::LeanObject,
    mut v_inst_3661_: *mut leanh::LeanObject,
    mut v_inst_3662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3663_ = leanh::lean_apply_2(v_inst_3661_, leanh::lean_box(0), v_inst_3662_);
    return v___x_3663_;
}
pub unsafe fn l_Lean_getBoolOption___redArg___lam__0(
    mut v_k_3664_: *mut leanh::LeanObject,
    mut v_toPure_3665_: *mut leanh::LeanObject,
    mut v_defValue_3666_: u8,
    mut v_opts_3667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_3668_ = leanh::lean_ctor_get(v_opts_3667_, 0);
    v___x_3669_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3668_,
            v_k_3664_,
        );
    if leanh::lean_obj_tag(v___x_3669_) == 0 {
        let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3670_ = leanh::lean_box((v_defValue_3666_) as usize);
        v___x_3671_ =
            leanh::lean_apply_2(v_toPure_3665_, leanh::lean_box(0), v___x_3670_);
        return v___x_3671_;
    } else {
        let mut v_val_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3672_ = leanh::lean_ctor_get(v___x_3669_, 0);
        leanh::lean_inc(v_val_3672_);
        leanh::lean_dec_ref_known(v___x_3669_, 1);
        if leanh::lean_obj_tag(v_val_3672_) == 1 {
            let mut v_v_3673_: u8 = 0;
            let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_3673_ = leanh::lean_ctor_get_uint8(v_val_3672_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_3672_, 0);
            v___x_3674_ = leanh::lean_box((v_v_3673_) as usize);
            v___x_3675_ =
                leanh::lean_apply_2(v_toPure_3665_, leanh::lean_box(0), v___x_3674_);
            return v___x_3675_;
        } else {
            let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_val_3672_);
            v___x_3676_ = leanh::lean_box((v_defValue_3666_) as usize);
            v___x_3677_ =
                leanh::lean_apply_2(v_toPure_3665_, leanh::lean_box(0), v___x_3676_);
            return v___x_3677_;
        }
    }
}
pub unsafe fn l_Lean_getBoolOption___redArg___lam__0___boxed(
    mut v_k_3678_: *mut leanh::LeanObject,
    mut v_toPure_3679_: *mut leanh::LeanObject,
    mut v_defValue_3680_: *mut leanh::LeanObject,
    mut v_opts_3681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_boxed_3682_: u8 = 0;
    let mut v_res_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_defValue_boxed_3682_ = (leanh::lean_unbox(v_defValue_3680_) as u8);
    v_res_3683_ = l_Lean_getBoolOption___redArg___lam__0(
        v_k_3678_,
        v_toPure_3679_,
        v_defValue_boxed_3682_,
        v_opts_3681_,
    );
    leanh::lean_dec_ref(v_opts_3681_);
    leanh::lean_dec(v_k_3678_);
    return v_res_3683_;
}
pub unsafe fn l_Lean_getBoolOption___redArg(
    mut v_inst_3684_: *mut leanh::LeanObject,
    mut v_inst_3685_: *mut leanh::LeanObject,
    mut v_k_3686_: *mut leanh::LeanObject,
    mut v_defValue_3687_: u8,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3688_ = leanh::lean_ctor_get(v_inst_3684_, 0);
    leanh::lean_inc_ref(v_toApplicative_3688_);
    v_toBind_3689_ = leanh::lean_ctor_get(v_inst_3684_, 1);
    leanh::lean_inc(v_toBind_3689_);
    leanh::lean_dec_ref(v_inst_3684_);
    v_toPure_3690_ = leanh::lean_ctor_get(v_toApplicative_3688_, 1);
    leanh::lean_inc(v_toPure_3690_);
    leanh::lean_dec_ref(v_toApplicative_3688_);
    v___x_3691_ = leanh::lean_box((v_defValue_3687_) as usize);
    v___f_3692_ = leanh::lean_alloc_closure(
        l_Lean_getBoolOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_3692_, 0, v_k_3686_);
    leanh::lean_closure_set(v___f_3692_, 1, v_toPure_3690_);
    leanh::lean_closure_set(v___f_3692_, 2, v___x_3691_);
    v___x_3693_ = leanh::lean_apply_4(
        v_toBind_3689_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_3685_,
        v___f_3692_,
    );
    return v___x_3693_;
}
pub unsafe fn l_Lean_getBoolOption___redArg___boxed(
    mut v_inst_3694_: *mut leanh::LeanObject,
    mut v_inst_3695_: *mut leanh::LeanObject,
    mut v_k_3696_: *mut leanh::LeanObject,
    mut v_defValue_3697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_boxed_3698_: u8 = 0;
    let mut v_res_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_defValue_boxed_3698_ = (leanh::lean_unbox(v_defValue_3697_) as u8);
    v_res_3699_ = l_Lean_getBoolOption___redArg(
        v_inst_3694_,
        v_inst_3695_,
        v_k_3696_,
        v_defValue_boxed_3698_,
    );
    return v_res_3699_;
}
pub unsafe fn l_Lean_getBoolOption(
    mut v_m_3700_: *mut leanh::LeanObject,
    mut v_inst_3701_: *mut leanh::LeanObject,
    mut v_inst_3702_: *mut leanh::LeanObject,
    mut v_k_3703_: *mut leanh::LeanObject,
    mut v_defValue_3704_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3705_ =
        l_Lean_getBoolOption___redArg(v_inst_3701_, v_inst_3702_, v_k_3703_, v_defValue_3704_);
    return v___x_3705_;
}
pub unsafe fn l_Lean_getBoolOption___boxed(
    mut v_m_3706_: *mut leanh::LeanObject,
    mut v_inst_3707_: *mut leanh::LeanObject,
    mut v_inst_3708_: *mut leanh::LeanObject,
    mut v_k_3709_: *mut leanh::LeanObject,
    mut v_defValue_3710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_boxed_3711_: u8 = 0;
    let mut v_res_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_defValue_boxed_3711_ = (leanh::lean_unbox(v_defValue_3710_) as u8);
    v_res_3712_ = l_Lean_getBoolOption(
        v_m_3706_,
        v_inst_3707_,
        v_inst_3708_,
        v_k_3709_,
        v_defValue_boxed_3711_,
    );
    return v_res_3712_;
}
pub unsafe fn l_Lean_getNatOption___redArg___lam__0(
    mut v_k_3713_: *mut leanh::LeanObject,
    mut v_toPure_3714_: *mut leanh::LeanObject,
    mut v_defValue_3715_: *mut leanh::LeanObject,
    mut v_opts_3716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_3717_ = leanh::lean_ctor_get(v_opts_3716_, 0);
    v___x_3718_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3717_,
            v_k_3713_,
        );
    if leanh::lean_obj_tag(v___x_3718_) == 0 {
        let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3719_ =
            leanh::lean_apply_2(v_toPure_3714_, leanh::lean_box(0), v_defValue_3715_);
        return v___x_3719_;
    } else {
        let mut v_val_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3720_ = leanh::lean_ctor_get(v___x_3718_, 0);
        leanh::lean_inc(v_val_3720_);
        leanh::lean_dec_ref_known(v___x_3718_, 1);
        if leanh::lean_obj_tag(v_val_3720_) == 3 {
            let mut v_v_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_defValue_3715_);
            v_v_3721_ = leanh::lean_ctor_get(v_val_3720_, 0);
            leanh::lean_inc(v_v_3721_);
            leanh::lean_dec_ref_known(v_val_3720_, 1);
            v___x_3722_ =
                leanh::lean_apply_2(v_toPure_3714_, leanh::lean_box(0), v_v_3721_);
            return v___x_3722_;
        } else {
            let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_val_3720_);
            v___x_3723_ = leanh::lean_apply_2(
                v_toPure_3714_,
                leanh::lean_box(0),
                v_defValue_3715_,
            );
            return v___x_3723_;
        }
    }
}
pub unsafe fn l_Lean_getNatOption___redArg___lam__0___boxed(
    mut v_k_3724_: *mut leanh::LeanObject,
    mut v_toPure_3725_: *mut leanh::LeanObject,
    mut v_defValue_3726_: *mut leanh::LeanObject,
    mut v_opts_3727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3728_ = l_Lean_getNatOption___redArg___lam__0(
        v_k_3724_,
        v_toPure_3725_,
        v_defValue_3726_,
        v_opts_3727_,
    );
    leanh::lean_dec_ref(v_opts_3727_);
    leanh::lean_dec(v_k_3724_);
    return v_res_3728_;
}
pub unsafe fn l_Lean_getNatOption___redArg(
    mut v_inst_3729_: *mut leanh::LeanObject,
    mut v_inst_3730_: *mut leanh::LeanObject,
    mut v_k_3731_: *mut leanh::LeanObject,
    mut v_defValue_3732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3733_ = leanh::lean_ctor_get(v_inst_3729_, 0);
    leanh::lean_inc_ref(v_toApplicative_3733_);
    v_toBind_3734_ = leanh::lean_ctor_get(v_inst_3729_, 1);
    leanh::lean_inc(v_toBind_3734_);
    leanh::lean_dec_ref(v_inst_3729_);
    v_toPure_3735_ = leanh::lean_ctor_get(v_toApplicative_3733_, 1);
    leanh::lean_inc(v_toPure_3735_);
    leanh::lean_dec_ref(v_toApplicative_3733_);
    v___f_3736_ = leanh::lean_alloc_closure(
        l_Lean_getNatOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_3736_, 0, v_k_3731_);
    leanh::lean_closure_set(v___f_3736_, 1, v_toPure_3735_);
    leanh::lean_closure_set(v___f_3736_, 2, v_defValue_3732_);
    v___x_3737_ = leanh::lean_apply_4(
        v_toBind_3734_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_3730_,
        v___f_3736_,
    );
    return v___x_3737_;
}
pub unsafe fn l_Lean_getNatOption(
    mut v_m_3738_: *mut leanh::LeanObject,
    mut v_inst_3739_: *mut leanh::LeanObject,
    mut v_inst_3740_: *mut leanh::LeanObject,
    mut v_k_3741_: *mut leanh::LeanObject,
    mut v_defValue_3742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3743_ =
        l_Lean_getNatOption___redArg(v_inst_3739_, v_inst_3740_, v_k_3741_, v_defValue_3742_);
    return v___x_3743_;
}
pub unsafe fn l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0(
    mut v_inst_3744_: *mut leanh::LeanObject,
    mut v_f_3745_: *mut leanh::LeanObject,
    mut v_00_u03b2_3746_: *mut leanh::LeanObject,
    mut v___y_3747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3748_ = leanh::lean_apply_3(
        v_inst_3744_,
        leanh::lean_box(0),
        v_f_3745_,
        v___y_3747_,
    );
    return v___x_3748_;
}
pub unsafe fn l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1(
    mut v_inst_3749_: *mut leanh::LeanObject,
    mut v_inst_3750_: *mut leanh::LeanObject,
    mut v_00_u03b1_3751_: *mut leanh::LeanObject,
    mut v_f_3752_: *mut leanh::LeanObject,
    mut v_x_3753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3754_ = leanh::lean_alloc_closure(
        l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_3754_, 0, v_inst_3749_);
    leanh::lean_closure_set(v___f_3754_, 1, v_f_3752_);
    v___x_3755_ = leanh::lean_apply_3(
        v_inst_3750_,
        leanh::lean_box(0),
        v___f_3754_,
        v_x_3753_,
    );
    return v___x_3755_;
}
pub unsafe fn l_Lean_instMonadWithOptionsOfMonadFunctor___redArg(
    mut v_inst_3756_: *mut leanh::LeanObject,
    mut v_inst_3757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3758_ = leanh::lean_alloc_closure(
        l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3758_, 0, v_inst_3757_);
    leanh::lean_closure_set(v___f_3758_, 1, v_inst_3756_);
    return v___f_3758_;
}
pub unsafe fn l_Lean_instMonadWithOptionsOfMonadFunctor(
    mut v_m_3759_: *mut leanh::LeanObject,
    mut v_n_3760_: *mut leanh::LeanObject,
    mut v_inst_3761_: *mut leanh::LeanObject,
    mut v_inst_3762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3763_ = leanh::lean_alloc_closure(
        l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3763_, 0, v_inst_3762_);
    leanh::lean_closure_set(v___f_3763_, 1, v_inst_3761_);
    return v___f_3763_;
}
pub unsafe fn l_Lean_withInPattern___redArg___lam__0(
    mut v___x_3767_: *mut leanh::LeanObject,
    mut v_o_3768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: u8 = 0;
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3769_ = l_Lean_withInPattern___redArg___lam__0___closed__1;
    v___x_3770_ = 1;
    v___x_3771_ = leanh::lean_box((v___x_3770_) as usize);
    v___x_3772_ = l_Lean_Options_set___redArg(v___x_3767_, v_o_3768_, v___x_3769_, v___x_3771_);
    return v___x_3772_;
}
pub unsafe fn _init_l_Lean_withInPattern___redArg___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3773_ = l_Lean_KVMap_instValueBool;
    v___f_3774_ = leanh::lean_alloc_closure(
        l_Lean_withInPattern___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3774_, 0, v___x_3773_);
    return v___f_3774_;
}
pub unsafe fn l_Lean_withInPattern___redArg(
    mut v_inst_3775_: *mut leanh::LeanObject,
    mut v_x_3776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3777_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_withInPattern___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_withInPattern___redArg___closed__0_once),
        _init_l_Lean_withInPattern___redArg___closed__0,
    );
    v___x_3778_ = leanh::lean_apply_3(
        v_inst_3775_,
        leanh::lean_box(0),
        v___f_3777_,
        v_x_3776_,
    );
    return v___x_3778_;
}
pub unsafe fn l_Lean_withInPattern(
    mut v_m_3779_: *mut leanh::LeanObject,
    mut v_00_u03b1_3780_: *mut leanh::LeanObject,
    mut v_inst_3781_: *mut leanh::LeanObject,
    mut v_x_3782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3783_ = l_Lean_withInPattern___redArg(v_inst_3781_, v_x_3782_);
    return v___x_3783_;
}
pub unsafe fn l_Lean_Options_getInPattern(mut v_o_3784_: *mut leanh::LeanObject) -> u8 {
    let mut v_map_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: u8 = 0;
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_3785_ = leanh::lean_ctor_get(v_o_3784_, 0);
    v___x_3786_ = l_Lean_withInPattern___redArg___lam__0___closed__1;
    v___x_3787_ = 0;
    v___x_3788_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3785_,
            v___x_3786_,
        );
    if leanh::lean_obj_tag(v___x_3788_) == 0 {
        return v___x_3787_;
    } else {
        let mut v_val_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3789_ = leanh::lean_ctor_get(v___x_3788_, 0);
        leanh::lean_inc(v_val_3789_);
        leanh::lean_dec_ref_known(v___x_3788_, 1);
        if leanh::lean_obj_tag(v_val_3789_) == 1 {
            let mut v_v_3790_: u8 = 0;
            v_v_3790_ = leanh::lean_ctor_get_uint8(v_val_3789_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_3789_, 0);
            return v_v_3790_;
        } else {
            leanh::lean_dec(v_val_3789_);
            return v___x_3787_;
        }
    }
}
pub unsafe fn l_Lean_Options_getInPattern___boxed(
    mut v_o_3791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3792_: u8 = 0;
    let mut v_r_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3792_ = l_Lean_Options_getInPattern(v_o_3791_);
    leanh::lean_dec_ref(v_o_3791_);
    v_r_3793_ = leanh::lean_box((v_res_3792_) as usize);
    return v_r_3793_;
}
pub unsafe fn l_Lean_instInhabitedOption_default___redArg(
    mut v_inst_3794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3795_ = leanh::lean_box(0);
    v___x_3796_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3796_, 0, v___x_3795_);
    leanh::lean_ctor_set(v___x_3796_, 1, v_inst_3794_);
    return v___x_3796_;
}
pub unsafe fn l_Lean_instInhabitedOption_default(
    mut v_00_u03b1_3797_: *mut leanh::LeanObject,
    mut v_inst_3798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3799_ = l_Lean_instInhabitedOption_default___redArg(v_inst_3798_);
    return v___x_3799_;
}
pub unsafe fn l_Lean_instInhabitedOption___redArg(
    mut v_inst_3800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3801_ = l_Lean_instInhabitedOption_default___redArg(v_inst_3800_);
    return v___x_3801_;
}
pub unsafe fn l_Lean_instInhabitedOption(
    mut v_a_3802_: *mut leanh::LeanObject,
    mut v_inst_3803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3804_ = l_Lean_instInhabitedOption_default___redArg(v_inst_3803_);
    return v___x_3804_;
}
pub unsafe fn l_Lean_Option_get_x3f___redArg(
    mut v_inst_3805_: *mut leanh::LeanObject,
    mut v_opts_3806_: *mut leanh::LeanObject,
    mut v_opt_3807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofDataValue_x3f_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_3808_ = leanh::lean_ctor_get(v_opt_3807_, 0);
    v_map_3809_ = leanh::lean_ctor_get(v_opts_3806_, 0);
    v_ofDataValue_x3f_3810_ = leanh::lean_ctor_get(v_inst_3805_, 1);
    leanh::lean_inc_ref(v_ofDataValue_x3f_3810_);
    leanh::lean_dec_ref(v_inst_3805_);
    v___x_3811_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3809_,
            v_name_3808_,
        );
    if leanh::lean_obj_tag(v___x_3811_) == 0 {
        let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_ofDataValue_x3f_3810_);
        v___x_3812_ = leanh::lean_box(0);
        return v___x_3812_;
    } else {
        let mut v_val_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3813_ = leanh::lean_ctor_get(v___x_3811_, 0);
        leanh::lean_inc(v_val_3813_);
        leanh::lean_dec_ref_known(v___x_3811_, 1);
        v___x_3814_ = leanh::lean_apply_1(v_ofDataValue_x3f_3810_, v_val_3813_);
        return v___x_3814_;
    }
}
pub unsafe fn l_Lean_Option_get_x3f___redArg___boxed(
    mut v_inst_3815_: *mut leanh::LeanObject,
    mut v_opts_3816_: *mut leanh::LeanObject,
    mut v_opt_3817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3818_ = l_Lean_Option_get_x3f___redArg(v_inst_3815_, v_opts_3816_, v_opt_3817_);
    leanh::lean_dec_ref(v_opt_3817_);
    leanh::lean_dec_ref(v_opts_3816_);
    return v_res_3818_;
}
pub unsafe fn l_Lean_Option_get_x3f(
    mut v_00_u03b1_3819_: *mut leanh::LeanObject,
    mut v_inst_3820_: *mut leanh::LeanObject,
    mut v_opts_3821_: *mut leanh::LeanObject,
    mut v_opt_3822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3823_ = l_Lean_Option_get_x3f___redArg(v_inst_3820_, v_opts_3821_, v_opt_3822_);
    return v___x_3823_;
}
pub unsafe fn l_Lean_Option_get_x3f___boxed(
    mut v_00_u03b1_3824_: *mut leanh::LeanObject,
    mut v_inst_3825_: *mut leanh::LeanObject,
    mut v_opts_3826_: *mut leanh::LeanObject,
    mut v_opt_3827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3828_ = l_Lean_Option_get_x3f(v_00_u03b1_3824_, v_inst_3825_, v_opts_3826_, v_opt_3827_);
    leanh::lean_dec_ref(v_opt_3827_);
    leanh::lean_dec_ref(v_opts_3826_);
    return v_res_3828_;
}
pub unsafe fn l_Lean_Option_get___redArg(
    mut v_inst_3829_: *mut leanh::LeanObject,
    mut v_opts_3830_: *mut leanh::LeanObject,
    mut v_opt_3831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofDataValue_x3f_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_3832_ = leanh::lean_ctor_get(v_opt_3831_, 0);
    v_defValue_3833_ = leanh::lean_ctor_get(v_opt_3831_, 1);
    v_map_3834_ = leanh::lean_ctor_get(v_opts_3830_, 0);
    v_ofDataValue_x3f_3835_ = leanh::lean_ctor_get(v_inst_3829_, 1);
    leanh::lean_inc_ref(v_ofDataValue_x3f_3835_);
    leanh::lean_dec_ref(v_inst_3829_);
    v___x_3836_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3834_,
            v_name_3832_,
        );
    if leanh::lean_obj_tag(v___x_3836_) == 0 {
        leanh::lean_dec_ref(v_ofDataValue_x3f_3835_);
        leanh::lean_inc(v_defValue_3833_);
        return v_defValue_3833_;
    } else {
        let mut v_val_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3837_ = leanh::lean_ctor_get(v___x_3836_, 0);
        leanh::lean_inc(v_val_3837_);
        leanh::lean_dec_ref_known(v___x_3836_, 1);
        v___x_3838_ = leanh::lean_apply_1(v_ofDataValue_x3f_3835_, v_val_3837_);
        if leanh::lean_obj_tag(v___x_3838_) == 0 {
            leanh::lean_inc(v_defValue_3833_);
            return v_defValue_3833_;
        } else {
            let mut v_val_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_3839_ = leanh::lean_ctor_get(v___x_3838_, 0);
            leanh::lean_inc(v_val_3839_);
            leanh::lean_dec_ref_known(v___x_3838_, 1);
            return v_val_3839_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___redArg___boxed(
    mut v_inst_3840_: *mut leanh::LeanObject,
    mut v_opts_3841_: *mut leanh::LeanObject,
    mut v_opt_3842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3843_ = l_Lean_Option_get___redArg(v_inst_3840_, v_opts_3841_, v_opt_3842_);
    leanh::lean_dec_ref(v_opt_3842_);
    leanh::lean_dec_ref(v_opts_3841_);
    return v_res_3843_;
}
pub unsafe fn l_Lean_Option_get(
    mut v_00_u03b1_3844_: *mut leanh::LeanObject,
    mut v_inst_3845_: *mut leanh::LeanObject,
    mut v_opts_3846_: *mut leanh::LeanObject,
    mut v_opt_3847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3848_ = l_Lean_Option_get___redArg(v_inst_3845_, v_opts_3846_, v_opt_3847_);
    return v___x_3848_;
}
pub unsafe fn l_Lean_Option_get___boxed(
    mut v_00_u03b1_3849_: *mut leanh::LeanObject,
    mut v_inst_3850_: *mut leanh::LeanObject,
    mut v_opts_3851_: *mut leanh::LeanObject,
    mut v_opt_3852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3853_ = l_Lean_Option_get(v_00_u03b1_3849_, v_inst_3850_, v_opts_3851_, v_opt_3852_);
    leanh::lean_dec_ref(v_opt_3852_);
    leanh::lean_dec_ref(v_opts_3851_);
    return v_res_3853_;
}
pub unsafe fn lean_options_get_bool(
    mut v_opts_3854_: *mut leanh::LeanObject,
    mut v_name_3855_: *mut leanh::LeanObject,
    mut v_defValue_3856_: u8,
) -> u8 {
    let mut v_map_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_3857_ = leanh::lean_ctor_get(v_opts_3854_, 0);
    leanh::lean_inc(v_map_3857_);
    leanh::lean_dec_ref(v_opts_3854_);
    v___x_3858_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3857_,
            v_name_3855_,
        );
    leanh::lean_dec(v_name_3855_);
    leanh::lean_dec(v_map_3857_);
    if leanh::lean_obj_tag(v___x_3858_) == 0 {
        return v_defValue_3856_;
    } else {
        let mut v_val_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3859_ = leanh::lean_ctor_get(v___x_3858_, 0);
        leanh::lean_inc(v_val_3859_);
        leanh::lean_dec_ref_known(v___x_3858_, 1);
        if leanh::lean_obj_tag(v_val_3859_) == 1 {
            let mut v_v_3860_: u8 = 0;
            v_v_3860_ = leanh::lean_ctor_get_uint8(v_val_3859_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_3859_, 0);
            return v_v_3860_;
        } else {
            leanh::lean_dec(v_val_3859_);
            return v_defValue_3856_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_Options_0__Lean_Option_getBool___boxed(
    mut v_opts_3861_: *mut leanh::LeanObject,
    mut v_name_3862_: *mut leanh::LeanObject,
    mut v_defValue_3863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_boxed_3864_: u8 = 0;
    let mut v_res_3865_: u8 = 0;
    let mut v_r_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_defValue_boxed_3864_ = (leanh::lean_unbox(v_defValue_3863_) as u8);
    v_res_3865_ = lean_options_get_bool(v_opts_3861_, v_name_3862_, v_defValue_boxed_3864_);
    v_r_3866_ = leanh::lean_box((v_res_3865_) as usize);
    return v_r_3866_;
}
pub unsafe fn l_Lean_Option_getM___redArg___lam__0(
    mut v_inst_3867_: *mut leanh::LeanObject,
    mut v_opt_3868_: *mut leanh::LeanObject,
    mut v_toPure_3869_: *mut leanh::LeanObject,
    mut v_____do__lift_3870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3871_ = l_Lean_Option_get___redArg(v_inst_3867_, v_____do__lift_3870_, v_opt_3868_);
    v___x_3872_ =
        leanh::lean_apply_2(v_toPure_3869_, leanh::lean_box(0), v___x_3871_);
    return v___x_3872_;
}
pub unsafe fn l_Lean_Option_getM___redArg___lam__0___boxed(
    mut v_inst_3873_: *mut leanh::LeanObject,
    mut v_opt_3874_: *mut leanh::LeanObject,
    mut v_toPure_3875_: *mut leanh::LeanObject,
    mut v_____do__lift_3876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3877_ = l_Lean_Option_getM___redArg___lam__0(
        v_inst_3873_,
        v_opt_3874_,
        v_toPure_3875_,
        v_____do__lift_3876_,
    );
    leanh::lean_dec_ref(v_____do__lift_3876_);
    leanh::lean_dec_ref(v_opt_3874_);
    return v_res_3877_;
}
pub unsafe fn l_Lean_Option_getM___redArg(
    mut v_inst_3878_: *mut leanh::LeanObject,
    mut v_inst_3879_: *mut leanh::LeanObject,
    mut v_inst_3880_: *mut leanh::LeanObject,
    mut v_opt_3881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3882_ = leanh::lean_ctor_get(v_inst_3878_, 0);
    leanh::lean_inc_ref(v_toApplicative_3882_);
    v_toBind_3883_ = leanh::lean_ctor_get(v_inst_3878_, 1);
    leanh::lean_inc(v_toBind_3883_);
    leanh::lean_dec_ref(v_inst_3878_);
    v_toPure_3884_ = leanh::lean_ctor_get(v_toApplicative_3882_, 1);
    leanh::lean_inc(v_toPure_3884_);
    leanh::lean_dec_ref(v_toApplicative_3882_);
    v___f_3885_ = leanh::lean_alloc_closure(
        l_Lean_Option_getM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_3885_, 0, v_inst_3880_);
    leanh::lean_closure_set(v___f_3885_, 1, v_opt_3881_);
    leanh::lean_closure_set(v___f_3885_, 2, v_toPure_3884_);
    v___x_3886_ = leanh::lean_apply_4(
        v_toBind_3883_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_3879_,
        v___f_3885_,
    );
    return v___x_3886_;
}
pub unsafe fn l_Lean_Option_getM(
    mut v_m_3887_: *mut leanh::LeanObject,
    mut v_00_u03b1_3888_: *mut leanh::LeanObject,
    mut v_inst_3889_: *mut leanh::LeanObject,
    mut v_inst_3890_: *mut leanh::LeanObject,
    mut v_inst_3891_: *mut leanh::LeanObject,
    mut v_opt_3892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3893_ =
        l_Lean_Option_getM___redArg(v_inst_3889_, v_inst_3890_, v_inst_3891_, v_opt_3892_);
    return v___x_3893_;
}
pub unsafe fn l_Lean_Option_set___redArg(
    mut v_inst_3894_: *mut leanh::LeanObject,
    mut v_opts_3895_: *mut leanh::LeanObject,
    mut v_opt_3896_: *mut leanh::LeanObject,
    mut v_val_3897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_3898_ = leanh::lean_ctor_get(v_opt_3896_, 0);
    leanh::lean_inc(v_name_3898_);
    leanh::lean_dec_ref(v_opt_3896_);
    v___x_3899_ =
        l_Lean_Options_set___redArg(v_inst_3894_, v_opts_3895_, v_name_3898_, v_val_3897_);
    return v___x_3899_;
}
pub unsafe fn l_Lean_Option_set(
    mut v_00_u03b1_3900_: *mut leanh::LeanObject,
    mut v_inst_3901_: *mut leanh::LeanObject,
    mut v_opts_3902_: *mut leanh::LeanObject,
    mut v_opt_3903_: *mut leanh::LeanObject,
    mut v_val_3904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3905_ = l_Lean_Option_set___redArg(v_inst_3901_, v_opts_3902_, v_opt_3903_, v_val_3904_);
    return v___x_3905_;
}
pub unsafe fn l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(
    mut v_o_3906_: *mut leanh::LeanObject,
    mut v_k_3907_: *mut leanh::LeanObject,
    mut v_v_3908_: u8,
) -> *mut leanh::LeanObject {
    let mut v_map_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3910_: u8 = 0;
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3913_: u8 = 0;
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: u8 = 0;
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3924_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3909_ = leanh::lean_ctor_get(v_o_3906_, 0);
                v_hasTrace_3910_ = leanh::lean_ctor_get_uint8(
                    v_o_3906_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3924_ = (!leanh::lean_is_exclusive(v_o_3906_)) as u8;
                if v_isSharedCheck_3924_ == 0 {
                    v___x_3912_ = v_o_3906_;
                    v_isShared_3913_ = v_isSharedCheck_3924_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_3909_);
                    leanh::lean_dec(v_o_3906_);
                    v___x_3912_ = leanh::lean_box(0);
                    v_isShared_3913_ = v_isSharedCheck_3924_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3914_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_3914_, 0 as u32, v_v_3908_);
                leanh::lean_inc(v_k_3907_);
                v___x_3915_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3907_, v___x_3914_, v_map_3909_);
                if v_hasTrace_3910_ == 0 {
                    v___x_3916_ = l_Lean_Options_insert___closed__1;
                    v___x_3917_ = l_Lean_Name_isPrefixOf(v___x_3916_, v_k_3907_);
                    leanh::lean_dec(v_k_3907_);
                    if v_isShared_3913_ == 0 {
                        leanh::lean_ctor_set(v___x_3912_, 0, v___x_3915_);
                        v___x_3919_ = v___x_3912_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3920_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3915_);
                        v___x_3919_ = v_reuseFailAlloc_3920_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_3907_);
                    if v_isShared_3913_ == 0 {
                        leanh::lean_ctor_set(v___x_3912_, 0, v___x_3915_);
                        v___x_3922_ = v___x_3912_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3923_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3915_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_3923_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_3910_,
                        );
                        v___x_3922_ = v_reuseFailAlloc_3923_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3919_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3917_,
                );
                return v___x_3919_;
            }
            3 => {
                return v___x_3922_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0___boxed(
    mut v_o_3925_: *mut leanh::LeanObject,
    mut v_k_3926_: *mut leanh::LeanObject,
    mut v_v_3927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_3928_: u8 = 0;
    let mut v_res_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_3928_ = (leanh::lean_unbox(v_v_3927_) as u8);
    v_res_3929_ =
        l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(
            v_o_3925_,
            v_k_3926_,
            v_v_boxed_3928_,
        );
    return v_res_3929_;
}
pub unsafe fn lean_options_update_bool(
    mut v_opts_3930_: *mut leanh::LeanObject,
    mut v_name_3931_: *mut leanh::LeanObject,
    mut v_val_3932_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3933_ =
        l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(
            v_opts_3930_,
            v_name_3931_,
            v_val_3932_,
        );
    return v___x_3933_;
}
pub unsafe fn l___private_Lean_Data_Options_0__Lean_Option_updateBool___boxed(
    mut v_opts_3934_: *mut leanh::LeanObject,
    mut v_name_3935_: *mut leanh::LeanObject,
    mut v_val_3936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_boxed_3937_: u8 = 0;
    let mut v_res_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_3937_ = (leanh::lean_unbox(v_val_3936_) as u8);
    v_res_3938_ = lean_options_update_bool(v_opts_3934_, v_name_3935_, v_val_boxed_3937_);
    return v_res_3938_;
}
pub unsafe fn l_Lean_Option_setIfNotSet___redArg(
    mut v_inst_3939_: *mut leanh::LeanObject,
    mut v_opts_3940_: *mut leanh::LeanObject,
    mut v_opt_3941_: *mut leanh::LeanObject,
    mut v_val_3942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: u8 = 0;
    v_name_3943_ = leanh::lean_ctor_get(v_opt_3941_, 0);
    v_map_3944_ = leanh::lean_ctor_get(v_opts_3940_, 0);
    v___x_3945_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(
            v_name_3943_,
            v_map_3944_,
        );
    if v___x_3945_ == 0 {
        let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3946_ =
            l_Lean_Option_set___redArg(v_inst_3939_, v_opts_3940_, v_opt_3941_, v_val_3942_);
        return v___x_3946_;
    } else {
        leanh::lean_dec(v_val_3942_);
        leanh::lean_dec_ref(v_opt_3941_);
        leanh::lean_dec_ref(v_inst_3939_);
        return v_opts_3940_;
    }
}
pub unsafe fn l_Lean_Option_setIfNotSet(
    mut v_00_u03b1_3947_: *mut leanh::LeanObject,
    mut v_inst_3948_: *mut leanh::LeanObject,
    mut v_opts_3949_: *mut leanh::LeanObject,
    mut v_opt_3950_: *mut leanh::LeanObject,
    mut v_val_3951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3952_ =
        l_Lean_Option_setIfNotSet___redArg(v_inst_3948_, v_opts_3949_, v_opt_3950_, v_val_3951_);
    return v___x_3952_;
}
pub unsafe fn _init_l_Lean_Option_register___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3953_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__28),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__28_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__28,
    );
    return v___x_3953_;
}
pub unsafe fn l_Lean_Option_register___redArg(
    mut v_inst_3954_: *mut leanh::LeanObject,
    mut v_name_3955_: *mut leanh::LeanObject,
    mut v_decl_3956_: *mut leanh::LeanObject,
    mut v_ref_3957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toDataValue_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3962_: u8 = 0;
    let mut v_defValue_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3971_: u8 = 0;
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3978_: u8 = 0;
    let mut v_unused_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3983_: u8 = 0;
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3987_: u8 = 0;
    let mut v_isSharedCheck_3988_: u8 = 0;
    let mut v_unused_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toDataValue_3959_ = leanh::lean_ctor_get(v_inst_3954_, 0);
                v_isSharedCheck_3988_ = (!leanh::lean_is_exclusive(v_inst_3954_)) as u8;
                if v_isSharedCheck_3988_ == 0 {
                    v_unused_3989_ = leanh::lean_ctor_get(v_inst_3954_, 1);
                    leanh::lean_dec(v_unused_3989_);
                    v___x_3961_ = v_inst_3954_;
                    v_isShared_3962_ = v_isSharedCheck_3988_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toDataValue_3959_);
                    leanh::lean_dec(v_inst_3954_);
                    v___x_3961_ = leanh::lean_box(0);
                    v_isShared_3962_ = v_isSharedCheck_3988_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_defValue_3963_ = leanh::lean_ctor_get(v_decl_3956_, 0);
                leanh::lean_inc_n(v_defValue_3963_, 2);
                v_descr_3964_ = leanh::lean_ctor_get(v_decl_3956_, 1);
                leanh::lean_inc_ref(v_descr_3964_);
                v_deprecation_x3f_3965_ = leanh::lean_ctor_get(v_decl_3956_, 2);
                leanh::lean_inc(v_deprecation_x3f_3965_);
                leanh::lean_dec_ref(v_decl_3956_);
                v___x_3966_ = leanh::lean_apply_1(v_toDataValue_3959_, v_defValue_3963_);
                leanh::lean_inc_n(v_name_3955_, 2);
                v___x_3967_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_3967_, 0, v_name_3955_);
                leanh::lean_ctor_set(v___x_3967_, 1, v_ref_3957_);
                leanh::lean_ctor_set(v___x_3967_, 2, v___x_3966_);
                leanh::lean_ctor_set(v___x_3967_, 3, v_descr_3964_);
                leanh::lean_ctor_set(v___x_3967_, 4, v_deprecation_x3f_3965_);
                v___x_3968_ = lean_register_option(v_name_3955_, v___x_3967_);
                if leanh::lean_obj_tag(v___x_3968_) == 0 {
                    v_isSharedCheck_3978_ = (!leanh::lean_is_exclusive(v___x_3968_)) as u8;
                    if v_isSharedCheck_3978_ == 0 {
                        v_unused_3979_ = leanh::lean_ctor_get(v___x_3968_, 0);
                        leanh::lean_dec(v_unused_3979_);
                        v___x_3970_ = v___x_3968_;
                        v_isShared_3971_ = v_isSharedCheck_3978_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3968_);
                        v___x_3970_ = leanh::lean_box(0);
                        v_isShared_3971_ = v_isSharedCheck_3978_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_defValue_3963_);
                    leanh::lean_del_object(v___x_3961_);
                    leanh::lean_dec(v_name_3955_);
                    v_a_3980_ = leanh::lean_ctor_get(v___x_3968_, 0);
                    v_isSharedCheck_3987_ = (!leanh::lean_is_exclusive(v___x_3968_)) as u8;
                    if v_isSharedCheck_3987_ == 0 {
                        v___x_3982_ = v___x_3968_;
                        v_isShared_3983_ = v_isSharedCheck_3987_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3980_);
                        leanh::lean_dec(v___x_3968_);
                        v___x_3982_ = leanh::lean_box(0);
                        v_isShared_3983_ = v_isSharedCheck_3987_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3962_ == 0 {
                    leanh::lean_ctor_set(v___x_3961_, 1, v_defValue_3963_);
                    leanh::lean_ctor_set(v___x_3961_, 0, v_name_3955_);
                    v___x_3973_ = v___x_3961_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3977_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_name_3955_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3977_, 1, v_defValue_3963_);
                    v___x_3973_ = v_reuseFailAlloc_3977_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3971_ == 0 {
                    leanh::lean_ctor_set(v___x_3970_, 0, v___x_3973_);
                    v___x_3975_ = v___x_3970_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3976_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3973_);
                    v___x_3975_ = v_reuseFailAlloc_3976_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3975_;
            }
            5 => {
                if v_isShared_3983_ == 0 {
                    v___x_3985_ = v___x_3982_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3986_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
                    v___x_3985_ = v_reuseFailAlloc_3986_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3985_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___redArg___boxed(
    mut v_inst_3990_: *mut leanh::LeanObject,
    mut v_name_3991_: *mut leanh::LeanObject,
    mut v_decl_3992_: *mut leanh::LeanObject,
    mut v_ref_3993_: *mut leanh::LeanObject,
    mut v_a_3994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3995_ =
        l_Lean_Option_register___redArg(v_inst_3990_, v_name_3991_, v_decl_3992_, v_ref_3993_);
    return v_res_3995_;
}
pub unsafe fn l_Lean_Option_register(
    mut v_00_u03b1_3996_: *mut leanh::LeanObject,
    mut v_inst_3997_: *mut leanh::LeanObject,
    mut v_name_3998_: *mut leanh::LeanObject,
    mut v_decl_3999_: *mut leanh::LeanObject,
    mut v_ref_4000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4002_ =
        l_Lean_Option_register___redArg(v_inst_3997_, v_name_3998_, v_decl_3999_, v_ref_4000_);
    return v___x_4002_;
}
pub unsafe fn l_Lean_Option_register___boxed(
    mut v_00_u03b1_4003_: *mut leanh::LeanObject,
    mut v_inst_4004_: *mut leanh::LeanObject,
    mut v_name_4005_: *mut leanh::LeanObject,
    mut v_decl_4006_: *mut leanh::LeanObject,
    mut v_ref_4007_: *mut leanh::LeanObject,
    mut v_a_4008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4009_ = l_Lean_Option_register(
        v_00_u03b1_4003_,
        v_inst_4004_,
        v_name_4005_,
        v_decl_4006_,
        v_ref_4007_,
    );
    return v_res_4009_;
}
pub unsafe fn _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4097_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__5;
    v___x_4098_ = l_String_toRawSubstring_x27(v___x_4097_);
    return v___x_4098_;
}
pub unsafe fn _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4118_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__16;
    v___x_4119_ = l_String_toRawSubstring_x27(v___x_4118_);
    return v___x_4119_;
}
pub unsafe fn _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29()
-> *mut leanh::LeanObject {
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4146_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_4146_;
}
pub unsafe fn l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(
    mut v_x_4147_: *mut leanh::LeanObject,
    mut v_a_4148_: *mut leanh::LeanObject,
    mut v_a_4149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: u8 = 0;
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: u8 = 0;
    let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4295_: u8 = 0;
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4299_: u8 = 0;
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4305_: u8 = 0;
    let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4150_ = l_Lean_OptionDecl_declName___autoParam___closed__0;
                v___x_4151_ = l_Lean_Option_registerBuiltinOption___closed__2;
                leanh::lean_inc(v_x_4147_);
                v___x_4152_ = l_Lean_Syntax_isOfKind(v_x_4147_, v___x_4151_);
                if v___x_4152_ == 0 {
                    leanh::lean_dec(v_x_4147_);
                    v___x_4153_ = leanh::lean_box(1);
                    v___x_4154_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4154_, 0, v___x_4153_);
                    leanh::lean_ctor_set(v___x_4154_, 1, v_a_4149_);
                    return v___x_4154_;
                } else {
                    v___x_4155_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4156_ = l_Lean_Syntax_getArg(v_x_4147_, v___x_4155_);
                    v___x_4157_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4158_ = l_Lean_Syntax_getArg(v_x_4147_, v___x_4157_);
                    v___x_4159_ = leanh::lean_unsigned_to_nat(3);
                    v_name_4160_ = l_Lean_Syntax_getArg(v_x_4147_, v___x_4159_);
                    v___x_4161_ = leanh::lean_unsigned_to_nat(5);
                    v___x_4162_ = l_Lean_Syntax_getArg(v_x_4147_, v___x_4161_);
                    v___x_4163_ = leanh::lean_unsigned_to_nat(7);
                    v___x_4164_ = l_Lean_Syntax_getArg(v_x_4147_, v___x_4163_);
                    leanh::lean_dec(v_x_4147_);
                    v___x_4300_ = l_Lean_Syntax_getOptional_x3f(v___x_4158_);
                    leanh::lean_dec(v___x_4158_);
                    if leanh::lean_obj_tag(v___x_4300_) == 0 {
                        v___x_4301_ = leanh::lean_box(0);
                        v___y_4289_ = v___x_4301_;
                        state = 5;
                        continue;
                    } else {
                        v_val_4302_ = leanh::lean_ctor_get(v___x_4300_, 0);
                        v_isSharedCheck_4309_ =
                            (!leanh::lean_is_exclusive(v___x_4300_)) as u8;
                        if v_isSharedCheck_4309_ == 0 {
                            v___x_4304_ = v___x_4300_;
                            v_isShared_4305_ = v_isSharedCheck_4309_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4302_);
                            leanh::lean_dec(v___x_4300_);
                            v___x_4304_ = leanh::lean_box(0);
                            v_isShared_4305_ = v_isSharedCheck_4309_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc_n(v___y_4170_, 2);
                leanh::lean_inc_n(v___y_4174_, 6);
                v___x_4179_ =
                    l_Lean_Syntax_node2(v___y_4174_, v___y_4170_, v___y_4178_, v___x_4164_);
                v___x_4180_ =
                    l_Lean_Syntax_node2(v___y_4174_, v___y_4169_, v___y_4166_, v___x_4179_);
                v___x_4181_ = l_Lean_Syntax_node1(v___y_4174_, v___y_4176_, v___x_4180_);
                v___x_4182_ =
                    l_Lean_Syntax_node2(v___y_4174_, v___y_4175_, v___x_4181_, v___y_4168_);
                v___x_4183_ = l_Lean_Syntax_node1(v___y_4174_, v___y_4170_, v___x_4182_);
                v___x_4184_ = l_Lean_Syntax_node1(v___y_4174_, v___y_4177_, v___x_4183_);
                leanh::lean_inc(v___y_4173_);
                v___x_4185_ = l_Lean_Syntax_node4(
                    v___y_4174_,
                    v___y_4173_,
                    v___y_4171_,
                    v___y_4172_,
                    v___y_4167_,
                    v___x_4184_,
                );
                v___x_4186_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4186_, 0, v___x_4185_);
                leanh::lean_ctor_set(v___x_4186_, 1, v_a_4149_);
                return v___x_4186_;
            }
            2 => {
                leanh::lean_inc_ref(v___y_4192_);
                v___x_4200_ = l_Array_append___redArg(v___y_4192_, v___y_4199_);
                leanh::lean_dec_ref(v___y_4199_);
                leanh::lean_inc_n(v___y_4190_, 3);
                leanh::lean_inc_n(v___y_4196_, 12);
                v___x_4201_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4201_, 0, v___y_4196_);
                leanh::lean_ctor_set(v___x_4201_, 1, v___y_4190_);
                leanh::lean_ctor_set(v___x_4201_, 2, v___x_4200_);
                leanh::lean_inc_n(v___y_4189_, 5);
                leanh::lean_inc(v___y_4195_);
                v___x_4202_ = l_Lean_Syntax_node7(
                    v___y_4196_,
                    v___y_4195_,
                    v___y_4198_,
                    v___y_4189_,
                    v___x_4201_,
                    v___y_4189_,
                    v___y_4189_,
                    v___y_4189_,
                    v___y_4189_,
                );
                v___x_4203_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0;
                leanh::lean_inc_ref(v___y_4188_);
                leanh::lean_inc_ref_n(v___y_4194_, 6);
                v___x_4204_ =
                    l_Lean_Name_mkStr4(v___x_4150_, v___y_4194_, v___y_4188_, v___x_4203_);
                v___x_4205_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1;
                v___x_4206_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4206_, 0, v___y_4196_);
                leanh::lean_ctor_set(v___x_4206_, 1, v___x_4205_);
                v___x_4207_ = l_Lean_Syntax_node1(v___y_4196_, v___x_4204_, v___x_4206_);
                v___x_4208_ = l_Lean_OptionDecl_declName___autoParam___closed__14;
                v___x_4209_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2;
                v___x_4210_ =
                    l_Lean_Name_mkStr4(v___x_4150_, v___y_4194_, v___x_4208_, v___x_4209_);
                v___x_4211_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3;
                v___x_4212_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4212_, 0, v___y_4196_);
                leanh::lean_ctor_set(v___x_4212_, 1, v___x_4211_);
                v___x_4213_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4;
                v___x_4214_ =
                    l_Lean_Name_mkStr4(v___x_4150_, v___y_4194_, v___x_4208_, v___x_4213_);
                v___x_4215_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6), core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once), _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
                v___x_4216_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7;
                leanh::lean_inc_n(v___y_4191_, 2);
                leanh::lean_inc_n(v___y_4197_, 2);
                v___x_4217_ = l_Lean_addMacroScope(v___y_4197_, v___x_4216_, v___y_4191_);
                v___x_4218_ = leanh::lean_box(0);
                v___x_4219_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11;
                v___x_4220_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4220_, 0, v___y_4196_);
                leanh::lean_ctor_set(v___x_4220_, 1, v___x_4215_);
                leanh::lean_ctor_set(v___x_4220_, 2, v___x_4217_);
                leanh::lean_ctor_set(v___x_4220_, 3, v___x_4219_);
                v___x_4221_ = l_Lean_Syntax_node1(v___y_4196_, v___y_4190_, v___x_4162_);
                leanh::lean_inc(v___x_4214_);
                v___x_4222_ =
                    l_Lean_Syntax_node2(v___y_4196_, v___x_4214_, v___x_4220_, v___x_4221_);
                v___x_4223_ =
                    l_Lean_Syntax_node2(v___y_4196_, v___x_4210_, v___x_4212_, v___x_4222_);
                v___x_4224_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12;
                v___x_4225_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4225_, 0, v___y_4196_);
                leanh::lean_ctor_set(v___x_4225_, 1, v___x_4224_);
                leanh::lean_inc(v_name_4160_);
                v___x_4226_ = l_Lean_Syntax_node3(
                    v___y_4196_,
                    v___y_4190_,
                    v_name_4160_,
                    v___x_4223_,
                    v___x_4225_,
                );
                v___x_4227_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13;
                v___x_4228_ =
                    l_Lean_Name_mkStr4(v___x_4150_, v___y_4194_, v___x_4208_, v___x_4227_);
                v___x_4229_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14;
                v___x_4230_ =
                    l_Lean_Name_mkStr4(v___x_4150_, v___y_4194_, v___x_4208_, v___x_4229_);
                v___x_4231_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15;
                v___x_4232_ =
                    l_Lean_Name_mkStr4(v___x_4150_, v___y_4194_, v___x_4208_, v___x_4231_);
                v___x_4233_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17), core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once), _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
                v___x_4234_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19;
                v___x_4235_ = l_Lean_addMacroScope(v___y_4197_, v___x_4234_, v___y_4191_);
                v___x_4236_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21;
                v___x_4237_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4237_, 0, v___y_4196_);
                leanh::lean_ctor_set(v___x_4237_, 1, v___x_4233_);
                leanh::lean_ctor_set(v___x_4237_, 2, v___x_4235_);
                leanh::lean_ctor_set(v___x_4237_, 3, v___x_4236_);
                v___x_4238_ = l_Lean_TSyntax_getId(v_name_4160_);
                leanh::lean_dec(v_name_4160_);
                leanh::lean_inc(v___x_4238_);
                v___x_4239_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                    v___x_4218_,
                    v___x_4238_,
                );
                if leanh::lean_obj_tag(v___x_4239_) == 0 {
                    v___x_4240_ = l_Lean_quoteNameMk(v___x_4238_);
                    v___y_4166_ = v___x_4237_;
                    v___y_4167_ = v___x_4226_;
                    v___y_4168_ = v___y_4189_;
                    v___y_4169_ = v___x_4214_;
                    v___y_4170_ = v___y_4190_;
                    v___y_4171_ = v___x_4202_;
                    v___y_4172_ = v___x_4207_;
                    v___y_4173_ = v___y_4193_;
                    v___y_4174_ = v___y_4196_;
                    v___y_4175_ = v___x_4230_;
                    v___y_4176_ = v___x_4232_;
                    v___y_4177_ = v___x_4228_;
                    v___y_4178_ = v___x_4240_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_4238_);
                    v_val_4241_ = leanh::lean_ctor_get(v___x_4239_, 0);
                    leanh::lean_inc(v_val_4241_);
                    leanh::lean_dec_ref_known(v___x_4239_, 1);
                    v___x_4242_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22;
                    leanh::lean_inc_ref(v___y_4194_);
                    v___x_4243_ =
                        l_Lean_Name_mkStr4(v___x_4150_, v___y_4194_, v___x_4208_, v___x_4242_);
                    v___x_4244_ = l_Lean_getOptionDecl___closed__1;
                    v___x_4245_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23;
                    v___x_4246_ = lean_string_intercalate(v___x_4245_, v_val_4241_);
                    v___x_4247_ = lean_string_append(v___x_4244_, v___x_4246_);
                    leanh::lean_dec_ref(v___x_4246_);
                    v___x_4248_ = leanh::lean_box(2);
                    v___x_4249_ = l_Lean_Syntax_mkNameLit(v___x_4247_, v___x_4248_);
                    v___x_4250_ = lean_mk_empty_array_with_capacity(v___x_4157_);
                    v___x_4251_ = lean_array_push(v___x_4250_, v___x_4249_);
                    v___x_4252_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_4252_, 0, v___x_4248_);
                    leanh::lean_ctor_set(v___x_4252_, 1, v___x_4243_);
                    leanh::lean_ctor_set(v___x_4252_, 2, v___x_4251_);
                    v___y_4166_ = v___x_4237_;
                    v___y_4167_ = v___x_4226_;
                    v___y_4168_ = v___y_4189_;
                    v___y_4169_ = v___x_4214_;
                    v___y_4170_ = v___y_4190_;
                    v___y_4171_ = v___x_4202_;
                    v___y_4172_ = v___x_4207_;
                    v___y_4173_ = v___y_4193_;
                    v___y_4174_ = v___y_4196_;
                    v___y_4175_ = v___x_4230_;
                    v___y_4176_ = v___x_4232_;
                    v___y_4177_ = v___x_4228_;
                    v___y_4178_ = v___x_4252_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref_n(v___y_4258_, 2);
                v___x_4265_ = l_Array_append___redArg(v___y_4258_, v___y_4264_);
                leanh::lean_dec_ref(v___y_4264_);
                leanh::lean_inc_n(v___y_4255_, 2);
                leanh::lean_inc_n(v___y_4262_, 2);
                v___x_4266_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4266_, 0, v___y_4262_);
                leanh::lean_ctor_set(v___x_4266_, 1, v___y_4255_);
                leanh::lean_ctor_set(v___x_4266_, 2, v___x_4265_);
                v___x_4267_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4267_, 0, v___y_4262_);
                leanh::lean_ctor_set(v___x_4267_, 1, v___y_4255_);
                leanh::lean_ctor_set(v___x_4267_, 2, v___y_4258_);
                if leanh::lean_obj_tag(v___y_4256_) == 1 {
                    v_val_4268_ = leanh::lean_ctor_get(v___y_4256_, 0);
                    leanh::lean_inc(v_val_4268_);
                    leanh::lean_dec_ref_known(v___y_4256_, 1);
                    v___x_4269_ = l_Array_mkArray1___redArg(v_val_4268_);
                    v___y_4188_ = v___y_4254_;
                    v___y_4189_ = v___x_4267_;
                    v___y_4190_ = v___y_4255_;
                    v___y_4191_ = v___y_4257_;
                    v___y_4192_ = v___y_4258_;
                    v___y_4193_ = v___y_4260_;
                    v___y_4194_ = v___y_4259_;
                    v___y_4195_ = v___y_4261_;
                    v___y_4196_ = v___y_4262_;
                    v___y_4197_ = v___y_4263_;
                    v___y_4198_ = v___x_4266_;
                    v___y_4199_ = v___x_4269_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___y_4256_);
                    v___x_4270_ = l_Lean_OptionDecl_declName___autoParam___closed__5;
                    v___y_4188_ = v___y_4254_;
                    v___y_4189_ = v___x_4267_;
                    v___y_4190_ = v___y_4255_;
                    v___y_4191_ = v___y_4257_;
                    v___y_4192_ = v___y_4258_;
                    v___y_4193_ = v___y_4260_;
                    v___y_4194_ = v___y_4259_;
                    v___y_4195_ = v___y_4261_;
                    v___y_4196_ = v___y_4262_;
                    v___y_4197_ = v___y_4263_;
                    v___y_4198_ = v___x_4266_;
                    v___y_4199_ = v___x_4270_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_quotContext_4274_ = leanh::lean_ctor_get(v_a_4148_, 1);
                v_currMacroScope_4275_ = leanh::lean_ctor_get(v_a_4148_, 2);
                v_ref_4276_ = leanh::lean_ctor_get(v_a_4148_, 5);
                v___x_4277_ = 0;
                v___x_4278_ = l_Lean_SourceInfo_fromRef(v_ref_4276_, v___x_4277_);
                v___x_4279_ = l_Lean_OptionDecl_declName___autoParam___closed__1;
                v___x_4280_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24;
                v___x_4281_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26;
                v___x_4282_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28;
                v___x_4283_ = l_Lean_OptionDecl_declName___autoParam___closed__9;
                v___x_4284_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29), core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once), _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29);
                if leanh::lean_obj_tag(v___y_4273_) == 1 {
                    v_val_4285_ = leanh::lean_ctor_get(v___y_4273_, 0);
                    leanh::lean_inc(v_val_4285_);
                    leanh::lean_dec_ref_known(v___y_4273_, 1);
                    v___x_4286_ = l_Array_mkArray1___redArg(v_val_4285_);
                    v___y_4254_ = v___x_4280_;
                    v___y_4255_ = v___x_4283_;
                    v___y_4256_ = v___y_4272_;
                    v___y_4257_ = v_currMacroScope_4275_;
                    v___y_4258_ = v___x_4284_;
                    v___y_4259_ = v___x_4279_;
                    v___y_4260_ = v___x_4281_;
                    v___y_4261_ = v___x_4282_;
                    v___y_4262_ = v___x_4278_;
                    v___y_4263_ = v_quotContext_4274_;
                    v___y_4264_ = v___x_4286_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___y_4273_);
                    v___x_4287_ = l_Lean_OptionDecl_declName___autoParam___closed__5;
                    v___y_4254_ = v___x_4280_;
                    v___y_4255_ = v___x_4283_;
                    v___y_4256_ = v___y_4272_;
                    v___y_4257_ = v_currMacroScope_4275_;
                    v___y_4258_ = v___x_4284_;
                    v___y_4259_ = v___x_4279_;
                    v___y_4260_ = v___x_4281_;
                    v___y_4261_ = v___x_4282_;
                    v___y_4262_ = v___x_4278_;
                    v___y_4263_ = v_quotContext_4274_;
                    v___y_4264_ = v___x_4287_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v___x_4290_ = l_Lean_Syntax_getOptional_x3f(v___x_4156_);
                leanh::lean_dec(v___x_4156_);
                if leanh::lean_obj_tag(v___x_4290_) == 0 {
                    v___x_4291_ = leanh::lean_box(0);
                    v___y_4272_ = v___y_4289_;
                    v___y_4273_ = v___x_4291_;
                    state = 4;
                    continue;
                } else {
                    v_val_4292_ = leanh::lean_ctor_get(v___x_4290_, 0);
                    v_isSharedCheck_4299_ = (!leanh::lean_is_exclusive(v___x_4290_)) as u8;
                    if v_isSharedCheck_4299_ == 0 {
                        v___x_4294_ = v___x_4290_;
                        v_isShared_4295_ = v_isSharedCheck_4299_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4292_);
                        leanh::lean_dec(v___x_4290_);
                        v___x_4294_ = leanh::lean_box(0);
                        v_isShared_4295_ = v_isSharedCheck_4299_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_4295_ == 0 {
                    v___x_4297_ = v___x_4294_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4298_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_val_4292_);
                    v___x_4297_ = v_reuseFailAlloc_4298_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4272_ = v___y_4289_;
                v___y_4273_ = v___x_4297_;
                state = 4;
                continue;
            }
            8 => {
                if v_isShared_4305_ == 0 {
                    v___x_4307_ = v___x_4304_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4308_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_val_4302_);
                    v___x_4307_ = v_reuseFailAlloc_4308_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_4289_ = v___x_4307_;
                state = 5;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___boxed(
    mut v_x_4310_: *mut leanh::LeanObject,
    mut v_a_4311_: *mut leanh::LeanObject,
    mut v_a_4312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4313_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(v_x_4310_, v_a_4311_, v_a_4312_);
    leanh::lean_dec_ref(v_a_4311_);
    return v_res_4313_;
}
pub unsafe fn l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(
    mut v_x_4390_: *mut leanh::LeanObject,
    mut v_a_4391_: *mut leanh::LeanObject,
    mut v_a_4392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: u8 = 0;
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: u8 = 0;
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4393_ = l_Lean_Option_registerOption___closed__1;
                leanh::lean_inc(v_x_4390_);
                v___x_4394_ = l_Lean_Syntax_isOfKind(v_x_4390_, v___x_4393_);
                if v___x_4394_ == 0 {
                    leanh::lean_dec(v_x_4390_);
                    v___x_4395_ = leanh::lean_box(1);
                    v___x_4396_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4396_, 0, v___x_4395_);
                    leanh::lean_ctor_set(v___x_4396_, 1, v_a_4392_);
                    return v___x_4396_;
                } else {
                    v_quotContext_4397_ = leanh::lean_ctor_get(v_a_4391_, 1);
                    v_currMacroScope_4398_ = leanh::lean_ctor_get(v_a_4391_, 2);
                    v_ref_4399_ = leanh::lean_ctor_get(v_a_4391_, 5);
                    v___x_4400_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4401_ = l_Lean_Syntax_getArg(v_x_4390_, v___x_4400_);
                    v___x_4402_ = leanh::lean_unsigned_to_nat(2);
                    v_name_4403_ = l_Lean_Syntax_getArg(v_x_4390_, v___x_4402_);
                    v___x_4404_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4405_ = l_Lean_Syntax_getArg(v_x_4390_, v___x_4404_);
                    v___x_4406_ = leanh::lean_unsigned_to_nat(6);
                    v___x_4407_ = l_Lean_Syntax_getArg(v_x_4390_, v___x_4406_);
                    leanh::lean_dec(v_x_4390_);
                    v___x_4408_ = 0;
                    v___x_4409_ = l_Lean_SourceInfo_fromRef(v_ref_4399_, v___x_4408_);
                    v___x_4410_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25;
                    v___x_4411_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26;
                    v___x_4412_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0;
                    leanh::lean_inc_n(v___x_4409_, 10);
                    v___x_4413_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4413_, 0, v___x_4409_);
                    leanh::lean_ctor_set(v___x_4413_, 1, v___x_4410_);
                    v___x_4414_ = l_Lean_Syntax_node1(v___x_4409_, v___x_4412_, v___x_4413_);
                    v___x_4415_ = l_Lean_OptionDecl_declName___autoParam___closed__9;
                    v___x_4416_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1;
                    v___x_4417_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3;
                    v___x_4418_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4418_, 0, v___x_4409_);
                    leanh::lean_ctor_set(v___x_4418_, 1, v___x_4417_);
                    v___x_4419_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2;
                    v___x_4420_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6), core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once), _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
                    v___x_4421_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7;
                    leanh::lean_inc_n(v_currMacroScope_4398_, 2);
                    leanh::lean_inc_n(v_quotContext_4397_, 2);
                    v___x_4422_ = l_Lean_addMacroScope(
                        v_quotContext_4397_,
                        v___x_4421_,
                        v_currMacroScope_4398_,
                    );
                    v___x_4423_ = leanh::lean_box(0);
                    v___x_4424_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11;
                    v___x_4425_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_4425_, 0, v___x_4409_);
                    leanh::lean_ctor_set(v___x_4425_, 1, v___x_4420_);
                    leanh::lean_ctor_set(v___x_4425_, 2, v___x_4422_);
                    leanh::lean_ctor_set(v___x_4425_, 3, v___x_4424_);
                    v___x_4426_ = l_Lean_Syntax_node1(v___x_4409_, v___x_4415_, v___x_4405_);
                    v___x_4427_ =
                        l_Lean_Syntax_node2(v___x_4409_, v___x_4419_, v___x_4425_, v___x_4426_);
                    v___x_4428_ =
                        l_Lean_Syntax_node2(v___x_4409_, v___x_4416_, v___x_4418_, v___x_4427_);
                    v___x_4429_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12;
                    v___x_4430_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4430_, 0, v___x_4409_);
                    leanh::lean_ctor_set(v___x_4430_, 1, v___x_4429_);
                    leanh::lean_inc(v_name_4403_);
                    v___x_4431_ = l_Lean_Syntax_node3(
                        v___x_4409_,
                        v___x_4415_,
                        v_name_4403_,
                        v___x_4428_,
                        v___x_4430_,
                    );
                    v___x_4432_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3;
                    v___x_4433_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4;
                    v___x_4434_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5;
                    v___x_4435_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17), core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once), _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
                    v___x_4436_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19;
                    v___x_4437_ = l_Lean_addMacroScope(
                        v_quotContext_4397_,
                        v___x_4436_,
                        v_currMacroScope_4398_,
                    );
                    v___x_4438_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21;
                    v___x_4439_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_4439_, 0, v___x_4409_);
                    leanh::lean_ctor_set(v___x_4439_, 1, v___x_4435_);
                    leanh::lean_ctor_set(v___x_4439_, 2, v___x_4437_);
                    leanh::lean_ctor_set(v___x_4439_, 3, v___x_4438_);
                    v___x_4452_ = l_Lean_TSyntax_getId(v_name_4403_);
                    leanh::lean_dec(v_name_4403_);
                    leanh::lean_inc(v___x_4452_);
                    v___x_4453_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                        v___x_4423_,
                        v___x_4452_,
                    );
                    if leanh::lean_obj_tag(v___x_4453_) == 0 {
                        v___x_4454_ = l_Lean_quoteNameMk(v___x_4452_);
                        v___y_4441_ = v___x_4454_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4452_);
                        v_val_4455_ = leanh::lean_ctor_get(v___x_4453_, 0);
                        leanh::lean_inc(v_val_4455_);
                        leanh::lean_dec_ref_known(v___x_4453_, 1);
                        v___x_4456_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6;
                        v___x_4457_ = l_Lean_getOptionDecl___closed__1;
                        v___x_4458_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23;
                        v___x_4459_ = lean_string_intercalate(v___x_4458_, v_val_4455_);
                        v___x_4460_ = lean_string_append(v___x_4457_, v___x_4459_);
                        leanh::lean_dec_ref(v___x_4459_);
                        v___x_4461_ = leanh::lean_box(2);
                        v___x_4462_ = l_Lean_Syntax_mkNameLit(v___x_4460_, v___x_4461_);
                        v___x_4463_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4464_ = lean_mk_empty_array_with_capacity(v___x_4463_);
                        v___x_4465_ = lean_array_push(v___x_4464_, v___x_4462_);
                        v___x_4466_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_4466_, 0, v___x_4461_);
                        leanh::lean_ctor_set(v___x_4466_, 1, v___x_4456_);
                        leanh::lean_ctor_set(v___x_4466_, 2, v___x_4465_);
                        v___y_4441_ = v___x_4466_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_n(v___x_4409_, 7);
                v___x_4442_ =
                    l_Lean_Syntax_node2(v___x_4409_, v___x_4415_, v___y_4441_, v___x_4407_);
                v___x_4443_ =
                    l_Lean_Syntax_node2(v___x_4409_, v___x_4419_, v___x_4439_, v___x_4442_);
                v___x_4444_ = l_Lean_Syntax_node1(v___x_4409_, v___x_4434_, v___x_4443_);
                v___x_4445_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29), core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once), _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29);
                v___x_4446_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4446_, 0, v___x_4409_);
                leanh::lean_ctor_set(v___x_4446_, 1, v___x_4415_);
                leanh::lean_ctor_set(v___x_4446_, 2, v___x_4445_);
                v___x_4447_ =
                    l_Lean_Syntax_node2(v___x_4409_, v___x_4433_, v___x_4444_, v___x_4446_);
                v___x_4448_ = l_Lean_Syntax_node1(v___x_4409_, v___x_4415_, v___x_4447_);
                v___x_4449_ = l_Lean_Syntax_node1(v___x_4409_, v___x_4432_, v___x_4448_);
                v___x_4450_ = l_Lean_Syntax_node4(
                    v___x_4409_,
                    v___x_4411_,
                    v___x_4401_,
                    v___x_4414_,
                    v___x_4431_,
                    v___x_4449_,
                );
                v___x_4451_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4451_, 0, v___x_4450_);
                leanh::lean_ctor_set(v___x_4451_, 1, v_a_4392_);
                return v___x_4451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___boxed(
    mut v_x_4467_: *mut leanh::LeanObject,
    mut v_a_4468_: *mut leanh::LeanObject,
    mut v_a_4469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4470_ =
        l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(
            v_x_4467_, v_a_4468_, v_a_4469_,
        );
    leanh::lean_dec_ref(v_a_4468_);
    return v_res_4470_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Options(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_ImportingFlag(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_KVMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_instInhabitedOptionDecl_default = _init_l_Lean_instInhabitedOptionDecl_default();
    leanh::lean_mark_persistent(l_Lean_instInhabitedOptionDecl_default);
    l_Lean_instInhabitedOptionDecl = _init_l_Lean_instInhabitedOptionDecl();
    leanh::lean_mark_persistent(l_Lean_instInhabitedOptionDecl);
    l_Lean_instInhabitedOptionDecls = _init_l_Lean_instInhabitedOptionDecls();
    leanh::lean_mark_persistent(l_Lean_instInhabitedOptionDecls);
    res = l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Data_Options_0__Lean_optionDeclsRef =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l___private_Lean_Data_Options_0__Lean_optionDeclsRef);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Options(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_OptionDecl_declName___autoParam = _init_l_Lean_OptionDecl_declName___autoParam();
    leanh::lean_mark_persistent(l_Lean_OptionDecl_declName___autoParam);
    l_Lean_Option_register___auto__1 = _init_l_Lean_Option_register___auto__1();
    leanh::lean_mark_persistent(l_Lean_Option_register___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Options(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_ImportingFlag(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_KVMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_NameMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Options(builtin);
}