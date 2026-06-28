// Lean compiler output
// Module: Lean.Data.Options
// Imports: Lean.ImportingFlag Lean.Data.KVMap Lean.Data.NameMap.Basic Init.Data.ToString.Macro
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
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2,
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getOptional_x3f, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node7,
    l_Lean_addMacroScope, l_Lean_mkAtom, l_String_toRawSubstring_x27,
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
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{
    lean_string_append, lean_string_intercalate,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mul, lean_string_dec_eq, lean_string_utf8_byte_size,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l_Lean_Options_empty___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((1 as usize) << 1) | 1) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Options_empty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_empty___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Options_empty: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_empty___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Options_instInhabited: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_empty___closed__0_value) as *mut LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Options_instToString___private__1___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Options_instToString___private__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Name_instToString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Options_instToString___private__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: lean_data_value_to_string as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Options_instToString___private__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__3_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instToStringProd___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Options_instToString___private__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__4_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Options_instToString___private__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__5_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Options_instToString___private__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__6_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Options_instToString___private__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__7_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Options_instToString___private__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__8_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Options_instToString___private__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__9_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Options_instToString___private__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__10_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Options_instToString___private__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__11_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Options_instToString___private__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__12_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Options_instToString___private__1___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Options_instToString___private__1___closed__13_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Options_instToString___private__1___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Options_instToString___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Options_instToString___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Options_instToString___private__1___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Options_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Options_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instToString___closed__0_value) as *mut LeanObject;
pub static l_Lean_Options_instBEq___private__1___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_instBEqDataValue_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Options_instBEq___private__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instBEq___private__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Options_instBEq___private__1___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Options_instBEq___private__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instBEq___private__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Options_instBEq___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Options_instBEq___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Options_instBEq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instBEq___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Options_instBEq: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_instBEq___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Options_instEmptyCollection: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_empty___closed__0_value) as *mut LeanObject;
pub static l_Lean_Options_insert___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Options_insert___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_insert___closed__0_value) as *mut LeanObject;
pub static l_Lean_Options_insert___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Options_insert___closed__0_value) as *mut LeanObject,
        14231257465488249300 as *mut LeanObject,
    ],
};
static mut l_Lean_Options_insert___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Options_insert___closed__1_value) as *mut LeanObject;
pub static l_Lean_instInhabitedOptionDeprecation_default___closed__0_value: LeanStringObject<1> =
    LeanStringObject {
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
static mut l_Lean_instInhabitedOptionDeprecation_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedOptionDeprecation_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instInhabitedOptionDeprecation_default___closed__1_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instInhabitedOptionDeprecation_default___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_instInhabitedOptionDeprecation_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedOptionDeprecation_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_instInhabitedOptionDeprecation_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedOptionDeprecation_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_instInhabitedOptionDeprecation: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedOptionDeprecation_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__0_value: LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__1_value: LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__2_value: LeanStringObject<7> =
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
static mut l_Lean_OptionDecl_declName___autoParam___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__3_value: LeanStringObject<10> =
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
        m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__3_value)
        as *mut LeanObject;
static l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_OptionDecl_declName___autoParam___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__5_value: LeanArrayObject<0> =
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
static mut l_Lean_OptionDecl_declName___autoParam___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__6_value: LeanStringObject<19> =
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
            116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__6_value)
        as *mut LeanObject;
static l_Lean_OptionDecl_declName___autoParam___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_OptionDecl_declName___autoParam___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_OptionDecl_declName___autoParam___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_OptionDecl_declName___autoParam___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__8_value: LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__10_value: LeanStringObject<6> =
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
        m_data: [101, 120, 97, 99, 116, 0],
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__10_value)
        as *mut LeanObject;
static l_Lean_OptionDecl_declName___autoParam___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_OptionDecl_declName___autoParam___closed__11_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_OptionDecl_declName___autoParam___closed__11_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__11_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_OptionDecl_declName___autoParam___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__11_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__10_value)
                as *mut LeanObject,
            14997215300048349804 as *mut LeanObject,
        ],
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_OptionDecl_declName___autoParam___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_OptionDecl_declName___autoParam___closed__14_value: LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__15_value: LeanStringObject<9> =
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
        m_data: [100, 101, 99, 108, 78, 97, 109, 101, 0],
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__15_value)
        as *mut LeanObject;
static l_Lean_OptionDecl_declName___autoParam___closed__16_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_OptionDecl_declName___autoParam___closed__16_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__16_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_OptionDecl_declName___autoParam___closed__16_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__16_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__14_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_OptionDecl_declName___autoParam___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__16_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__15_value)
                as *mut LeanObject,
            7677164612348466033 as *mut LeanObject,
        ],
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_OptionDecl_declName___autoParam___closed__17_value: LeanStringObject<11> =
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
        m_data: [100, 101, 99, 108, 95, 110, 97, 109, 101, 37, 0],
    };
static mut l_Lean_OptionDecl_declName___autoParam___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__17_value)
        as *mut LeanObject;
static mut l_Lean_OptionDecl_declName___autoParam___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__27_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__27: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_OptionDecl_declName___autoParam___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_OptionDecl_declName___autoParam___closed__28: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_OptionDecl_declName___autoParam: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instInhabitedOptionDecl_default___closed__0_value: LeanStringObject<24> =
    LeanStringObject {
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
            105, 110, 115, 116, 73, 110, 104, 97, 98, 105, 116, 101, 100, 79, 112, 116, 105, 111,
            110, 68, 101, 99, 108, 0,
        ],
    };
static mut l_Lean_instInhabitedOptionDecl_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedOptionDecl_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instInhabitedOptionDecl_default___closed__1_value: LeanStringObject<8> =
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
        m_data: [100, 101, 102, 97, 117, 108, 116, 0],
    };
static mut l_Lean_instInhabitedOptionDecl_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedOptionDecl_default___closed__1_value)
        as *mut LeanObject;
static l_Lean_instInhabitedOptionDecl_default___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_instInhabitedOptionDecl_default___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instInhabitedOptionDecl_default___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instInhabitedOptionDecl_default___closed__0_value)
                as *mut LeanObject,
            12894178242470612343 as *mut LeanObject,
        ],
    };
pub static l_Lean_instInhabitedOptionDecl_default___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instInhabitedOptionDecl_default___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instInhabitedOptionDecl_default___closed__1_value)
                as *mut LeanObject,
            7948044940217330697 as *mut LeanObject,
        ],
    };
static mut l_Lean_instInhabitedOptionDecl_default___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedOptionDecl_default___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_instInhabitedOptionDecl_default___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedOptionDecl_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedOptionDecl_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instInhabitedOptionDecl: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_OptionDecl_fullDescr___closed__0_value: LeanStringObject<218> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_OptionDecl_fullDescr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_fullDescr___closed__0_value) as *mut LeanObject;
pub static l_Lean_OptionDecl_fullDescr___closed__1_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_OptionDecl_fullDescr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_fullDescr___closed__1_value) as *mut LeanObject;
pub static l_Lean_OptionDecl_fullDescr___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_OptionDecl_fullDescr___closed__1_value) as *mut LeanObject,
        15861075605163525197 as *mut LeanObject,
    ],
};
static mut l_Lean_OptionDecl_fullDescr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_fullDescr___closed__2_value) as *mut LeanObject;
pub static l_Lean_OptionDecl_fullDescr___closed__3_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_OptionDecl_fullDescr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_OptionDecl_fullDescr___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_instInhabitedOptionDecls: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_registerOption___closed__0_value: LeanStringObject<80> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 80,
    m_capacity: 80,
    m_length: 79,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 103, 105, 115, 116, 101, 114, 32,
        111, 112, 116, 105, 111, 110, 58, 32, 79, 112, 116, 105, 111, 110, 115, 32, 99, 97, 110,
        32, 111, 110, 108, 121, 32, 98, 101, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101, 100,
        32, 100, 117, 114, 105, 110, 103, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116,
        105, 111, 110, 0,
    ],
};
static mut l_Lean_registerOption___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerOption___closed__0_value) as *mut LeanObject;
static mut l_Lean_registerOption___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerOption___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_registerOption___closed__2_value: LeanStringObject<29> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        73, 110, 118, 97, 108, 105, 100, 32, 111, 112, 116, 105, 111, 110, 32, 100, 101, 99, 108,
        97, 114, 97, 116, 105, 111, 110, 32, 96, 0,
    ],
};
static mut l_Lean_registerOption___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerOption___closed__2_value) as *mut LeanObject;
pub static l_Lean_registerOption___closed__3_value: LeanStringObject<25> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        96, 58, 32, 79, 112, 116, 105, 111, 110, 32, 97, 108, 114, 101, 97, 100, 121, 32, 101, 120,
        105, 115, 116, 115, 0,
    ],
};
static mut l_Lean_registerOption___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerOption___closed__3_value) as *mut LeanObject;
pub static l_Lean_getOptionDeclsArray___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_getOptionDeclsArray___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getOptionDeclsArray___closed__0_value) as *mut LeanObject;
pub static l_Lean_getOptionDecl___closed__0_value: LeanStringObject<17> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_getOptionDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getOptionDecl___closed__0_value) as *mut LeanObject;
pub static l_Lean_getOptionDecl___closed__1_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_getOptionDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getOptionDecl___closed__1_value) as *mut LeanObject;
pub static l_Lean_withInPattern___redArg___lam__0___closed__0_value: LeanStringObject<11> =
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
        m_data: [95, 105, 110, 80, 97, 116, 116, 101, 114, 110, 0],
    };
static mut l_Lean_withInPattern___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_withInPattern___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_withInPattern___redArg___lam__0___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_withInPattern___redArg___lam__0___closed__0_value)
                as *mut LeanObject,
            1702504630968652677 as *mut LeanObject,
        ],
    };
static mut l_Lean_withInPattern___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_withInPattern___redArg___lam__0___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_withInPattern___redArg___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_withInPattern___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Option_register___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Option_registerBuiltinOption___closed__0_value: LeanStringObject<7> =
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
        m_data: [79, 112, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__0_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__1_value: LeanStringObject<22> =
    LeanStringObject {
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
            114, 101, 103, 105, 115, 116, 101, 114, 66, 117, 105, 108, 116, 105, 110, 79, 112, 116,
            105, 111, 110, 0,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__1_value) as *mut LeanObject;
static l_Lean_Option_registerBuiltinOption___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Option_registerBuiltinOption___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__0_value)
                as *mut LeanObject,
            3127099019797772086 as *mut LeanObject,
        ],
    };
pub static l_Lean_Option_registerBuiltinOption___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__1_value)
                as *mut LeanObject,
            5912347743684231271 as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__2_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__3_value: LeanStringObject<8> =
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
static mut l_Lean_Option_registerBuiltinOption___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__3_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__3_value)
                as *mut LeanObject,
            12571085391447129896 as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__5_value: LeanStringObject<9> =
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
static mut l_Lean_Option_registerBuiltinOption___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__5_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__5_value)
                as *mut LeanObject,
            18170484695678750185 as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__6_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__7_value: LeanStringObject<11> =
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
static mut l_Lean_Option_registerBuiltinOption___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__7_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__7_value)
                as *mut LeanObject,
            3961966953292576997 as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__8_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__9_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__10_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__10_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__11_value: LeanStringObject<11> =
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
        m_data: [118, 105, 115, 105, 98, 105, 108, 105, 116, 121, 0],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__11_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__11_value)
                as *mut LeanObject,
            18370519569176055110 as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__12_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__13_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__13_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__14_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__14_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__15_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__15_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__16_value: LeanStringObject<24> =
    LeanStringObject {
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
            114, 101, 103, 105, 115, 116, 101, 114, 95, 98, 117, 105, 108, 116, 105, 110, 95, 111,
            112, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__16_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__17_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__17_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__18_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__15_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__18_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__19_value: LeanStringObject<6> =
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
        m_data: [105, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__19_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__20_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__19_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__20_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__21_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__21_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__22_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__18_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__21_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__22_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__23_value: LeanStringObject<4> =
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
        m_data: [32, 58, 32, 0],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__23_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__24_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__23_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__24_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__25_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__22_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__24_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__25_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__26_value: LeanStringObject<5> =
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
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__26_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__27_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__26_value)
                as *mut LeanObject,
            8609355255726335675 as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__27_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__28_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__27_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__28_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__29_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__25_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__28_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__29_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__30_value: LeanStringObject<5> =
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
        m_data: [32, 58, 61, 32, 0],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__30_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__31_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__30_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__31_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__32_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__29_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__31_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__32_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__33_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__32_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__28_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__33_value) as *mut LeanObject;
pub static l_Lean_Option_registerBuiltinOption___closed__34_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__2_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__33_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Option_registerBuiltinOption___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__34_value) as *mut LeanObject;
pub static mut l_Lean_Option_registerBuiltinOption: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__34_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 75, 101, 121, 119, 111, 114, 100, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__5_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [76, 101, 97, 110, 46, 79, 112, 116, 105, 111, 110, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__5_value) as *mut LeanObject;
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6: *mut LeanObject = core::ptr::null_mut();
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__0_value) as *mut LeanObject,3127099019797772086 as *mut LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__8_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__8_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__9_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7_value) as *mut LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__9_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__10_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__9_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__10_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__10_value) as *mut LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 144, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 111, 83, 101, 113, 73, 110, 100, 101, 110, 116, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 83, 101, 113, 73, 116, 101, 109, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 111, 69, 120, 112, 114, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__16_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [76, 101, 97, 110, 46, 79, 112, 116, 105, 111, 110, 46, 114, 101, 103, 105, 115, 116, 101, 114, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__16_value) as *mut LeanObject;
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__18_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [114, 101, 103, 105, 115, 116, 101, 114, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__18_value) as *mut LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__0_value) as *mut LeanObject,3127099019797772086 as *mut LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__18_value) as *mut LeanObject,11387295883396010367 as *mut LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__20_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__20_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__20_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25_value) as *mut LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25_value) as *mut LeanObject,12014440461648055863 as *mut LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value) as *mut LeanObject;
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27_value) as *mut LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27_value) as *mut LeanObject,14557702332550915328 as *mut LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value) as *mut LeanObject;
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Option_registerOption___closed__0_value: LeanStringObject<15> =
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
            114, 101, 103, 105, 115, 116, 101, 114, 79, 112, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Option_registerOption___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__0_value) as *mut LeanObject;
static l_Lean_Option_registerOption___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Option_registerOption___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Option_registerOption___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__0_value)
            as *mut LeanObject,
        3127099019797772086 as *mut LeanObject,
    ],
};
pub static l_Lean_Option_registerOption___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Option_registerOption___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Option_registerOption___closed__0_value) as *mut LeanObject,
        3829388930784714694 as *mut LeanObject,
    ],
};
static mut l_Lean_Option_registerOption___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__1_value) as *mut LeanObject;
pub static l_Lean_Option_registerOption___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27_value) as *mut LeanObject,9573766061812123505 as *mut LeanObject] };
static mut l_Lean_Option_registerOption___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__2_value) as *mut LeanObject;
pub static l_Lean_Option_registerOption___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Option_registerOption___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Option_registerOption___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__3_value) as *mut LeanObject;
pub static l_Lean_Option_registerOption___closed__4_value: LeanStringObject<16> =
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
            114, 101, 103, 105, 115, 116, 101, 114, 95, 111, 112, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Option_registerOption___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__4_value) as *mut LeanObject;
pub static l_Lean_Option_registerOption___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Option_registerOption___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Option_registerOption___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__5_value) as *mut LeanObject;
pub static l_Lean_Option_registerOption___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Option_registerOption___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Option_registerOption___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Option_registerOption___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__6_value) as *mut LeanObject;
pub static l_Lean_Option_registerOption___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Option_registerOption___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__21_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Option_registerOption___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__7_value) as *mut LeanObject;
pub static l_Lean_Option_registerOption___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Option_registerOption___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__24_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Option_registerOption___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__8_value) as *mut LeanObject;
pub static l_Lean_Option_registerOption___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Option_registerOption___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__28_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Option_registerOption___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__9_value) as *mut LeanObject;
pub static l_Lean_Option_registerOption___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Option_registerOption___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__31_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Option_registerOption___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__10_value) as *mut LeanObject;
pub static l_Lean_Option_registerOption___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__4_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Option_registerOption___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Option_registerBuiltinOption___closed__28_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Option_registerOption___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__11_value) as *mut LeanObject;
pub static l_Lean_Option_registerOption___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Option_registerOption___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Option_registerOption___closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Option_registerOption___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__12_value) as *mut LeanObject;
pub static mut l_Lean_Option_registerOption: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Option_registerOption___closed__12_value) as *mut LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0_value) as *mut LeanObject,387456110215466097 as *mut LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value) as *mut LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__14_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2_value) as *mut LeanObject,4498178684837002829 as *mut LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value) as *mut LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__14_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value) as *mut LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__14_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13_value) as *mut LeanObject,3326968124746134365 as *mut LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value) as *mut LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__14_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14_value) as *mut LeanObject,940684074193935882 as *mut LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value) as *mut LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__14_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15_value) as *mut LeanObject,5573444893818005634 as *mut LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value) as *mut LeanObject;
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_OptionDecl_declName___autoParam___closed__14_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22_value) as *mut LeanObject,9368229134555052249 as *mut LeanObject] };
static mut l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value) as *mut LeanObject;
pub unsafe fn lean_options_get_empty(mut v_x_2240_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    v___x_2241_ = l_Lean_Options_empty;
    return v___x_2241_;
}
pub unsafe fn l_Lean_Options_instToString___private__1___lam__0(
    mut v_x1_2243_: *mut LeanObject,
    mut v_x2_2244_: *mut LeanObject,
    mut v_x3_2245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    v___x_2246_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2246_, 0, v_x1_2243_);
    lean_ctor_set(v___x_2246_, 1, v_x2_2244_);
    v___x_2247_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2247_, 0, v___x_2246_);
    lean_ctor_set(v___x_2247_, 1, v_x3_2245_);
    return v___x_2247_;
}
pub unsafe fn l_Lean_Options_instToString___private__1(
    mut v_o_2273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    v_map_2274_ = lean_ctor_get(v_o_2273_, 0);
    lean_inc(v_map_2274_);
    lean_dec_ref(v_o_2273_);
    v___f_2275_ = l_Lean_Options_instToString___private__1___closed__0;
    v___f_2276_ = l_Lean_Options_instToString___private__1___closed__3;
    v___x_2277_ = lean_box(0);
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
    mut v___f_2281_: *mut LeanObject,
    mut v_o_2282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    v_map_2283_ = lean_ctor_get(v_o_2282_, 0);
    lean_inc(v_map_2283_);
    lean_dec_ref(v_o_2282_);
    v___f_2284_ = l_Lean_Options_instToString___private__1___closed__3;
    v___x_2285_ = lean_box(0);
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
    mut v_f_2292_: *mut LeanObject,
    mut v_a_2293_: *mut LeanObject,
    mut v_b_2294_: *mut LeanObject,
    mut v_c_2295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    v___x_2296_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2296_, 0, v_a_2293_);
    lean_ctor_set(v___x_2296_, 1, v_b_2294_);
    v___x_2297_ = lean_apply_2(v_f_2292_, v___x_2296_, v_c_2295_);
    return v___x_2297_;
}
pub unsafe fn l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1(
    mut v_toPure_2298_: *mut LeanObject,
    mut v_____do__lift_2299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    v_a_2300_ = lean_ctor_get(v_____do__lift_2299_, 0);
    lean_inc(v_a_2300_);
    lean_dec_ref(v_____do__lift_2299_);
    v___x_2301_ = lean_apply_2(v_toPure_2298_, lean_box(0), v_a_2300_);
    return v___x_2301_;
}
pub unsafe fn l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg(
    mut v_inst_2302_: *mut LeanObject,
    mut v_o_2303_: *mut LeanObject,
    mut v_init_2304_: *mut LeanObject,
    mut v_f_2305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2306_ = lean_ctor_get(v_inst_2302_, 0);
    v_map_2307_ = lean_ctor_get(v_o_2303_, 0);
    lean_inc(v_map_2307_);
    lean_dec_ref(v_o_2303_);
    v_toBind_2308_ = lean_ctor_get(v_inst_2302_, 1);
    lean_inc(v_toBind_2308_);
    v_toPure_2309_ = lean_ctor_get(v_toApplicative_2306_, 1);
    lean_inc(v_toPure_2309_);
    v___f_2310_ = lean_alloc_closure(
        l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2310_, 0, v_f_2305_);
    v___x_2311_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2302_,
        v___f_2310_,
        v_init_2304_,
        v_map_2307_,
    );
    v___f_2312_ = lean_alloc_closure(
        l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2312_, 0, v_toPure_2309_);
    v___x_2313_ = lean_apply_4(
        v_toBind_2308_,
        lean_box(0),
        lean_box(0),
        v___x_2311_,
        v___f_2312_,
    );
    return v___x_2313_;
}
pub unsafe fn l_Lean_Options_instForInProdNameDataValueOfMonad___private__1(
    mut v_m_2314_: *mut LeanObject,
    mut v_inst_2315_: *mut LeanObject,
    mut v_00_u03b2_2316_: *mut LeanObject,
    mut v_o_2317_: *mut LeanObject,
    mut v_init_2318_: *mut LeanObject,
    mut v_f_2319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2320_ = lean_ctor_get(v_inst_2315_, 0);
    v_map_2321_ = lean_ctor_get(v_o_2317_, 0);
    lean_inc(v_map_2321_);
    lean_dec_ref(v_o_2317_);
    v_toBind_2322_ = lean_ctor_get(v_inst_2315_, 1);
    lean_inc(v_toBind_2322_);
    v_toPure_2323_ = lean_ctor_get(v_toApplicative_2320_, 1);
    lean_inc(v_toPure_2323_);
    v___f_2324_ = lean_alloc_closure(
        l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2324_, 0, v_f_2319_);
    v___x_2325_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2315_,
        v___f_2324_,
        v_init_2318_,
        v_map_2321_,
    );
    v___f_2326_ = lean_alloc_closure(
        l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2326_, 0, v_toPure_2323_);
    v___x_2327_ = lean_apply_4(
        v_toBind_2322_,
        lean_box(0),
        lean_box(0),
        v___x_2325_,
        v___f_2326_,
    );
    return v___x_2327_;
}
pub unsafe fn l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__2(
    mut v_inst_2328_: *mut LeanObject,
    mut v_00_u03b2_2329_: *mut LeanObject,
    mut v_o_2330_: *mut LeanObject,
    mut v_init_2331_: *mut LeanObject,
    mut v_f_2332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2333_ = lean_ctor_get(v_inst_2328_, 0);
    v_map_2334_ = lean_ctor_get(v_o_2330_, 0);
    lean_inc(v_map_2334_);
    lean_dec_ref(v_o_2330_);
    v_toBind_2335_ = lean_ctor_get(v_inst_2328_, 1);
    lean_inc(v_toBind_2335_);
    v_toPure_2336_ = lean_ctor_get(v_toApplicative_2333_, 1);
    lean_inc(v_toPure_2336_);
    v___f_2337_ = lean_alloc_closure(
        l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2337_, 0, v_f_2332_);
    v___x_2338_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2328_,
        v___f_2337_,
        v_init_2331_,
        v_map_2334_,
    );
    v___f_2339_ = lean_alloc_closure(
        l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2339_, 0, v_toPure_2336_);
    v___x_2340_ = lean_apply_4(
        v_toBind_2335_,
        lean_box(0),
        lean_box(0),
        v___x_2338_,
        v___f_2339_,
    );
    return v___x_2340_;
}
pub unsafe fn l_Lean_Options_instForInProdNameDataValueOfMonad___redArg(
    mut v_inst_2341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2342_: *mut LeanObject = core::ptr::null_mut();
    v___f_2342_ = lean_alloc_closure(
        l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_2342_, 0, v_inst_2341_);
    return v___f_2342_;
}
pub unsafe fn l_Lean_Options_instForInProdNameDataValueOfMonad(
    mut v_m_2343_: *mut LeanObject,
    mut v_inst_2344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2345_: *mut LeanObject = core::ptr::null_mut();
    v___f_2345_ = lean_alloc_closure(
        l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_2345_, 0, v_inst_2344_);
    return v___f_2345_;
}
pub unsafe fn l_Lean_Options_instBEq___private__1(
    mut v_o1_2348_: *mut LeanObject,
    mut v_o2_2349_: *mut LeanObject,
) -> u8 {
    let mut v_map_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: u8 = 0;
    v_map_2350_ = lean_ctor_get(v_o1_2348_, 0);
    lean_inc(v_map_2350_);
    lean_dec_ref(v_o1_2348_);
    v_map_2351_ = lean_ctor_get(v_o2_2349_, 0);
    lean_inc(v_map_2351_);
    lean_dec_ref(v_o2_2349_);
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
    mut v_o1_2355_: *mut LeanObject,
    mut v_o2_2356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2357_: u8 = 0;
    let mut v_r_2358_: *mut LeanObject = core::ptr::null_mut();
    v_res_2357_ = l_Lean_Options_instBEq___private__1(v_o1_2355_, v_o2_2356_);
    v_r_2358_ = lean_box((v_res_2357_) as usize);
    return v_r_2358_;
}
pub unsafe fn l_Lean_Options_instBEq___lam__0(
    mut v_o1_2359_: *mut LeanObject,
    mut v_o2_2360_: *mut LeanObject,
) -> u8 {
    let mut v_map_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: u8 = 0;
    v_map_2361_ = lean_ctor_get(v_o1_2359_, 0);
    lean_inc(v_map_2361_);
    lean_dec_ref(v_o1_2359_);
    v_map_2362_ = lean_ctor_get(v_o2_2360_, 0);
    lean_inc(v_map_2362_);
    lean_dec_ref(v_o2_2360_);
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
    mut v_o1_2366_: *mut LeanObject,
    mut v_o2_2367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2368_: u8 = 0;
    let mut v_r_2369_: *mut LeanObject = core::ptr::null_mut();
    v_res_2368_ = l_Lean_Options_instBEq___lam__0(v_o1_2366_, v_o2_2367_);
    v_r_2369_ = lean_box((v_res_2368_) as usize);
    return v_r_2369_;
}
pub unsafe fn l_Lean_Options_find_x3f(
    mut v_o_2373_: *mut LeanObject,
    mut v_k_2374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    v_map_2375_ = lean_ctor_get(v_o_2373_, 0);
    v___x_2376_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2375_,
            v_k_2374_,
        );
    return v___x_2376_;
}
pub unsafe fn l_Lean_Options_find_x3f___boxed(
    mut v_o_2377_: *mut LeanObject,
    mut v_k_2378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2379_: *mut LeanObject = core::ptr::null_mut();
    v_res_2379_ = l_Lean_Options_find_x3f(v_o_2377_, v_k_2378_);
    lean_dec(v_k_2378_);
    lean_dec_ref(v_o_2377_);
    return v_res_2379_;
}
pub unsafe fn l_Lean_Options_find(
    mut v_o_2380_: *mut LeanObject,
    mut v_k_2381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    v_map_2382_ = lean_ctor_get(v_o_2380_, 0);
    v___x_2383_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2382_,
            v_k_2381_,
        );
    return v___x_2383_;
}
pub unsafe fn l_Lean_Options_find___boxed(
    mut v_o_2384_: *mut LeanObject,
    mut v_k_2385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2386_: *mut LeanObject = core::ptr::null_mut();
    v_res_2386_ = l_Lean_Options_find(v_o_2384_, v_k_2385_);
    lean_dec(v_k_2385_);
    lean_dec_ref(v_o_2384_);
    return v_res_2386_;
}
pub unsafe fn l_Lean_Options_get_x3f___redArg(
    mut v_inst_2387_: *mut LeanObject,
    mut v_o_2388_: *mut LeanObject,
    mut v_k_2389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofDataValue_x3f_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    v_map_2390_ = lean_ctor_get(v_o_2388_, 0);
    v_ofDataValue_x3f_2391_ = lean_ctor_get(v_inst_2387_, 1);
    lean_inc_ref(v_ofDataValue_x3f_2391_);
    lean_dec_ref(v_inst_2387_);
    v___x_2392_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2390_,
            v_k_2389_,
        );
    if lean_obj_tag(v___x_2392_) == 0 {
        let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_ofDataValue_x3f_2391_);
        v___x_2393_ = lean_box(0);
        return v___x_2393_;
    } else {
        let mut v_val_2394_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
        v_val_2394_ = lean_ctor_get(v___x_2392_, 0);
        lean_inc(v_val_2394_);
        lean_dec_ref_known(v___x_2392_, 1);
        v___x_2395_ = lean_apply_1(v_ofDataValue_x3f_2391_, v_val_2394_);
        return v___x_2395_;
    }
}
pub unsafe fn l_Lean_Options_get_x3f___redArg___boxed(
    mut v_inst_2396_: *mut LeanObject,
    mut v_o_2397_: *mut LeanObject,
    mut v_k_2398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2399_: *mut LeanObject = core::ptr::null_mut();
    v_res_2399_ = l_Lean_Options_get_x3f___redArg(v_inst_2396_, v_o_2397_, v_k_2398_);
    lean_dec(v_k_2398_);
    lean_dec_ref(v_o_2397_);
    return v_res_2399_;
}
pub unsafe fn l_Lean_Options_get_x3f(
    mut v_00_u03b1_2400_: *mut LeanObject,
    mut v_inst_2401_: *mut LeanObject,
    mut v_o_2402_: *mut LeanObject,
    mut v_k_2403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofDataValue_x3f_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    v_map_2404_ = lean_ctor_get(v_o_2402_, 0);
    v_ofDataValue_x3f_2405_ = lean_ctor_get(v_inst_2401_, 1);
    lean_inc_ref(v_ofDataValue_x3f_2405_);
    lean_dec_ref(v_inst_2401_);
    v___x_2406_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2404_,
            v_k_2403_,
        );
    if lean_obj_tag(v___x_2406_) == 0 {
        let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_ofDataValue_x3f_2405_);
        v___x_2407_ = lean_box(0);
        return v___x_2407_;
    } else {
        let mut v_val_2408_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
        v_val_2408_ = lean_ctor_get(v___x_2406_, 0);
        lean_inc(v_val_2408_);
        lean_dec_ref_known(v___x_2406_, 1);
        v___x_2409_ = lean_apply_1(v_ofDataValue_x3f_2405_, v_val_2408_);
        return v___x_2409_;
    }
}
pub unsafe fn l_Lean_Options_get_x3f___boxed(
    mut v_00_u03b1_2410_: *mut LeanObject,
    mut v_inst_2411_: *mut LeanObject,
    mut v_o_2412_: *mut LeanObject,
    mut v_k_2413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2414_: *mut LeanObject = core::ptr::null_mut();
    v_res_2414_ = l_Lean_Options_get_x3f(v_00_u03b1_2410_, v_inst_2411_, v_o_2412_, v_k_2413_);
    lean_dec(v_k_2413_);
    lean_dec_ref(v_o_2412_);
    return v_res_2414_;
}
pub unsafe fn l_Lean_Options_get___redArg(
    mut v_inst_2415_: *mut LeanObject,
    mut v_o_2416_: *mut LeanObject,
    mut v_k_2417_: *mut LeanObject,
    mut v_defVal_2418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofDataValue_x3f_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    v_map_2419_ = lean_ctor_get(v_o_2416_, 0);
    v_ofDataValue_x3f_2420_ = lean_ctor_get(v_inst_2415_, 1);
    lean_inc_ref(v_ofDataValue_x3f_2420_);
    lean_dec_ref(v_inst_2415_);
    v___x_2421_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2419_,
            v_k_2417_,
        );
    if lean_obj_tag(v___x_2421_) == 0 {
        lean_dec_ref(v_ofDataValue_x3f_2420_);
        lean_inc(v_defVal_2418_);
        return v_defVal_2418_;
    } else {
        let mut v_val_2422_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
        v_val_2422_ = lean_ctor_get(v___x_2421_, 0);
        lean_inc(v_val_2422_);
        lean_dec_ref_known(v___x_2421_, 1);
        v___x_2423_ = lean_apply_1(v_ofDataValue_x3f_2420_, v_val_2422_);
        if lean_obj_tag(v___x_2423_) == 0 {
            lean_inc(v_defVal_2418_);
            return v_defVal_2418_;
        } else {
            let mut v_val_2424_: *mut LeanObject = core::ptr::null_mut();
            v_val_2424_ = lean_ctor_get(v___x_2423_, 0);
            lean_inc(v_val_2424_);
            lean_dec_ref_known(v___x_2423_, 1);
            return v_val_2424_;
        }
    }
}
pub unsafe fn l_Lean_Options_get___redArg___boxed(
    mut v_inst_2425_: *mut LeanObject,
    mut v_o_2426_: *mut LeanObject,
    mut v_k_2427_: *mut LeanObject,
    mut v_defVal_2428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2429_: *mut LeanObject = core::ptr::null_mut();
    v_res_2429_ = l_Lean_Options_get___redArg(v_inst_2425_, v_o_2426_, v_k_2427_, v_defVal_2428_);
    lean_dec(v_defVal_2428_);
    lean_dec(v_k_2427_);
    lean_dec_ref(v_o_2426_);
    return v_res_2429_;
}
pub unsafe fn l_Lean_Options_get(
    mut v_00_u03b1_2430_: *mut LeanObject,
    mut v_inst_2431_: *mut LeanObject,
    mut v_o_2432_: *mut LeanObject,
    mut v_k_2433_: *mut LeanObject,
    mut v_defVal_2434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofDataValue_x3f_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    v_map_2435_ = lean_ctor_get(v_o_2432_, 0);
    v_ofDataValue_x3f_2436_ = lean_ctor_get(v_inst_2431_, 1);
    lean_inc_ref(v_ofDataValue_x3f_2436_);
    lean_dec_ref(v_inst_2431_);
    v___x_2437_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2435_,
            v_k_2433_,
        );
    if lean_obj_tag(v___x_2437_) == 0 {
        lean_dec_ref(v_ofDataValue_x3f_2436_);
        lean_inc(v_defVal_2434_);
        return v_defVal_2434_;
    } else {
        let mut v_val_2438_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
        v_val_2438_ = lean_ctor_get(v___x_2437_, 0);
        lean_inc(v_val_2438_);
        lean_dec_ref_known(v___x_2437_, 1);
        v___x_2439_ = lean_apply_1(v_ofDataValue_x3f_2436_, v_val_2438_);
        if lean_obj_tag(v___x_2439_) == 0 {
            lean_inc(v_defVal_2434_);
            return v_defVal_2434_;
        } else {
            let mut v_val_2440_: *mut LeanObject = core::ptr::null_mut();
            v_val_2440_ = lean_ctor_get(v___x_2439_, 0);
            lean_inc(v_val_2440_);
            lean_dec_ref_known(v___x_2439_, 1);
            return v_val_2440_;
        }
    }
}
pub unsafe fn l_Lean_Options_get___boxed(
    mut v_00_u03b1_2441_: *mut LeanObject,
    mut v_inst_2442_: *mut LeanObject,
    mut v_o_2443_: *mut LeanObject,
    mut v_k_2444_: *mut LeanObject,
    mut v_defVal_2445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2446_: *mut LeanObject = core::ptr::null_mut();
    v_res_2446_ = l_Lean_Options_get(
        v_00_u03b1_2441_,
        v_inst_2442_,
        v_o_2443_,
        v_k_2444_,
        v_defVal_2445_,
    );
    lean_dec(v_defVal_2445_);
    lean_dec(v_k_2444_);
    lean_dec_ref(v_o_2443_);
    return v_res_2446_;
}
pub unsafe fn l_Lean_Options_getBool(
    mut v_o_2447_: *mut LeanObject,
    mut v_k_2448_: *mut LeanObject,
    mut v_defVal_2449_: u8,
) -> u8 {
    let mut v_map_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    v_map_2450_ = lean_ctor_get(v_o_2447_, 0);
    v___x_2451_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2450_,
            v_k_2448_,
        );
    if lean_obj_tag(v___x_2451_) == 0 {
        return v_defVal_2449_;
    } else {
        let mut v_val_2452_: *mut LeanObject = core::ptr::null_mut();
        v_val_2452_ = lean_ctor_get(v___x_2451_, 0);
        lean_inc(v_val_2452_);
        lean_dec_ref_known(v___x_2451_, 1);
        if lean_obj_tag(v_val_2452_) == 1 {
            let mut v_v_2453_: u8 = 0;
            v_v_2453_ = lean_ctor_get_uint8(v_val_2452_, 0 as u32);
            lean_dec_ref_known(v_val_2452_, 0);
            return v_v_2453_;
        } else {
            lean_dec(v_val_2452_);
            return v_defVal_2449_;
        }
    }
}
pub unsafe fn l_Lean_Options_getBool___boxed(
    mut v_o_2454_: *mut LeanObject,
    mut v_k_2455_: *mut LeanObject,
    mut v_defVal_2456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defVal_boxed_2457_: u8 = 0;
    let mut v_res_2458_: u8 = 0;
    let mut v_r_2459_: *mut LeanObject = core::ptr::null_mut();
    v_defVal_boxed_2457_ = (lean_unbox(v_defVal_2456_) as u8);
    v_res_2458_ = l_Lean_Options_getBool(v_o_2454_, v_k_2455_, v_defVal_boxed_2457_);
    lean_dec(v_k_2455_);
    lean_dec_ref(v_o_2454_);
    v_r_2459_ = lean_box((v_res_2458_) as usize);
    return v_r_2459_;
}
pub unsafe fn l_Lean_Options_contains(
    mut v_o_2460_: *mut LeanObject,
    mut v_k_2461_: *mut LeanObject,
) -> u8 {
    let mut v_map_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: u8 = 0;
    v_map_2462_ = lean_ctor_get(v_o_2460_, 0);
    v___x_2463_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(
            v_k_2461_,
            v_map_2462_,
        );
    return v___x_2463_;
}
pub unsafe fn l_Lean_Options_contains___boxed(
    mut v_o_2464_: *mut LeanObject,
    mut v_k_2465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2466_: u8 = 0;
    let mut v_r_2467_: *mut LeanObject = core::ptr::null_mut();
    v_res_2466_ = l_Lean_Options_contains(v_o_2464_, v_k_2465_);
    lean_dec(v_k_2465_);
    lean_dec_ref(v_o_2464_);
    v_r_2467_ = lean_box((v_res_2466_) as usize);
    return v_r_2467_;
}
pub unsafe fn l_Lean_Options_insert(
    mut v_o_2471_: *mut LeanObject,
    mut v_k_2472_: *mut LeanObject,
    mut v_v_2473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2475_: u8 = 0;
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2478_: u8 = 0;
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: u8 = 0;
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_2474_ = lean_ctor_get(v_o_2471_, 0);
                v_hasTrace_2475_ = lean_ctor_get_uint8(
                    v_o_2471_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2488_ = (!lean_is_exclusive(v_o_2471_)) as u8;
                if v_isSharedCheck_2488_ == 0 {
                    v___x_2477_ = v_o_2471_;
                    v_isShared_2478_ = v_isSharedCheck_2488_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_2474_);
                    lean_dec(v_o_2471_);
                    v___x_2477_ = lean_box(0);
                    v_isShared_2478_ = v_isSharedCheck_2488_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_k_2472_);
                v___x_2479_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2472_, v_v_2473_, v_map_2474_);
                if v_hasTrace_2475_ == 0 {
                    v___x_2480_ = l_Lean_Options_insert___closed__1;
                    v___x_2481_ = l_Lean_Name_isPrefixOf(v___x_2480_, v_k_2472_);
                    lean_dec(v_k_2472_);
                    if v_isShared_2478_ == 0 {
                        lean_ctor_set(v___x_2477_, 0, v___x_2479_);
                        v___x_2483_ = v___x_2477_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2479_);
                        v___x_2483_ = v_reuseFailAlloc_2484_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_k_2472_);
                    if v_isShared_2478_ == 0 {
                        lean_ctor_set(v___x_2477_, 0, v___x_2479_);
                        v___x_2486_ = v___x_2477_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2479_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2487_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v_hasTrace_2475_,
                        );
                        v___x_2486_ = v_reuseFailAlloc_2487_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_2483_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_inst_2489_: *mut LeanObject,
    mut v_o_2490_: *mut LeanObject,
    mut v_k_2491_: *mut LeanObject,
    mut v_v_2492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toDataValue_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2495_: u8 = 0;
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2498_: u8 = 0;
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: u8 = 0;
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2509_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toDataValue_2493_ = lean_ctor_get(v_inst_2489_, 0);
                lean_inc_ref(v_toDataValue_2493_);
                lean_dec_ref(v_inst_2489_);
                v_map_2494_ = lean_ctor_get(v_o_2490_, 0);
                v_hasTrace_2495_ = lean_ctor_get_uint8(
                    v_o_2490_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2509_ = (!lean_is_exclusive(v_o_2490_)) as u8;
                if v_isSharedCheck_2509_ == 0 {
                    v___x_2497_ = v_o_2490_;
                    v_isShared_2498_ = v_isSharedCheck_2509_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_2494_);
                    lean_dec(v_o_2490_);
                    v___x_2497_ = lean_box(0);
                    v_isShared_2498_ = v_isSharedCheck_2509_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2499_ = lean_apply_1(v_toDataValue_2493_, v_v_2492_);
                lean_inc(v_k_2491_);
                v___x_2500_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2491_, v___x_2499_, v_map_2494_);
                if v_hasTrace_2495_ == 0 {
                    v___x_2501_ = l_Lean_Options_insert___closed__1;
                    v___x_2502_ = l_Lean_Name_isPrefixOf(v___x_2501_, v_k_2491_);
                    lean_dec(v_k_2491_);
                    if v_isShared_2498_ == 0 {
                        lean_ctor_set(v___x_2497_, 0, v___x_2500_);
                        v___x_2504_ = v___x_2497_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2500_);
                        v___x_2504_ = v_reuseFailAlloc_2505_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_k_2491_);
                    if v_isShared_2498_ == 0 {
                        lean_ctor_set(v___x_2497_, 0, v___x_2500_);
                        v___x_2507_ = v___x_2497_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2500_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2508_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v_hasTrace_2495_,
                        );
                        v___x_2507_ = v_reuseFailAlloc_2508_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_2504_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_00_u03b1_2510_: *mut LeanObject,
    mut v_inst_2511_: *mut LeanObject,
    mut v_o_2512_: *mut LeanObject,
    mut v_k_2513_: *mut LeanObject,
    mut v_v_2514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    v___x_2515_ = l_Lean_Options_set___redArg(v_inst_2511_, v_o_2512_, v_k_2513_, v_v_2514_);
    return v___x_2515_;
}
pub unsafe fn l_Lean_Options_setBool(
    mut v_o_2516_: *mut LeanObject,
    mut v_k_2517_: *mut LeanObject,
    mut v_v_2518_: u8,
) -> *mut LeanObject {
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    v___x_2519_ = l_Lean_KVMap_instValueBool;
    v___x_2520_ = lean_box((v_v_2518_) as usize);
    v___x_2521_ = l_Lean_Options_set___redArg(v___x_2519_, v_o_2516_, v_k_2517_, v___x_2520_);
    return v___x_2521_;
}
pub unsafe fn l_Lean_Options_setBool___boxed(
    mut v_o_2522_: *mut LeanObject,
    mut v_k_2523_: *mut LeanObject,
    mut v_v_2524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_2525_: u8 = 0;
    let mut v_res_2526_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_2525_ = (lean_unbox(v_v_2524_) as u8);
    v_res_2526_ = l_Lean_Options_setBool(v_o_2522_, v_k_2523_, v_v_boxed_2525_);
    return v_res_2526_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(
    mut v_init_2527_: *mut LeanObject,
    mut v_x_2528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2528_) == 0 {
                    v_k_2529_ = lean_ctor_get(v_x_2528_, 1);
                    v_l_2530_ = lean_ctor_get(v_x_2528_, 3);
                    v_r_2531_ = lean_ctor_get(v_x_2528_, 4);
                    v___x_2532_ =
                        l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(
                            v_init_2527_,
                            v_r_2531_,
                        );
                    lean_inc(v_k_2529_);
                    v___x_2533_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2533_, 0, v_k_2529_);
                    lean_ctor_set(v___x_2533_, 1, v___x_2532_);
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
    mut v_init_2535_: *mut LeanObject,
    mut v_x_2536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2537_: *mut LeanObject = core::ptr::null_mut();
    v_res_2537_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(
        v_init_2535_,
        v_x_2536_,
    );
    lean_dec(v_x_2536_);
    return v_res_2537_;
}
pub unsafe fn l_List_any___at___00Lean_Options_erase_spec__2(mut v_x_2538_: *mut LeanObject) -> u8 {
    let mut v___x_2539_: u8 = 0;
    let mut v_head_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2538_) == 0 {
                    v___x_2539_ = 0;
                    return v___x_2539_;
                } else {
                    v_head_2540_ = lean_ctor_get(v_x_2538_, 0);
                    v_tail_2541_ = lean_ctor_get(v_x_2538_, 1);
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
    mut v_x_2545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2546_: u8 = 0;
    let mut v_r_2547_: *mut LeanObject = core::ptr::null_mut();
    v_res_2546_ = l_List_any___at___00Lean_Options_erase_spec__2(v_x_2545_);
    lean_dec(v_x_2545_);
    v_r_2547_ = lean_box((v_res_2546_) as usize);
    return v_r_2547_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(
    mut v_k_2548_: *mut LeanObject,
    mut v_t_2549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2556_: u8 = 0;
    let mut v___x_2557_: u8 = 0;
    let mut v_impl_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: u8 = 0;
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2576_: u8 = 0;
    let mut v_size_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: u8 = 0;
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2588_: u8 = 0;
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2613_: u8 = 0;
    let mut v_unused_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2626_: u8 = 0;
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2630_: u8 = 0;
    let mut v_unused_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2637_: u8 = 0;
    let mut v_unused_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2655_: u8 = 0;
    let mut v_size_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2665_: u8 = 0;
    let mut v_unused_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2672_: u8 = 0;
    let mut v_k_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2677_: u8 = 0;
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2688_: u8 = 0;
    let mut v_unused_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2692_: u8 = 0;
    let mut v_unused_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2701_: u8 = 0;
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2709_: u8 = 0;
    let mut v_unused_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2718_: u8 = 0;
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2726_: u8 = 0;
    let mut v_unused_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: u8 = 0;
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2746_: u8 = 0;
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: u8 = 0;
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2762_: u8 = 0;
    let mut v_size_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: u8 = 0;
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2774_: u8 = 0;
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2799_: u8 = 0;
    let mut v_unused_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2814_: u8 = 0;
    let mut v_unused_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v_k_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2840_: u8 = 0;
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2851_: u8 = 0;
    let mut v_unused_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2873_: u8 = 0;
    let mut v_unused_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2879_: u8 = 0;
    let mut v_unused_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2887_: u8 = 0;
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: u8 = 0;
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2903_: u8 = 0;
    let mut v_size_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: u8 = 0;
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2915_: u8 = 0;
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2927_: u8 = 0;
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2931_: u8 = 0;
    let mut v_unused_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2950_: u8 = 0;
    let mut v_unused_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2966_: u8 = 0;
    let mut v_unused_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2974_: u8 = 0;
    let mut v_k_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2995_: u8 = 0;
    let mut v_unused_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3003_: u8 = 0;
    let mut v_k_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3010_: u8 = 0;
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3021_: u8 = 0;
    let mut v_unused_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3025_: u8 = 0;
    let mut v_unused_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v_unused_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: u8 = 0;
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3061_: u8 = 0;
    let mut v_size_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: u8 = 0;
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3073_: u8 = 0;
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3099_: u8 = 0;
    let mut v_unused_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3113_: u8 = 0;
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3117_: u8 = 0;
    let mut v_unused_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v_unused_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3142_: u8 = 0;
    let mut v_size_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3152_: u8 = 0;
    let mut v_unused_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3159_: u8 = 0;
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3167_: u8 = 0;
    let mut v_unused_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3176_: u8 = 0;
    let mut v_k_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3181_: u8 = 0;
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3192_: u8 = 0;
    let mut v_unused_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3196_: u8 = 0;
    let mut v_unused_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3207_: u8 = 0;
    let mut v_unused_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2549_) == 0 {
                    v_k_2550_ = lean_ctor_get(v_t_2549_, 1);
                    v_v_2551_ = lean_ctor_get(v_t_2549_, 2);
                    v_l_2552_ = lean_ctor_get(v_t_2549_, 3);
                    v_r_2553_ = lean_ctor_get(v_t_2549_, 4);
                    v_isSharedCheck_3207_ = (!lean_is_exclusive(v_t_2549_)) as u8;
                    if v_isSharedCheck_3207_ == 0 {
                        v_unused_3208_ = lean_ctor_get(v_t_2549_, 0);
                        lean_dec(v_unused_3208_);
                        v___x_2555_ = v_t_2549_;
                        v_isShared_2556_ = v_isSharedCheck_3207_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_2553_);
                        lean_inc(v_l_2552_);
                        lean_inc(v_v_2551_);
                        lean_inc(v_k_2550_);
                        lean_dec(v_t_2549_);
                        v___x_2555_ = lean_box(0);
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
                        v___x_2559_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_impl_2558_) == 0 {
                            if lean_obj_tag(v_r_2553_) == 0 {
                                v_size_2560_ = lean_ctor_get(v_impl_2558_, 0);
                                lean_inc(v_size_2560_);
                                v_size_2561_ = lean_ctor_get(v_r_2553_, 0);
                                v_k_2562_ = lean_ctor_get(v_r_2553_, 1);
                                v_v_2563_ = lean_ctor_get(v_r_2553_, 2);
                                v_l_2564_ = lean_ctor_get(v_r_2553_, 3);
                                lean_inc(v_l_2564_);
                                v_r_2565_ = lean_ctor_get(v_r_2553_, 4);
                                v___x_2566_ = lean_unsigned_to_nat(3);
                                v___x_2567_ = lean_nat_mul(v___x_2566_, v_size_2560_);
                                v___x_2568_ = lean_nat_dec_lt(v___x_2567_, v_size_2561_);
                                lean_dec(v___x_2567_);
                                if v___x_2568_ == 0 {
                                    lean_dec(v_l_2564_);
                                    v___x_2569_ = lean_nat_add(v___x_2559_, v_size_2560_);
                                    lean_dec(v_size_2560_);
                                    v___x_2570_ = lean_nat_add(v___x_2569_, v_size_2561_);
                                    lean_dec(v___x_2569_);
                                    if v_isShared_2556_ == 0 {
                                        lean_ctor_set(v___x_2555_, 3, v_impl_2558_);
                                        lean_ctor_set(v___x_2555_, 0, v___x_2570_);
                                        v___x_2572_ = v___x_2555_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
                                        lean_ctor_set(v_reuseFailAlloc_2573_, 1, v_k_2550_);
                                        lean_ctor_set(v_reuseFailAlloc_2573_, 2, v_v_2551_);
                                        lean_ctor_set(v_reuseFailAlloc_2573_, 3, v_impl_2558_);
                                        lean_ctor_set(v_reuseFailAlloc_2573_, 4, v_r_2553_);
                                        v___x_2572_ = v_reuseFailAlloc_2573_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_inc(v_r_2565_);
                                    lean_inc(v_v_2563_);
                                    lean_inc(v_k_2562_);
                                    lean_inc(v_size_2561_);
                                    v_isSharedCheck_2637_ = (!lean_is_exclusive(v_r_2553_)) as u8;
                                    if v_isSharedCheck_2637_ == 0 {
                                        v_unused_2638_ = lean_ctor_get(v_r_2553_, 4);
                                        lean_dec(v_unused_2638_);
                                        v_unused_2639_ = lean_ctor_get(v_r_2553_, 3);
                                        lean_dec(v_unused_2639_);
                                        v_unused_2640_ = lean_ctor_get(v_r_2553_, 2);
                                        lean_dec(v_unused_2640_);
                                        v_unused_2641_ = lean_ctor_get(v_r_2553_, 1);
                                        lean_dec(v_unused_2641_);
                                        v_unused_2642_ = lean_ctor_get(v_r_2553_, 0);
                                        lean_dec(v_unused_2642_);
                                        v___x_2575_ = v_r_2553_;
                                        v_isShared_2576_ = v_isSharedCheck_2637_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_dec(v_r_2553_);
                                        v___x_2575_ = lean_box(0);
                                        v_isShared_2576_ = v_isSharedCheck_2637_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_2643_ = lean_ctor_get(v_impl_2558_, 0);
                                lean_inc(v_size_2643_);
                                v___x_2644_ = lean_nat_add(v___x_2559_, v_size_2643_);
                                lean_dec(v_size_2643_);
                                if v_isShared_2556_ == 0 {
                                    lean_ctor_set(v___x_2555_, 3, v_impl_2558_);
                                    lean_ctor_set(v___x_2555_, 0, v___x_2644_);
                                    v___x_2646_ = v___x_2555_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2644_);
                                    lean_ctor_set(v_reuseFailAlloc_2647_, 1, v_k_2550_);
                                    lean_ctor_set(v_reuseFailAlloc_2647_, 2, v_v_2551_);
                                    lean_ctor_set(v_reuseFailAlloc_2647_, 3, v_impl_2558_);
                                    lean_ctor_set(v_reuseFailAlloc_2647_, 4, v_r_2553_);
                                    v___x_2646_ = v_reuseFailAlloc_2647_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if lean_obj_tag(v_r_2553_) == 0 {
                                v_l_2648_ = lean_ctor_get(v_r_2553_, 3);
                                lean_inc(v_l_2648_);
                                if lean_obj_tag(v_l_2648_) == 0 {
                                    v_r_2649_ = lean_ctor_get(v_r_2553_, 4);
                                    lean_inc(v_r_2649_);
                                    if lean_obj_tag(v_r_2649_) == 0 {
                                        v_size_2650_ = lean_ctor_get(v_r_2553_, 0);
                                        v_k_2651_ = lean_ctor_get(v_r_2553_, 1);
                                        v_v_2652_ = lean_ctor_get(v_r_2553_, 2);
                                        v_isSharedCheck_2665_ =
                                            (!lean_is_exclusive(v_r_2553_)) as u8;
                                        if v_isSharedCheck_2665_ == 0 {
                                            v_unused_2666_ = lean_ctor_get(v_r_2553_, 4);
                                            lean_dec(v_unused_2666_);
                                            v_unused_2667_ = lean_ctor_get(v_r_2553_, 3);
                                            lean_dec(v_unused_2667_);
                                            v___x_2654_ = v_r_2553_;
                                            v_isShared_2655_ = v_isSharedCheck_2665_;
                                            state = 14;
                                            continue;
                                        } else {
                                            lean_inc(v_v_2652_);
                                            lean_inc(v_k_2651_);
                                            lean_inc(v_size_2650_);
                                            lean_dec(v_r_2553_);
                                            v___x_2654_ = lean_box(0);
                                            v_isShared_2655_ = v_isSharedCheck_2665_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_2668_ = lean_ctor_get(v_r_2553_, 1);
                                        v_v_2669_ = lean_ctor_get(v_r_2553_, 2);
                                        v_isSharedCheck_2692_ =
                                            (!lean_is_exclusive(v_r_2553_)) as u8;
                                        if v_isSharedCheck_2692_ == 0 {
                                            v_unused_2693_ = lean_ctor_get(v_r_2553_, 4);
                                            lean_dec(v_unused_2693_);
                                            v_unused_2694_ = lean_ctor_get(v_r_2553_, 3);
                                            lean_dec(v_unused_2694_);
                                            v_unused_2695_ = lean_ctor_get(v_r_2553_, 0);
                                            lean_dec(v_unused_2695_);
                                            v___x_2671_ = v_r_2553_;
                                            v_isShared_2672_ = v_isSharedCheck_2692_;
                                            state = 17;
                                            continue;
                                        } else {
                                            lean_inc(v_v_2669_);
                                            lean_inc(v_k_2668_);
                                            lean_dec(v_r_2553_);
                                            v___x_2671_ = lean_box(0);
                                            v_isShared_2672_ = v_isSharedCheck_2692_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_2696_ = lean_ctor_get(v_r_2553_, 4);
                                    lean_inc(v_r_2696_);
                                    if lean_obj_tag(v_r_2696_) == 0 {
                                        v_k_2697_ = lean_ctor_get(v_r_2553_, 1);
                                        v_v_2698_ = lean_ctor_get(v_r_2553_, 2);
                                        v_isSharedCheck_2709_ =
                                            (!lean_is_exclusive(v_r_2553_)) as u8;
                                        if v_isSharedCheck_2709_ == 0 {
                                            v_unused_2710_ = lean_ctor_get(v_r_2553_, 4);
                                            lean_dec(v_unused_2710_);
                                            v_unused_2711_ = lean_ctor_get(v_r_2553_, 3);
                                            lean_dec(v_unused_2711_);
                                            v_unused_2712_ = lean_ctor_get(v_r_2553_, 0);
                                            lean_dec(v_unused_2712_);
                                            v___x_2700_ = v_r_2553_;
                                            v_isShared_2701_ = v_isSharedCheck_2709_;
                                            state = 22;
                                            continue;
                                        } else {
                                            lean_inc(v_v_2698_);
                                            lean_inc(v_k_2697_);
                                            lean_dec(v_r_2553_);
                                            v___x_2700_ = lean_box(0);
                                            v_isShared_2701_ = v_isSharedCheck_2709_;
                                            state = 22;
                                            continue;
                                        }
                                    } else {
                                        v_size_2713_ = lean_ctor_get(v_r_2553_, 0);
                                        v_k_2714_ = lean_ctor_get(v_r_2553_, 1);
                                        v_v_2715_ = lean_ctor_get(v_r_2553_, 2);
                                        v_isSharedCheck_2726_ =
                                            (!lean_is_exclusive(v_r_2553_)) as u8;
                                        if v_isSharedCheck_2726_ == 0 {
                                            v_unused_2727_ = lean_ctor_get(v_r_2553_, 4);
                                            lean_dec(v_unused_2727_);
                                            v_unused_2728_ = lean_ctor_get(v_r_2553_, 3);
                                            lean_dec(v_unused_2728_);
                                            v___x_2717_ = v_r_2553_;
                                            v_isShared_2718_ = v_isSharedCheck_2726_;
                                            state = 25;
                                            continue;
                                        } else {
                                            lean_inc(v_v_2715_);
                                            lean_inc(v_k_2714_);
                                            lean_inc(v_size_2713_);
                                            lean_dec(v_r_2553_);
                                            v___x_2717_ = lean_box(0);
                                            v_isShared_2718_ = v_isSharedCheck_2726_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_2556_ == 0 {
                                    lean_ctor_set(v___x_2555_, 3, v_r_2553_);
                                    lean_ctor_set(v___x_2555_, 0, v___x_2559_);
                                    v___x_2730_ = v___x_2555_;
                                    state = 28;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2559_);
                                    lean_ctor_set(v_reuseFailAlloc_2731_, 1, v_k_2550_);
                                    lean_ctor_set(v_reuseFailAlloc_2731_, 2, v_v_2551_);
                                    lean_ctor_set(v_reuseFailAlloc_2731_, 3, v_r_2553_);
                                    lean_ctor_set(v_reuseFailAlloc_2731_, 4, v_r_2553_);
                                    v___x_2730_ = v_reuseFailAlloc_2731_;
                                    state = 28;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        lean_del_object(v___x_2555_);
                        lean_dec(v_v_2551_);
                        lean_dec(v_k_2550_);
                        if lean_obj_tag(v_l_2552_) == 0 {
                            if lean_obj_tag(v_r_2553_) == 0 {
                                v_size_2732_ = lean_ctor_get(v_l_2552_, 0);
                                v_k_2733_ = lean_ctor_get(v_l_2552_, 1);
                                v_v_2734_ = lean_ctor_get(v_l_2552_, 2);
                                v_l_2735_ = lean_ctor_get(v_l_2552_, 3);
                                v_r_2736_ = lean_ctor_get(v_l_2552_, 4);
                                lean_inc(v_r_2736_);
                                v_size_2737_ = lean_ctor_get(v_r_2553_, 0);
                                v_k_2738_ = lean_ctor_get(v_r_2553_, 1);
                                v_v_2739_ = lean_ctor_get(v_r_2553_, 2);
                                v_l_2740_ = lean_ctor_get(v_r_2553_, 3);
                                lean_inc(v_l_2740_);
                                v_r_2741_ = lean_ctor_get(v_r_2553_, 4);
                                v___x_2742_ = lean_unsigned_to_nat(1);
                                v___x_2743_ = lean_nat_dec_lt(v_size_2732_, v_size_2737_);
                                if v___x_2743_ == 0 {
                                    lean_inc(v_l_2735_);
                                    lean_inc(v_v_2734_);
                                    lean_inc(v_k_2733_);
                                    v_isSharedCheck_2879_ = (!lean_is_exclusive(v_l_2552_)) as u8;
                                    if v_isSharedCheck_2879_ == 0 {
                                        v_unused_2880_ = lean_ctor_get(v_l_2552_, 4);
                                        lean_dec(v_unused_2880_);
                                        v_unused_2881_ = lean_ctor_get(v_l_2552_, 3);
                                        lean_dec(v_unused_2881_);
                                        v_unused_2882_ = lean_ctor_get(v_l_2552_, 2);
                                        lean_dec(v_unused_2882_);
                                        v_unused_2883_ = lean_ctor_get(v_l_2552_, 1);
                                        lean_dec(v_unused_2883_);
                                        v_unused_2884_ = lean_ctor_get(v_l_2552_, 0);
                                        lean_dec(v_unused_2884_);
                                        v___x_2745_ = v_l_2552_;
                                        v_isShared_2746_ = v_isSharedCheck_2879_;
                                        state = 29;
                                        continue;
                                    } else {
                                        lean_dec(v_l_2552_);
                                        v___x_2745_ = lean_box(0);
                                        v_isShared_2746_ = v_isSharedCheck_2879_;
                                        state = 29;
                                        continue;
                                    }
                                } else {
                                    lean_inc(v_r_2741_);
                                    lean_inc(v_v_2739_);
                                    lean_inc(v_k_2738_);
                                    v_isSharedCheck_3037_ = (!lean_is_exclusive(v_r_2553_)) as u8;
                                    if v_isSharedCheck_3037_ == 0 {
                                        v_unused_3038_ = lean_ctor_get(v_r_2553_, 4);
                                        lean_dec(v_unused_3038_);
                                        v_unused_3039_ = lean_ctor_get(v_r_2553_, 3);
                                        lean_dec(v_unused_3039_);
                                        v_unused_3040_ = lean_ctor_get(v_r_2553_, 2);
                                        lean_dec(v_unused_3040_);
                                        v_unused_3041_ = lean_ctor_get(v_r_2553_, 1);
                                        lean_dec(v_unused_3041_);
                                        v_unused_3042_ = lean_ctor_get(v_r_2553_, 0);
                                        lean_dec(v_unused_3042_);
                                        v___x_2886_ = v_r_2553_;
                                        v_isShared_2887_ = v_isSharedCheck_3037_;
                                        state = 51;
                                        continue;
                                    } else {
                                        lean_dec(v_r_2553_);
                                        v___x_2886_ = lean_box(0);
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
                        v___x_3044_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_impl_3043_) == 0 {
                            if lean_obj_tag(v_l_2552_) == 0 {
                                v_size_3045_ = lean_ctor_get(v_impl_3043_, 0);
                                lean_inc(v_size_3045_);
                                v_size_3046_ = lean_ctor_get(v_l_2552_, 0);
                                v_k_3047_ = lean_ctor_get(v_l_2552_, 1);
                                v_v_3048_ = lean_ctor_get(v_l_2552_, 2);
                                v_l_3049_ = lean_ctor_get(v_l_2552_, 3);
                                v_r_3050_ = lean_ctor_get(v_l_2552_, 4);
                                lean_inc(v_r_3050_);
                                v___x_3051_ = lean_unsigned_to_nat(3);
                                v___x_3052_ = lean_nat_mul(v___x_3051_, v_size_3045_);
                                v___x_3053_ = lean_nat_dec_lt(v___x_3052_, v_size_3046_);
                                lean_dec(v___x_3052_);
                                if v___x_3053_ == 0 {
                                    lean_dec(v_r_3050_);
                                    v___x_3054_ = lean_nat_add(v___x_3044_, v_size_3046_);
                                    v___x_3055_ = lean_nat_add(v___x_3054_, v_size_3045_);
                                    lean_dec(v_size_3045_);
                                    lean_dec(v___x_3054_);
                                    if v_isShared_2556_ == 0 {
                                        lean_ctor_set(v___x_2555_, 4, v_impl_3043_);
                                        lean_ctor_set(v___x_2555_, 0, v___x_3055_);
                                        v___x_3057_ = v___x_2555_;
                                        state = 74;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___x_3055_);
                                        lean_ctor_set(v_reuseFailAlloc_3058_, 1, v_k_2550_);
                                        lean_ctor_set(v_reuseFailAlloc_3058_, 2, v_v_2551_);
                                        lean_ctor_set(v_reuseFailAlloc_3058_, 3, v_l_2552_);
                                        lean_ctor_set(v_reuseFailAlloc_3058_, 4, v_impl_3043_);
                                        v___x_3057_ = v_reuseFailAlloc_3058_;
                                        state = 74;
                                        continue;
                                    }
                                } else {
                                    lean_inc(v_l_3049_);
                                    lean_inc(v_v_3048_);
                                    lean_inc(v_k_3047_);
                                    lean_inc(v_size_3046_);
                                    v_isSharedCheck_3124_ = (!lean_is_exclusive(v_l_2552_)) as u8;
                                    if v_isSharedCheck_3124_ == 0 {
                                        v_unused_3125_ = lean_ctor_get(v_l_2552_, 4);
                                        lean_dec(v_unused_3125_);
                                        v_unused_3126_ = lean_ctor_get(v_l_2552_, 3);
                                        lean_dec(v_unused_3126_);
                                        v_unused_3127_ = lean_ctor_get(v_l_2552_, 2);
                                        lean_dec(v_unused_3127_);
                                        v_unused_3128_ = lean_ctor_get(v_l_2552_, 1);
                                        lean_dec(v_unused_3128_);
                                        v_unused_3129_ = lean_ctor_get(v_l_2552_, 0);
                                        lean_dec(v_unused_3129_);
                                        v___x_3060_ = v_l_2552_;
                                        v_isShared_3061_ = v_isSharedCheck_3124_;
                                        state = 75;
                                        continue;
                                    } else {
                                        lean_dec(v_l_2552_);
                                        v___x_3060_ = lean_box(0);
                                        v_isShared_3061_ = v_isSharedCheck_3124_;
                                        state = 75;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_3130_ = lean_ctor_get(v_impl_3043_, 0);
                                lean_inc(v_size_3130_);
                                v___x_3131_ = lean_nat_add(v___x_3044_, v_size_3130_);
                                lean_dec(v_size_3130_);
                                if v_isShared_2556_ == 0 {
                                    lean_ctor_set(v___x_2555_, 4, v_impl_3043_);
                                    lean_ctor_set(v___x_2555_, 0, v___x_3131_);
                                    v___x_3133_ = v___x_2555_;
                                    state = 85;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3131_);
                                    lean_ctor_set(v_reuseFailAlloc_3134_, 1, v_k_2550_);
                                    lean_ctor_set(v_reuseFailAlloc_3134_, 2, v_v_2551_);
                                    lean_ctor_set(v_reuseFailAlloc_3134_, 3, v_l_2552_);
                                    lean_ctor_set(v_reuseFailAlloc_3134_, 4, v_impl_3043_);
                                    v___x_3133_ = v_reuseFailAlloc_3134_;
                                    state = 85;
                                    continue;
                                }
                            }
                        } else {
                            if lean_obj_tag(v_l_2552_) == 0 {
                                v_l_3135_ = lean_ctor_get(v_l_2552_, 3);
                                if lean_obj_tag(v_l_3135_) == 0 {
                                    lean_inc_ref(v_l_3135_);
                                    v_r_3136_ = lean_ctor_get(v_l_2552_, 4);
                                    lean_inc(v_r_3136_);
                                    if lean_obj_tag(v_r_3136_) == 0 {
                                        v_size_3137_ = lean_ctor_get(v_l_2552_, 0);
                                        v_k_3138_ = lean_ctor_get(v_l_2552_, 1);
                                        v_v_3139_ = lean_ctor_get(v_l_2552_, 2);
                                        v_isSharedCheck_3152_ =
                                            (!lean_is_exclusive(v_l_2552_)) as u8;
                                        if v_isSharedCheck_3152_ == 0 {
                                            v_unused_3153_ = lean_ctor_get(v_l_2552_, 4);
                                            lean_dec(v_unused_3153_);
                                            v_unused_3154_ = lean_ctor_get(v_l_2552_, 3);
                                            lean_dec(v_unused_3154_);
                                            v___x_3141_ = v_l_2552_;
                                            v_isShared_3142_ = v_isSharedCheck_3152_;
                                            state = 86;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3139_);
                                            lean_inc(v_k_3138_);
                                            lean_inc(v_size_3137_);
                                            lean_dec(v_l_2552_);
                                            v___x_3141_ = lean_box(0);
                                            v_isShared_3142_ = v_isSharedCheck_3152_;
                                            state = 86;
                                            continue;
                                        }
                                    } else {
                                        v_k_3155_ = lean_ctor_get(v_l_2552_, 1);
                                        v_v_3156_ = lean_ctor_get(v_l_2552_, 2);
                                        v_isSharedCheck_3167_ =
                                            (!lean_is_exclusive(v_l_2552_)) as u8;
                                        if v_isSharedCheck_3167_ == 0 {
                                            v_unused_3168_ = lean_ctor_get(v_l_2552_, 4);
                                            lean_dec(v_unused_3168_);
                                            v_unused_3169_ = lean_ctor_get(v_l_2552_, 3);
                                            lean_dec(v_unused_3169_);
                                            v_unused_3170_ = lean_ctor_get(v_l_2552_, 0);
                                            lean_dec(v_unused_3170_);
                                            v___x_3158_ = v_l_2552_;
                                            v_isShared_3159_ = v_isSharedCheck_3167_;
                                            state = 89;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3156_);
                                            lean_inc(v_k_3155_);
                                            lean_dec(v_l_2552_);
                                            v___x_3158_ = lean_box(0);
                                            v_isShared_3159_ = v_isSharedCheck_3167_;
                                            state = 89;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_3171_ = lean_ctor_get(v_l_2552_, 4);
                                    lean_inc(v_r_3171_);
                                    if lean_obj_tag(v_r_3171_) == 0 {
                                        lean_inc(v_l_3135_);
                                        v_k_3172_ = lean_ctor_get(v_l_2552_, 1);
                                        v_v_3173_ = lean_ctor_get(v_l_2552_, 2);
                                        v_isSharedCheck_3196_ =
                                            (!lean_is_exclusive(v_l_2552_)) as u8;
                                        if v_isSharedCheck_3196_ == 0 {
                                            v_unused_3197_ = lean_ctor_get(v_l_2552_, 4);
                                            lean_dec(v_unused_3197_);
                                            v_unused_3198_ = lean_ctor_get(v_l_2552_, 3);
                                            lean_dec(v_unused_3198_);
                                            v_unused_3199_ = lean_ctor_get(v_l_2552_, 0);
                                            lean_dec(v_unused_3199_);
                                            v___x_3175_ = v_l_2552_;
                                            v_isShared_3176_ = v_isSharedCheck_3196_;
                                            state = 92;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3173_);
                                            lean_inc(v_k_3172_);
                                            lean_dec(v_l_2552_);
                                            v___x_3175_ = lean_box(0);
                                            v_isShared_3176_ = v_isSharedCheck_3196_;
                                            state = 92;
                                            continue;
                                        }
                                    } else {
                                        v___x_3200_ = lean_unsigned_to_nat(2);
                                        if v_isShared_2556_ == 0 {
                                            lean_ctor_set(v___x_2555_, 4, v_r_3171_);
                                            lean_ctor_set(v___x_2555_, 0, v___x_3200_);
                                            v___x_3202_ = v___x_2555_;
                                            state = 97;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3203_ =
                                                lean_alloc_ctor(0, 5, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3200_);
                                            lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_k_2550_);
                                            lean_ctor_set(v_reuseFailAlloc_3203_, 2, v_v_2551_);
                                            lean_ctor_set(v_reuseFailAlloc_3203_, 3, v_l_2552_);
                                            lean_ctor_set(v_reuseFailAlloc_3203_, 4, v_r_3171_);
                                            v___x_3202_ = v_reuseFailAlloc_3203_;
                                            state = 97;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_2556_ == 0 {
                                    lean_ctor_set(v___x_2555_, 4, v_l_2552_);
                                    lean_ctor_set(v___x_2555_, 0, v___x_3044_);
                                    v___x_3205_ = v___x_2555_;
                                    state = 98;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3044_);
                                    lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_k_2550_);
                                    lean_ctor_set(v_reuseFailAlloc_3206_, 2, v_v_2551_);
                                    lean_ctor_set(v_reuseFailAlloc_3206_, 3, v_l_2552_);
                                    lean_ctor_set(v_reuseFailAlloc_3206_, 4, v_l_2552_);
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
                v_size_2577_ = lean_ctor_get(v_l_2564_, 0);
                v_k_2578_ = lean_ctor_get(v_l_2564_, 1);
                v_v_2579_ = lean_ctor_get(v_l_2564_, 2);
                v_l_2580_ = lean_ctor_get(v_l_2564_, 3);
                v_r_2581_ = lean_ctor_get(v_l_2564_, 4);
                v_size_2582_ = lean_ctor_get(v_r_2565_, 0);
                v___x_2583_ = lean_unsigned_to_nat(2);
                v___x_2584_ = lean_nat_mul(v___x_2583_, v_size_2582_);
                v___x_2585_ = lean_nat_dec_lt(v_size_2577_, v___x_2584_);
                lean_dec(v___x_2584_);
                if v___x_2585_ == 0 {
                    lean_inc(v_r_2581_);
                    lean_inc(v_l_2580_);
                    lean_inc(v_v_2579_);
                    lean_inc(v_k_2578_);
                    v_isSharedCheck_2613_ = (!lean_is_exclusive(v_l_2564_)) as u8;
                    if v_isSharedCheck_2613_ == 0 {
                        v_unused_2614_ = lean_ctor_get(v_l_2564_, 4);
                        lean_dec(v_unused_2614_);
                        v_unused_2615_ = lean_ctor_get(v_l_2564_, 3);
                        lean_dec(v_unused_2615_);
                        v_unused_2616_ = lean_ctor_get(v_l_2564_, 2);
                        lean_dec(v_unused_2616_);
                        v_unused_2617_ = lean_ctor_get(v_l_2564_, 1);
                        lean_dec(v_unused_2617_);
                        v_unused_2618_ = lean_ctor_get(v_l_2564_, 0);
                        lean_dec(v_unused_2618_);
                        v___x_2587_ = v_l_2564_;
                        v_isShared_2588_ = v_isSharedCheck_2613_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_l_2564_);
                        v___x_2587_ = lean_box(0);
                        v_isShared_2588_ = v_isSharedCheck_2613_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2555_);
                    v___x_2619_ = lean_nat_add(v___x_2559_, v_size_2560_);
                    lean_dec(v_size_2560_);
                    v___x_2620_ = lean_nat_add(v___x_2619_, v_size_2561_);
                    lean_dec(v_size_2561_);
                    v___x_2621_ = lean_nat_add(v___x_2619_, v_size_2577_);
                    lean_dec(v___x_2619_);
                    lean_inc_ref(v_impl_2558_);
                    if v_isShared_2576_ == 0 {
                        lean_ctor_set(v___x_2575_, 4, v_l_2564_);
                        lean_ctor_set(v___x_2575_, 3, v_impl_2558_);
                        lean_ctor_set(v___x_2575_, 2, v_v_2551_);
                        lean_ctor_set(v___x_2575_, 1, v_k_2550_);
                        lean_ctor_set(v___x_2575_, 0, v___x_2621_);
                        v___x_2623_ = v___x_2575_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2621_);
                        lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_k_2550_);
                        lean_ctor_set(v_reuseFailAlloc_2636_, 2, v_v_2551_);
                        lean_ctor_set(v_reuseFailAlloc_2636_, 3, v_impl_2558_);
                        lean_ctor_set(v_reuseFailAlloc_2636_, 4, v_l_2564_);
                        v___x_2623_ = v_reuseFailAlloc_2636_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2589_ = lean_nat_add(v___x_2559_, v_size_2560_);
                lean_dec(v_size_2560_);
                v___x_2590_ = lean_nat_add(v___x_2589_, v_size_2561_);
                lean_dec(v_size_2561_);
                if lean_obj_tag(v_l_2580_) == 0 {
                    v_size_2611_ = lean_ctor_get(v_l_2580_, 0);
                    lean_inc(v_size_2611_);
                    v___y_2603_ = v_size_2611_;
                    state = 8;
                    continue;
                } else {
                    v___x_2612_ = lean_unsigned_to_nat(0);
                    v___y_2603_ = v___x_2612_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2595_ = lean_nat_add(v___y_2592_, v___y_2594_);
                lean_dec(v___y_2594_);
                lean_dec(v___y_2592_);
                if v_isShared_2588_ == 0 {
                    lean_ctor_set(v___x_2587_, 4, v_r_2565_);
                    lean_ctor_set(v___x_2587_, 3, v_r_2581_);
                    lean_ctor_set(v___x_2587_, 2, v_v_2563_);
                    lean_ctor_set(v___x_2587_, 1, v_k_2562_);
                    lean_ctor_set(v___x_2587_, 0, v___x_2595_);
                    v___x_2597_ = v___x_2587_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2595_);
                    lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_k_2562_);
                    lean_ctor_set(v_reuseFailAlloc_2601_, 2, v_v_2563_);
                    lean_ctor_set(v_reuseFailAlloc_2601_, 3, v_r_2581_);
                    lean_ctor_set(v_reuseFailAlloc_2601_, 4, v_r_2565_);
                    v___x_2597_ = v_reuseFailAlloc_2601_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2576_ == 0 {
                    lean_ctor_set(v___x_2575_, 4, v___x_2597_);
                    lean_ctor_set(v___x_2575_, 3, v___y_2593_);
                    lean_ctor_set(v___x_2575_, 2, v_v_2579_);
                    lean_ctor_set(v___x_2575_, 1, v_k_2578_);
                    lean_ctor_set(v___x_2575_, 0, v___x_2590_);
                    v___x_2599_ = v___x_2575_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2590_);
                    lean_ctor_set(v_reuseFailAlloc_2600_, 1, v_k_2578_);
                    lean_ctor_set(v_reuseFailAlloc_2600_, 2, v_v_2579_);
                    lean_ctor_set(v_reuseFailAlloc_2600_, 3, v___y_2593_);
                    lean_ctor_set(v_reuseFailAlloc_2600_, 4, v___x_2597_);
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
                lean_dec(v___y_2603_);
                lean_dec(v___x_2589_);
                if v_isShared_2556_ == 0 {
                    lean_ctor_set(v___x_2555_, 4, v_l_2580_);
                    lean_ctor_set(v___x_2555_, 3, v_impl_2558_);
                    lean_ctor_set(v___x_2555_, 0, v___x_2604_);
                    v___x_2606_ = v___x_2555_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2604_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_k_2550_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 2, v_v_2551_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 3, v_impl_2558_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 4, v_l_2580_);
                    v___x_2606_ = v_reuseFailAlloc_2610_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2607_ = lean_nat_add(v___x_2559_, v_size_2582_);
                if lean_obj_tag(v_r_2581_) == 0 {
                    v_size_2608_ = lean_ctor_get(v_r_2581_, 0);
                    lean_inc(v_size_2608_);
                    v___y_2592_ = v___x_2607_;
                    v___y_2593_ = v___x_2606_;
                    v___y_2594_ = v_size_2608_;
                    state = 5;
                    continue;
                } else {
                    v___x_2609_ = lean_unsigned_to_nat(0);
                    v___y_2592_ = v___x_2607_;
                    v___y_2593_ = v___x_2606_;
                    v___y_2594_ = v___x_2609_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2630_ = (!lean_is_exclusive(v_impl_2558_)) as u8;
                if v_isSharedCheck_2630_ == 0 {
                    v_unused_2631_ = lean_ctor_get(v_impl_2558_, 4);
                    lean_dec(v_unused_2631_);
                    v_unused_2632_ = lean_ctor_get(v_impl_2558_, 3);
                    lean_dec(v_unused_2632_);
                    v_unused_2633_ = lean_ctor_get(v_impl_2558_, 2);
                    lean_dec(v_unused_2633_);
                    v_unused_2634_ = lean_ctor_get(v_impl_2558_, 1);
                    lean_dec(v_unused_2634_);
                    v_unused_2635_ = lean_ctor_get(v_impl_2558_, 0);
                    lean_dec(v_unused_2635_);
                    v___x_2625_ = v_impl_2558_;
                    v_isShared_2626_ = v_isSharedCheck_2630_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_impl_2558_);
                    v___x_2625_ = lean_box(0);
                    v_isShared_2626_ = v_isSharedCheck_2630_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2626_ == 0 {
                    lean_ctor_set(v___x_2625_, 4, v_r_2565_);
                    lean_ctor_set(v___x_2625_, 3, v___x_2623_);
                    lean_ctor_set(v___x_2625_, 2, v_v_2563_);
                    lean_ctor_set(v___x_2625_, 1, v_k_2562_);
                    lean_ctor_set(v___x_2625_, 0, v___x_2620_);
                    v___x_2628_ = v___x_2625_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2620_);
                    lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_k_2562_);
                    lean_ctor_set(v_reuseFailAlloc_2629_, 2, v_v_2563_);
                    lean_ctor_set(v_reuseFailAlloc_2629_, 3, v___x_2623_);
                    lean_ctor_set(v_reuseFailAlloc_2629_, 4, v_r_2565_);
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
                v_size_2656_ = lean_ctor_get(v_l_2648_, 0);
                v___x_2657_ = lean_nat_add(v___x_2559_, v_size_2650_);
                lean_dec(v_size_2650_);
                v___x_2658_ = lean_nat_add(v___x_2559_, v_size_2656_);
                if v_isShared_2655_ == 0 {
                    lean_ctor_set(v___x_2654_, 4, v_l_2648_);
                    lean_ctor_set(v___x_2654_, 3, v_impl_2558_);
                    lean_ctor_set(v___x_2654_, 2, v_v_2551_);
                    lean_ctor_set(v___x_2654_, 1, v_k_2550_);
                    lean_ctor_set(v___x_2654_, 0, v___x_2658_);
                    v___x_2660_ = v___x_2654_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2658_);
                    lean_ctor_set(v_reuseFailAlloc_2664_, 1, v_k_2550_);
                    lean_ctor_set(v_reuseFailAlloc_2664_, 2, v_v_2551_);
                    lean_ctor_set(v_reuseFailAlloc_2664_, 3, v_impl_2558_);
                    lean_ctor_set(v_reuseFailAlloc_2664_, 4, v_l_2648_);
                    v___x_2660_ = v_reuseFailAlloc_2664_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_2556_ == 0 {
                    lean_ctor_set(v___x_2555_, 4, v_r_2649_);
                    lean_ctor_set(v___x_2555_, 3, v___x_2660_);
                    lean_ctor_set(v___x_2555_, 2, v_v_2652_);
                    lean_ctor_set(v___x_2555_, 1, v_k_2651_);
                    lean_ctor_set(v___x_2555_, 0, v___x_2657_);
                    v___x_2662_ = v___x_2555_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2657_);
                    lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_k_2651_);
                    lean_ctor_set(v_reuseFailAlloc_2663_, 2, v_v_2652_);
                    lean_ctor_set(v_reuseFailAlloc_2663_, 3, v___x_2660_);
                    lean_ctor_set(v_reuseFailAlloc_2663_, 4, v_r_2649_);
                    v___x_2662_ = v_reuseFailAlloc_2663_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2662_;
            }
            17 => {
                v_k_2673_ = lean_ctor_get(v_l_2648_, 1);
                v_v_2674_ = lean_ctor_get(v_l_2648_, 2);
                v_isSharedCheck_2688_ = (!lean_is_exclusive(v_l_2648_)) as u8;
                if v_isSharedCheck_2688_ == 0 {
                    v_unused_2689_ = lean_ctor_get(v_l_2648_, 4);
                    lean_dec(v_unused_2689_);
                    v_unused_2690_ = lean_ctor_get(v_l_2648_, 3);
                    lean_dec(v_unused_2690_);
                    v_unused_2691_ = lean_ctor_get(v_l_2648_, 0);
                    lean_dec(v_unused_2691_);
                    v___x_2676_ = v_l_2648_;
                    v_isShared_2677_ = v_isSharedCheck_2688_;
                    state = 18;
                    continue;
                } else {
                    lean_inc(v_v_2674_);
                    lean_inc(v_k_2673_);
                    lean_dec(v_l_2648_);
                    v___x_2676_ = lean_box(0);
                    v_isShared_2677_ = v_isSharedCheck_2688_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_2678_ = lean_unsigned_to_nat(3);
                if v_isShared_2677_ == 0 {
                    lean_ctor_set(v___x_2676_, 4, v_r_2649_);
                    lean_ctor_set(v___x_2676_, 3, v_r_2649_);
                    lean_ctor_set(v___x_2676_, 2, v_v_2551_);
                    lean_ctor_set(v___x_2676_, 1, v_k_2550_);
                    lean_ctor_set(v___x_2676_, 0, v___x_2559_);
                    v___x_2680_ = v___x_2676_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2559_);
                    lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_k_2550_);
                    lean_ctor_set(v_reuseFailAlloc_2687_, 2, v_v_2551_);
                    lean_ctor_set(v_reuseFailAlloc_2687_, 3, v_r_2649_);
                    lean_ctor_set(v_reuseFailAlloc_2687_, 4, v_r_2649_);
                    v___x_2680_ = v_reuseFailAlloc_2687_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2672_ == 0 {
                    lean_ctor_set(v___x_2671_, 3, v_r_2649_);
                    lean_ctor_set(v___x_2671_, 0, v___x_2559_);
                    v___x_2682_ = v___x_2671_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2559_);
                    lean_ctor_set(v_reuseFailAlloc_2686_, 1, v_k_2668_);
                    lean_ctor_set(v_reuseFailAlloc_2686_, 2, v_v_2669_);
                    lean_ctor_set(v_reuseFailAlloc_2686_, 3, v_r_2649_);
                    lean_ctor_set(v_reuseFailAlloc_2686_, 4, v_r_2649_);
                    v___x_2682_ = v_reuseFailAlloc_2686_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_2556_ == 0 {
                    lean_ctor_set(v___x_2555_, 4, v___x_2682_);
                    lean_ctor_set(v___x_2555_, 3, v___x_2680_);
                    lean_ctor_set(v___x_2555_, 2, v_v_2674_);
                    lean_ctor_set(v___x_2555_, 1, v_k_2673_);
                    lean_ctor_set(v___x_2555_, 0, v___x_2678_);
                    v___x_2684_ = v___x_2555_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2678_);
                    lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_k_2673_);
                    lean_ctor_set(v_reuseFailAlloc_2685_, 2, v_v_2674_);
                    lean_ctor_set(v_reuseFailAlloc_2685_, 3, v___x_2680_);
                    lean_ctor_set(v_reuseFailAlloc_2685_, 4, v___x_2682_);
                    v___x_2684_ = v_reuseFailAlloc_2685_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2684_;
            }
            22 => {
                v___x_2702_ = lean_unsigned_to_nat(3);
                if v_isShared_2701_ == 0 {
                    lean_ctor_set(v___x_2700_, 4, v_l_2648_);
                    lean_ctor_set(v___x_2700_, 2, v_v_2551_);
                    lean_ctor_set(v___x_2700_, 1, v_k_2550_);
                    lean_ctor_set(v___x_2700_, 0, v___x_2559_);
                    v___x_2704_ = v___x_2700_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2559_);
                    lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_k_2550_);
                    lean_ctor_set(v_reuseFailAlloc_2708_, 2, v_v_2551_);
                    lean_ctor_set(v_reuseFailAlloc_2708_, 3, v_l_2648_);
                    lean_ctor_set(v_reuseFailAlloc_2708_, 4, v_l_2648_);
                    v___x_2704_ = v_reuseFailAlloc_2708_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_2556_ == 0 {
                    lean_ctor_set(v___x_2555_, 4, v_r_2696_);
                    lean_ctor_set(v___x_2555_, 3, v___x_2704_);
                    lean_ctor_set(v___x_2555_, 2, v_v_2698_);
                    lean_ctor_set(v___x_2555_, 1, v_k_2697_);
                    lean_ctor_set(v___x_2555_, 0, v___x_2702_);
                    v___x_2706_ = v___x_2555_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2702_);
                    lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_k_2697_);
                    lean_ctor_set(v_reuseFailAlloc_2707_, 2, v_v_2698_);
                    lean_ctor_set(v_reuseFailAlloc_2707_, 3, v___x_2704_);
                    lean_ctor_set(v_reuseFailAlloc_2707_, 4, v_r_2696_);
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
                    lean_ctor_set(v___x_2717_, 3, v_r_2696_);
                    v___x_2720_ = v___x_2717_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_size_2713_);
                    lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_k_2714_);
                    lean_ctor_set(v_reuseFailAlloc_2725_, 2, v_v_2715_);
                    lean_ctor_set(v_reuseFailAlloc_2725_, 3, v_r_2696_);
                    lean_ctor_set(v_reuseFailAlloc_2725_, 4, v_r_2696_);
                    v___x_2720_ = v_reuseFailAlloc_2725_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_2721_ = lean_unsigned_to_nat(2);
                if v_isShared_2556_ == 0 {
                    lean_ctor_set(v___x_2555_, 4, v___x_2720_);
                    lean_ctor_set(v___x_2555_, 3, v_r_2696_);
                    lean_ctor_set(v___x_2555_, 0, v___x_2721_);
                    v___x_2723_ = v___x_2555_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2721_);
                    lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_k_2550_);
                    lean_ctor_set(v_reuseFailAlloc_2724_, 2, v_v_2551_);
                    lean_ctor_set(v_reuseFailAlloc_2724_, 3, v_r_2696_);
                    lean_ctor_set(v_reuseFailAlloc_2724_, 4, v___x_2720_);
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
                v_tree_2748_ = lean_ctor_get(v___x_2747_, 2);
                lean_inc(v_tree_2748_);
                if lean_obj_tag(v_tree_2748_) == 0 {
                    v_k_2749_ = lean_ctor_get(v___x_2747_, 0);
                    lean_inc(v_k_2749_);
                    v_v_2750_ = lean_ctor_get(v___x_2747_, 1);
                    lean_inc(v_v_2750_);
                    lean_dec_ref(v___x_2747_);
                    v_size_2751_ = lean_ctor_get(v_tree_2748_, 0);
                    v___x_2752_ = lean_unsigned_to_nat(3);
                    v___x_2753_ = lean_nat_mul(v___x_2752_, v_size_2751_);
                    v___x_2754_ = lean_nat_dec_lt(v___x_2753_, v_size_2737_);
                    lean_dec(v___x_2753_);
                    if v___x_2754_ == 0 {
                        lean_dec(v_l_2740_);
                        v___x_2755_ = lean_nat_add(v___x_2742_, v_size_2751_);
                        v___x_2756_ = lean_nat_add(v___x_2755_, v_size_2737_);
                        lean_dec(v___x_2755_);
                        if v_isShared_2746_ == 0 {
                            lean_ctor_set(v___x_2745_, 4, v_r_2553_);
                            lean_ctor_set(v___x_2745_, 3, v_tree_2748_);
                            lean_ctor_set(v___x_2745_, 2, v_v_2750_);
                            lean_ctor_set(v___x_2745_, 1, v_k_2749_);
                            lean_ctor_set(v___x_2745_, 0, v___x_2756_);
                            v___x_2758_ = v___x_2745_;
                            state = 30;
                            continue;
                        } else {
                            v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2756_);
                            lean_ctor_set(v_reuseFailAlloc_2759_, 1, v_k_2749_);
                            lean_ctor_set(v_reuseFailAlloc_2759_, 2, v_v_2750_);
                            lean_ctor_set(v_reuseFailAlloc_2759_, 3, v_tree_2748_);
                            lean_ctor_set(v_reuseFailAlloc_2759_, 4, v_r_2553_);
                            v___x_2758_ = v_reuseFailAlloc_2759_;
                            state = 30;
                            continue;
                        }
                    } else {
                        lean_inc(v_r_2741_);
                        lean_inc(v_v_2739_);
                        lean_inc(v_k_2738_);
                        lean_inc(v_size_2737_);
                        v_isSharedCheck_2814_ = (!lean_is_exclusive(v_r_2553_)) as u8;
                        if v_isSharedCheck_2814_ == 0 {
                            v_unused_2815_ = lean_ctor_get(v_r_2553_, 4);
                            lean_dec(v_unused_2815_);
                            v_unused_2816_ = lean_ctor_get(v_r_2553_, 3);
                            lean_dec(v_unused_2816_);
                            v_unused_2817_ = lean_ctor_get(v_r_2553_, 2);
                            lean_dec(v_unused_2817_);
                            v_unused_2818_ = lean_ctor_get(v_r_2553_, 1);
                            lean_dec(v_unused_2818_);
                            v_unused_2819_ = lean_ctor_get(v_r_2553_, 0);
                            lean_dec(v_unused_2819_);
                            v___x_2761_ = v_r_2553_;
                            v_isShared_2762_ = v_isSharedCheck_2814_;
                            state = 31;
                            continue;
                        } else {
                            lean_dec(v_r_2553_);
                            v___x_2761_ = lean_box(0);
                            v_isShared_2762_ = v_isSharedCheck_2814_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_r_2741_);
                    lean_inc(v_v_2739_);
                    lean_inc(v_k_2738_);
                    lean_inc(v_size_2737_);
                    v_isSharedCheck_2873_ = (!lean_is_exclusive(v_r_2553_)) as u8;
                    if v_isSharedCheck_2873_ == 0 {
                        v_unused_2874_ = lean_ctor_get(v_r_2553_, 4);
                        lean_dec(v_unused_2874_);
                        v_unused_2875_ = lean_ctor_get(v_r_2553_, 3);
                        lean_dec(v_unused_2875_);
                        v_unused_2876_ = lean_ctor_get(v_r_2553_, 2);
                        lean_dec(v_unused_2876_);
                        v_unused_2877_ = lean_ctor_get(v_r_2553_, 1);
                        lean_dec(v_unused_2877_);
                        v_unused_2878_ = lean_ctor_get(v_r_2553_, 0);
                        lean_dec(v_unused_2878_);
                        v___x_2821_ = v_r_2553_;
                        v_isShared_2822_ = v_isSharedCheck_2873_;
                        state = 40;
                        continue;
                    } else {
                        lean_dec(v_r_2553_);
                        v___x_2821_ = lean_box(0);
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
                v_size_2763_ = lean_ctor_get(v_l_2740_, 0);
                v_k_2764_ = lean_ctor_get(v_l_2740_, 1);
                v_v_2765_ = lean_ctor_get(v_l_2740_, 2);
                v_l_2766_ = lean_ctor_get(v_l_2740_, 3);
                v_r_2767_ = lean_ctor_get(v_l_2740_, 4);
                v_size_2768_ = lean_ctor_get(v_r_2741_, 0);
                v___x_2769_ = lean_unsigned_to_nat(2);
                v___x_2770_ = lean_nat_mul(v___x_2769_, v_size_2768_);
                v___x_2771_ = lean_nat_dec_lt(v_size_2763_, v___x_2770_);
                lean_dec(v___x_2770_);
                if v___x_2771_ == 0 {
                    lean_inc(v_r_2767_);
                    lean_inc(v_l_2766_);
                    lean_inc(v_v_2765_);
                    lean_inc(v_k_2764_);
                    v_isSharedCheck_2799_ = (!lean_is_exclusive(v_l_2740_)) as u8;
                    if v_isSharedCheck_2799_ == 0 {
                        v_unused_2800_ = lean_ctor_get(v_l_2740_, 4);
                        lean_dec(v_unused_2800_);
                        v_unused_2801_ = lean_ctor_get(v_l_2740_, 3);
                        lean_dec(v_unused_2801_);
                        v_unused_2802_ = lean_ctor_get(v_l_2740_, 2);
                        lean_dec(v_unused_2802_);
                        v_unused_2803_ = lean_ctor_get(v_l_2740_, 1);
                        lean_dec(v_unused_2803_);
                        v_unused_2804_ = lean_ctor_get(v_l_2740_, 0);
                        lean_dec(v_unused_2804_);
                        v___x_2773_ = v_l_2740_;
                        v_isShared_2774_ = v_isSharedCheck_2799_;
                        state = 32;
                        continue;
                    } else {
                        lean_dec(v_l_2740_);
                        v___x_2773_ = lean_box(0);
                        v_isShared_2774_ = v_isSharedCheck_2799_;
                        state = 32;
                        continue;
                    }
                } else {
                    v___x_2805_ = lean_nat_add(v___x_2742_, v_size_2751_);
                    v___x_2806_ = lean_nat_add(v___x_2805_, v_size_2737_);
                    lean_dec(v_size_2737_);
                    v___x_2807_ = lean_nat_add(v___x_2805_, v_size_2763_);
                    lean_dec(v___x_2805_);
                    if v_isShared_2762_ == 0 {
                        lean_ctor_set(v___x_2761_, 4, v_l_2740_);
                        lean_ctor_set(v___x_2761_, 3, v_tree_2748_);
                        lean_ctor_set(v___x_2761_, 2, v_v_2750_);
                        lean_ctor_set(v___x_2761_, 1, v_k_2749_);
                        lean_ctor_set(v___x_2761_, 0, v___x_2807_);
                        v___x_2809_ = v___x_2761_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2807_);
                        lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_k_2749_);
                        lean_ctor_set(v_reuseFailAlloc_2813_, 2, v_v_2750_);
                        lean_ctor_set(v_reuseFailAlloc_2813_, 3, v_tree_2748_);
                        lean_ctor_set(v_reuseFailAlloc_2813_, 4, v_l_2740_);
                        v___x_2809_ = v_reuseFailAlloc_2813_;
                        state = 38;
                        continue;
                    }
                }
            }
            32 => {
                v___x_2775_ = lean_nat_add(v___x_2742_, v_size_2751_);
                v___x_2776_ = lean_nat_add(v___x_2775_, v_size_2737_);
                lean_dec(v_size_2737_);
                if lean_obj_tag(v_l_2766_) == 0 {
                    v_size_2797_ = lean_ctor_get(v_l_2766_, 0);
                    lean_inc(v_size_2797_);
                    v___y_2789_ = v_size_2797_;
                    state = 36;
                    continue;
                } else {
                    v___x_2798_ = lean_unsigned_to_nat(0);
                    v___y_2789_ = v___x_2798_;
                    state = 36;
                    continue;
                }
            }
            33 => {
                v___x_2781_ = lean_nat_add(v___y_2778_, v___y_2780_);
                lean_dec(v___y_2780_);
                lean_dec(v___y_2778_);
                if v_isShared_2774_ == 0 {
                    lean_ctor_set(v___x_2773_, 4, v_r_2741_);
                    lean_ctor_set(v___x_2773_, 3, v_r_2767_);
                    lean_ctor_set(v___x_2773_, 2, v_v_2739_);
                    lean_ctor_set(v___x_2773_, 1, v_k_2738_);
                    lean_ctor_set(v___x_2773_, 0, v___x_2781_);
                    v___x_2783_ = v___x_2773_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2781_);
                    lean_ctor_set(v_reuseFailAlloc_2787_, 1, v_k_2738_);
                    lean_ctor_set(v_reuseFailAlloc_2787_, 2, v_v_2739_);
                    lean_ctor_set(v_reuseFailAlloc_2787_, 3, v_r_2767_);
                    lean_ctor_set(v_reuseFailAlloc_2787_, 4, v_r_2741_);
                    v___x_2783_ = v_reuseFailAlloc_2787_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_2762_ == 0 {
                    lean_ctor_set(v___x_2761_, 4, v___x_2783_);
                    lean_ctor_set(v___x_2761_, 3, v___y_2779_);
                    lean_ctor_set(v___x_2761_, 2, v_v_2765_);
                    lean_ctor_set(v___x_2761_, 1, v_k_2764_);
                    lean_ctor_set(v___x_2761_, 0, v___x_2776_);
                    v___x_2785_ = v___x_2761_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2776_);
                    lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_k_2764_);
                    lean_ctor_set(v_reuseFailAlloc_2786_, 2, v_v_2765_);
                    lean_ctor_set(v_reuseFailAlloc_2786_, 3, v___y_2779_);
                    lean_ctor_set(v_reuseFailAlloc_2786_, 4, v___x_2783_);
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
                lean_dec(v___y_2789_);
                lean_dec(v___x_2775_);
                if v_isShared_2746_ == 0 {
                    lean_ctor_set(v___x_2745_, 4, v_l_2766_);
                    lean_ctor_set(v___x_2745_, 3, v_tree_2748_);
                    lean_ctor_set(v___x_2745_, 2, v_v_2750_);
                    lean_ctor_set(v___x_2745_, 1, v_k_2749_);
                    lean_ctor_set(v___x_2745_, 0, v___x_2790_);
                    v___x_2792_ = v___x_2745_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2790_);
                    lean_ctor_set(v_reuseFailAlloc_2796_, 1, v_k_2749_);
                    lean_ctor_set(v_reuseFailAlloc_2796_, 2, v_v_2750_);
                    lean_ctor_set(v_reuseFailAlloc_2796_, 3, v_tree_2748_);
                    lean_ctor_set(v_reuseFailAlloc_2796_, 4, v_l_2766_);
                    v___x_2792_ = v_reuseFailAlloc_2796_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_2793_ = lean_nat_add(v___x_2742_, v_size_2768_);
                if lean_obj_tag(v_r_2767_) == 0 {
                    v_size_2794_ = lean_ctor_get(v_r_2767_, 0);
                    lean_inc(v_size_2794_);
                    v___y_2778_ = v___x_2793_;
                    v___y_2779_ = v___x_2792_;
                    v___y_2780_ = v_size_2794_;
                    state = 33;
                    continue;
                } else {
                    v___x_2795_ = lean_unsigned_to_nat(0);
                    v___y_2778_ = v___x_2793_;
                    v___y_2779_ = v___x_2792_;
                    v___y_2780_ = v___x_2795_;
                    state = 33;
                    continue;
                }
            }
            38 => {
                if v_isShared_2746_ == 0 {
                    lean_ctor_set(v___x_2745_, 4, v_r_2741_);
                    lean_ctor_set(v___x_2745_, 3, v___x_2809_);
                    lean_ctor_set(v___x_2745_, 2, v_v_2739_);
                    lean_ctor_set(v___x_2745_, 1, v_k_2738_);
                    lean_ctor_set(v___x_2745_, 0, v___x_2806_);
                    v___x_2811_ = v___x_2745_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2806_);
                    lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_k_2738_);
                    lean_ctor_set(v_reuseFailAlloc_2812_, 2, v_v_2739_);
                    lean_ctor_set(v_reuseFailAlloc_2812_, 3, v___x_2809_);
                    lean_ctor_set(v_reuseFailAlloc_2812_, 4, v_r_2741_);
                    v___x_2811_ = v_reuseFailAlloc_2812_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_2811_;
            }
            40 => {
                if lean_obj_tag(v_l_2740_) == 0 {
                    if lean_obj_tag(v_r_2741_) == 0 {
                        v_k_2823_ = lean_ctor_get(v___x_2747_, 0);
                        lean_inc(v_k_2823_);
                        v_v_2824_ = lean_ctor_get(v___x_2747_, 1);
                        lean_inc(v_v_2824_);
                        lean_dec_ref(v___x_2747_);
                        v_size_2825_ = lean_ctor_get(v_l_2740_, 0);
                        v___x_2826_ = lean_nat_add(v___x_2742_, v_size_2737_);
                        lean_dec(v_size_2737_);
                        v___x_2827_ = lean_nat_add(v___x_2742_, v_size_2825_);
                        if v_isShared_2822_ == 0 {
                            lean_ctor_set(v___x_2821_, 4, v_l_2740_);
                            lean_ctor_set(v___x_2821_, 3, v_tree_2748_);
                            lean_ctor_set(v___x_2821_, 2, v_v_2824_);
                            lean_ctor_set(v___x_2821_, 1, v_k_2823_);
                            lean_ctor_set(v___x_2821_, 0, v___x_2827_);
                            v___x_2829_ = v___x_2821_;
                            state = 41;
                            continue;
                        } else {
                            v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2827_);
                            lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_k_2823_);
                            lean_ctor_set(v_reuseFailAlloc_2833_, 2, v_v_2824_);
                            lean_ctor_set(v_reuseFailAlloc_2833_, 3, v_tree_2748_);
                            lean_ctor_set(v_reuseFailAlloc_2833_, 4, v_l_2740_);
                            v___x_2829_ = v_reuseFailAlloc_2833_;
                            state = 41;
                            continue;
                        }
                    } else {
                        lean_dec(v_size_2737_);
                        v_k_2834_ = lean_ctor_get(v___x_2747_, 0);
                        lean_inc(v_k_2834_);
                        v_v_2835_ = lean_ctor_get(v___x_2747_, 1);
                        lean_inc(v_v_2835_);
                        lean_dec_ref(v___x_2747_);
                        v_k_2836_ = lean_ctor_get(v_l_2740_, 1);
                        v_v_2837_ = lean_ctor_get(v_l_2740_, 2);
                        v_isSharedCheck_2851_ = (!lean_is_exclusive(v_l_2740_)) as u8;
                        if v_isSharedCheck_2851_ == 0 {
                            v_unused_2852_ = lean_ctor_get(v_l_2740_, 4);
                            lean_dec(v_unused_2852_);
                            v_unused_2853_ = lean_ctor_get(v_l_2740_, 3);
                            lean_dec(v_unused_2853_);
                            v_unused_2854_ = lean_ctor_get(v_l_2740_, 0);
                            lean_dec(v_unused_2854_);
                            v___x_2839_ = v_l_2740_;
                            v_isShared_2840_ = v_isSharedCheck_2851_;
                            state = 43;
                            continue;
                        } else {
                            lean_inc(v_v_2837_);
                            lean_inc(v_k_2836_);
                            lean_dec(v_l_2740_);
                            v___x_2839_ = lean_box(0);
                            v_isShared_2840_ = v_isSharedCheck_2851_;
                            state = 43;
                            continue;
                        }
                    }
                } else {
                    if lean_obj_tag(v_r_2741_) == 0 {
                        lean_dec(v_size_2737_);
                        v_k_2855_ = lean_ctor_get(v___x_2747_, 0);
                        lean_inc(v_k_2855_);
                        v_v_2856_ = lean_ctor_get(v___x_2747_, 1);
                        lean_inc(v_v_2856_);
                        lean_dec_ref(v___x_2747_);
                        v___x_2857_ = lean_unsigned_to_nat(3);
                        if v_isShared_2822_ == 0 {
                            lean_ctor_set(v___x_2821_, 4, v_l_2740_);
                            lean_ctor_set(v___x_2821_, 2, v_v_2856_);
                            lean_ctor_set(v___x_2821_, 1, v_k_2855_);
                            lean_ctor_set(v___x_2821_, 0, v___x_2742_);
                            v___x_2859_ = v___x_2821_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2742_);
                            lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_k_2855_);
                            lean_ctor_set(v_reuseFailAlloc_2863_, 2, v_v_2856_);
                            lean_ctor_set(v_reuseFailAlloc_2863_, 3, v_l_2740_);
                            lean_ctor_set(v_reuseFailAlloc_2863_, 4, v_l_2740_);
                            v___x_2859_ = v_reuseFailAlloc_2863_;
                            state = 47;
                            continue;
                        }
                    } else {
                        v_k_2864_ = lean_ctor_get(v___x_2747_, 0);
                        lean_inc(v_k_2864_);
                        v_v_2865_ = lean_ctor_get(v___x_2747_, 1);
                        lean_inc(v_v_2865_);
                        lean_dec_ref(v___x_2747_);
                        if v_isShared_2822_ == 0 {
                            lean_ctor_set(v___x_2821_, 3, v_r_2741_);
                            v___x_2867_ = v___x_2821_;
                            state = 49;
                            continue;
                        } else {
                            v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_size_2737_);
                            lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_k_2738_);
                            lean_ctor_set(v_reuseFailAlloc_2872_, 2, v_v_2739_);
                            lean_ctor_set(v_reuseFailAlloc_2872_, 3, v_r_2741_);
                            lean_ctor_set(v_reuseFailAlloc_2872_, 4, v_r_2741_);
                            v___x_2867_ = v_reuseFailAlloc_2872_;
                            state = 49;
                            continue;
                        }
                    }
                }
            }
            41 => {
                if v_isShared_2746_ == 0 {
                    lean_ctor_set(v___x_2745_, 4, v_r_2741_);
                    lean_ctor_set(v___x_2745_, 3, v___x_2829_);
                    lean_ctor_set(v___x_2745_, 2, v_v_2739_);
                    lean_ctor_set(v___x_2745_, 1, v_k_2738_);
                    lean_ctor_set(v___x_2745_, 0, v___x_2826_);
                    v___x_2831_ = v___x_2745_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2826_);
                    lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_k_2738_);
                    lean_ctor_set(v_reuseFailAlloc_2832_, 2, v_v_2739_);
                    lean_ctor_set(v_reuseFailAlloc_2832_, 3, v___x_2829_);
                    lean_ctor_set(v_reuseFailAlloc_2832_, 4, v_r_2741_);
                    v___x_2831_ = v_reuseFailAlloc_2832_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_2831_;
            }
            43 => {
                v___x_2841_ = lean_unsigned_to_nat(3);
                if v_isShared_2840_ == 0 {
                    lean_ctor_set(v___x_2839_, 4, v_r_2741_);
                    lean_ctor_set(v___x_2839_, 3, v_r_2741_);
                    lean_ctor_set(v___x_2839_, 2, v_v_2835_);
                    lean_ctor_set(v___x_2839_, 1, v_k_2834_);
                    lean_ctor_set(v___x_2839_, 0, v___x_2742_);
                    v___x_2843_ = v___x_2839_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2742_);
                    lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_k_2834_);
                    lean_ctor_set(v_reuseFailAlloc_2850_, 2, v_v_2835_);
                    lean_ctor_set(v_reuseFailAlloc_2850_, 3, v_r_2741_);
                    lean_ctor_set(v_reuseFailAlloc_2850_, 4, v_r_2741_);
                    v___x_2843_ = v_reuseFailAlloc_2850_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_2822_ == 0 {
                    lean_ctor_set(v___x_2821_, 3, v_r_2741_);
                    lean_ctor_set(v___x_2821_, 0, v___x_2742_);
                    v___x_2845_ = v___x_2821_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2742_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 1, v_k_2738_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 2, v_v_2739_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 3, v_r_2741_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 4, v_r_2741_);
                    v___x_2845_ = v_reuseFailAlloc_2849_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_2746_ == 0 {
                    lean_ctor_set(v___x_2745_, 4, v___x_2845_);
                    lean_ctor_set(v___x_2745_, 3, v___x_2843_);
                    lean_ctor_set(v___x_2745_, 2, v_v_2837_);
                    lean_ctor_set(v___x_2745_, 1, v_k_2836_);
                    lean_ctor_set(v___x_2745_, 0, v___x_2841_);
                    v___x_2847_ = v___x_2745_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2841_);
                    lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_k_2836_);
                    lean_ctor_set(v_reuseFailAlloc_2848_, 2, v_v_2837_);
                    lean_ctor_set(v_reuseFailAlloc_2848_, 3, v___x_2843_);
                    lean_ctor_set(v_reuseFailAlloc_2848_, 4, v___x_2845_);
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
                    lean_ctor_set(v___x_2745_, 4, v_r_2741_);
                    lean_ctor_set(v___x_2745_, 3, v___x_2859_);
                    lean_ctor_set(v___x_2745_, 2, v_v_2739_);
                    lean_ctor_set(v___x_2745_, 1, v_k_2738_);
                    lean_ctor_set(v___x_2745_, 0, v___x_2857_);
                    v___x_2861_ = v___x_2745_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2857_);
                    lean_ctor_set(v_reuseFailAlloc_2862_, 1, v_k_2738_);
                    lean_ctor_set(v_reuseFailAlloc_2862_, 2, v_v_2739_);
                    lean_ctor_set(v_reuseFailAlloc_2862_, 3, v___x_2859_);
                    lean_ctor_set(v_reuseFailAlloc_2862_, 4, v_r_2741_);
                    v___x_2861_ = v_reuseFailAlloc_2862_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_2861_;
            }
            49 => {
                v___x_2868_ = lean_unsigned_to_nat(2);
                if v_isShared_2746_ == 0 {
                    lean_ctor_set(v___x_2745_, 4, v___x_2867_);
                    lean_ctor_set(v___x_2745_, 3, v_r_2741_);
                    lean_ctor_set(v___x_2745_, 2, v_v_2865_);
                    lean_ctor_set(v___x_2745_, 1, v_k_2864_);
                    lean_ctor_set(v___x_2745_, 0, v___x_2868_);
                    v___x_2870_ = v___x_2745_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2868_);
                    lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_k_2864_);
                    lean_ctor_set(v_reuseFailAlloc_2871_, 2, v_v_2865_);
                    lean_ctor_set(v_reuseFailAlloc_2871_, 3, v_r_2741_);
                    lean_ctor_set(v_reuseFailAlloc_2871_, 4, v___x_2867_);
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
                v_tree_2889_ = lean_ctor_get(v___x_2888_, 2);
                lean_inc(v_tree_2889_);
                if lean_obj_tag(v_tree_2889_) == 0 {
                    v_k_2890_ = lean_ctor_get(v___x_2888_, 0);
                    lean_inc(v_k_2890_);
                    v_v_2891_ = lean_ctor_get(v___x_2888_, 1);
                    lean_inc(v_v_2891_);
                    lean_dec_ref(v___x_2888_);
                    v_size_2892_ = lean_ctor_get(v_tree_2889_, 0);
                    v___x_2893_ = lean_unsigned_to_nat(3);
                    v___x_2894_ = lean_nat_mul(v___x_2893_, v_size_2892_);
                    v___x_2895_ = lean_nat_dec_lt(v___x_2894_, v_size_2732_);
                    lean_dec(v___x_2894_);
                    if v___x_2895_ == 0 {
                        lean_dec(v_r_2736_);
                        v___x_2896_ = lean_nat_add(v___x_2742_, v_size_2732_);
                        v___x_2897_ = lean_nat_add(v___x_2896_, v_size_2892_);
                        lean_dec(v___x_2896_);
                        if v_isShared_2887_ == 0 {
                            lean_ctor_set(v___x_2886_, 4, v_tree_2889_);
                            lean_ctor_set(v___x_2886_, 3, v_l_2552_);
                            lean_ctor_set(v___x_2886_, 2, v_v_2891_);
                            lean_ctor_set(v___x_2886_, 1, v_k_2890_);
                            lean_ctor_set(v___x_2886_, 0, v___x_2897_);
                            v___x_2899_ = v___x_2886_;
                            state = 52;
                            continue;
                        } else {
                            v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2897_);
                            lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_k_2890_);
                            lean_ctor_set(v_reuseFailAlloc_2900_, 2, v_v_2891_);
                            lean_ctor_set(v_reuseFailAlloc_2900_, 3, v_l_2552_);
                            lean_ctor_set(v_reuseFailAlloc_2900_, 4, v_tree_2889_);
                            v___x_2899_ = v_reuseFailAlloc_2900_;
                            state = 52;
                            continue;
                        }
                    } else {
                        lean_inc(v_l_2735_);
                        lean_inc(v_v_2734_);
                        lean_inc(v_k_2733_);
                        lean_inc(v_size_2732_);
                        v_isSharedCheck_2966_ = (!lean_is_exclusive(v_l_2552_)) as u8;
                        if v_isSharedCheck_2966_ == 0 {
                            v_unused_2967_ = lean_ctor_get(v_l_2552_, 4);
                            lean_dec(v_unused_2967_);
                            v_unused_2968_ = lean_ctor_get(v_l_2552_, 3);
                            lean_dec(v_unused_2968_);
                            v_unused_2969_ = lean_ctor_get(v_l_2552_, 2);
                            lean_dec(v_unused_2969_);
                            v_unused_2970_ = lean_ctor_get(v_l_2552_, 1);
                            lean_dec(v_unused_2970_);
                            v_unused_2971_ = lean_ctor_get(v_l_2552_, 0);
                            lean_dec(v_unused_2971_);
                            v___x_2902_ = v_l_2552_;
                            v_isShared_2903_ = v_isSharedCheck_2966_;
                            state = 53;
                            continue;
                        } else {
                            lean_dec(v_l_2552_);
                            v___x_2902_ = lean_box(0);
                            v_isShared_2903_ = v_isSharedCheck_2966_;
                            state = 53;
                            continue;
                        }
                    }
                } else {
                    if lean_obj_tag(v_l_2735_) == 0 {
                        lean_inc_ref(v_l_2735_);
                        lean_inc(v_v_2734_);
                        lean_inc(v_k_2733_);
                        lean_inc(v_size_2732_);
                        v_isSharedCheck_2995_ = (!lean_is_exclusive(v_l_2552_)) as u8;
                        if v_isSharedCheck_2995_ == 0 {
                            v_unused_2996_ = lean_ctor_get(v_l_2552_, 4);
                            lean_dec(v_unused_2996_);
                            v_unused_2997_ = lean_ctor_get(v_l_2552_, 3);
                            lean_dec(v_unused_2997_);
                            v_unused_2998_ = lean_ctor_get(v_l_2552_, 2);
                            lean_dec(v_unused_2998_);
                            v_unused_2999_ = lean_ctor_get(v_l_2552_, 1);
                            lean_dec(v_unused_2999_);
                            v_unused_3000_ = lean_ctor_get(v_l_2552_, 0);
                            lean_dec(v_unused_3000_);
                            v___x_2973_ = v_l_2552_;
                            v_isShared_2974_ = v_isSharedCheck_2995_;
                            state = 63;
                            continue;
                        } else {
                            lean_dec(v_l_2552_);
                            v___x_2973_ = lean_box(0);
                            v_isShared_2974_ = v_isSharedCheck_2995_;
                            state = 63;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v_r_2736_) == 0 {
                            lean_inc(v_l_2735_);
                            lean_inc(v_v_2734_);
                            lean_inc(v_k_2733_);
                            v_isSharedCheck_3025_ = (!lean_is_exclusive(v_l_2552_)) as u8;
                            if v_isSharedCheck_3025_ == 0 {
                                v_unused_3026_ = lean_ctor_get(v_l_2552_, 4);
                                lean_dec(v_unused_3026_);
                                v_unused_3027_ = lean_ctor_get(v_l_2552_, 3);
                                lean_dec(v_unused_3027_);
                                v_unused_3028_ = lean_ctor_get(v_l_2552_, 2);
                                lean_dec(v_unused_3028_);
                                v_unused_3029_ = lean_ctor_get(v_l_2552_, 1);
                                lean_dec(v_unused_3029_);
                                v_unused_3030_ = lean_ctor_get(v_l_2552_, 0);
                                lean_dec(v_unused_3030_);
                                v___x_3002_ = v_l_2552_;
                                v_isShared_3003_ = v_isSharedCheck_3025_;
                                state = 68;
                                continue;
                            } else {
                                lean_dec(v_l_2552_);
                                v___x_3002_ = lean_box(0);
                                v_isShared_3003_ = v_isSharedCheck_3025_;
                                state = 68;
                                continue;
                            }
                        } else {
                            v_k_3031_ = lean_ctor_get(v___x_2888_, 0);
                            lean_inc(v_k_3031_);
                            v_v_3032_ = lean_ctor_get(v___x_2888_, 1);
                            lean_inc(v_v_3032_);
                            lean_dec_ref(v___x_2888_);
                            v___x_3033_ = lean_unsigned_to_nat(2);
                            if v_isShared_2887_ == 0 {
                                lean_ctor_set(v___x_2886_, 4, v_r_2736_);
                                lean_ctor_set(v___x_2886_, 3, v_l_2552_);
                                lean_ctor_set(v___x_2886_, 2, v_v_3032_);
                                lean_ctor_set(v___x_2886_, 1, v_k_3031_);
                                lean_ctor_set(v___x_2886_, 0, v___x_3033_);
                                v___x_3035_ = v___x_2886_;
                                state = 73;
                                continue;
                            } else {
                                v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
                                lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_k_3031_);
                                lean_ctor_set(v_reuseFailAlloc_3036_, 2, v_v_3032_);
                                lean_ctor_set(v_reuseFailAlloc_3036_, 3, v_l_2552_);
                                lean_ctor_set(v_reuseFailAlloc_3036_, 4, v_r_2736_);
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
                v_size_2904_ = lean_ctor_get(v_l_2735_, 0);
                v_size_2905_ = lean_ctor_get(v_r_2736_, 0);
                v_k_2906_ = lean_ctor_get(v_r_2736_, 1);
                v_v_2907_ = lean_ctor_get(v_r_2736_, 2);
                v_l_2908_ = lean_ctor_get(v_r_2736_, 3);
                v_r_2909_ = lean_ctor_get(v_r_2736_, 4);
                v___x_2910_ = lean_unsigned_to_nat(2);
                v___x_2911_ = lean_nat_mul(v___x_2910_, v_size_2904_);
                v___x_2912_ = lean_nat_dec_lt(v_size_2905_, v___x_2911_);
                lean_dec(v___x_2911_);
                if v___x_2912_ == 0 {
                    lean_inc(v_r_2909_);
                    lean_inc(v_l_2908_);
                    lean_inc(v_v_2907_);
                    lean_inc(v_k_2906_);
                    lean_del_object(v___x_2902_);
                    v_isSharedCheck_2950_ = (!lean_is_exclusive(v_r_2736_)) as u8;
                    if v_isSharedCheck_2950_ == 0 {
                        v_unused_2951_ = lean_ctor_get(v_r_2736_, 4);
                        lean_dec(v_unused_2951_);
                        v_unused_2952_ = lean_ctor_get(v_r_2736_, 3);
                        lean_dec(v_unused_2952_);
                        v_unused_2953_ = lean_ctor_get(v_r_2736_, 2);
                        lean_dec(v_unused_2953_);
                        v_unused_2954_ = lean_ctor_get(v_r_2736_, 1);
                        lean_dec(v_unused_2954_);
                        v_unused_2955_ = lean_ctor_get(v_r_2736_, 0);
                        lean_dec(v_unused_2955_);
                        v___x_2914_ = v_r_2736_;
                        v_isShared_2915_ = v_isSharedCheck_2950_;
                        state = 54;
                        continue;
                    } else {
                        lean_dec(v_r_2736_);
                        v___x_2914_ = lean_box(0);
                        v_isShared_2915_ = v_isSharedCheck_2950_;
                        state = 54;
                        continue;
                    }
                } else {
                    v___x_2956_ = lean_nat_add(v___x_2742_, v_size_2732_);
                    lean_dec(v_size_2732_);
                    v___x_2957_ = lean_nat_add(v___x_2956_, v_size_2892_);
                    lean_dec(v___x_2956_);
                    v___x_2958_ = lean_nat_add(v___x_2742_, v_size_2892_);
                    v___x_2959_ = lean_nat_add(v___x_2958_, v_size_2905_);
                    lean_dec(v___x_2958_);
                    if v_isShared_2887_ == 0 {
                        lean_ctor_set(v___x_2886_, 4, v_tree_2889_);
                        lean_ctor_set(v___x_2886_, 3, v_r_2736_);
                        lean_ctor_set(v___x_2886_, 2, v_v_2891_);
                        lean_ctor_set(v___x_2886_, 1, v_k_2890_);
                        lean_ctor_set(v___x_2886_, 0, v___x_2959_);
                        v___x_2961_ = v___x_2886_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2959_);
                        lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_k_2890_);
                        lean_ctor_set(v_reuseFailAlloc_2965_, 2, v_v_2891_);
                        lean_ctor_set(v_reuseFailAlloc_2965_, 3, v_r_2736_);
                        lean_ctor_set(v_reuseFailAlloc_2965_, 4, v_tree_2889_);
                        v___x_2961_ = v_reuseFailAlloc_2965_;
                        state = 61;
                        continue;
                    }
                }
            }
            54 => {
                v___x_2916_ = lean_nat_add(v___x_2742_, v_size_2732_);
                lean_dec(v_size_2732_);
                v___x_2917_ = lean_nat_add(v___x_2916_, v_size_2892_);
                lean_dec(v___x_2916_);
                v___x_2938_ = lean_nat_add(v___x_2742_, v_size_2904_);
                if lean_obj_tag(v_l_2908_) == 0 {
                    v_size_2948_ = lean_ctor_get(v_l_2908_, 0);
                    lean_inc(v_size_2948_);
                    v___y_2940_ = v_size_2948_;
                    state = 59;
                    continue;
                } else {
                    v___x_2949_ = lean_unsigned_to_nat(0);
                    v___y_2940_ = v___x_2949_;
                    state = 59;
                    continue;
                }
            }
            55 => {
                v___x_2922_ = lean_nat_add(v___y_2920_, v___y_2921_);
                lean_dec(v___y_2921_);
                lean_dec(v___y_2920_);
                lean_inc_ref(v_tree_2889_);
                if v_isShared_2915_ == 0 {
                    lean_ctor_set(v___x_2914_, 4, v_tree_2889_);
                    lean_ctor_set(v___x_2914_, 3, v_r_2909_);
                    lean_ctor_set(v___x_2914_, 2, v_v_2891_);
                    lean_ctor_set(v___x_2914_, 1, v_k_2890_);
                    lean_ctor_set(v___x_2914_, 0, v___x_2922_);
                    v___x_2924_ = v___x_2914_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2937_, 0, v___x_2922_);
                    lean_ctor_set(v_reuseFailAlloc_2937_, 1, v_k_2890_);
                    lean_ctor_set(v_reuseFailAlloc_2937_, 2, v_v_2891_);
                    lean_ctor_set(v_reuseFailAlloc_2937_, 3, v_r_2909_);
                    lean_ctor_set(v_reuseFailAlloc_2937_, 4, v_tree_2889_);
                    v___x_2924_ = v_reuseFailAlloc_2937_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                v_isSharedCheck_2931_ = (!lean_is_exclusive(v_tree_2889_)) as u8;
                if v_isSharedCheck_2931_ == 0 {
                    v_unused_2932_ = lean_ctor_get(v_tree_2889_, 4);
                    lean_dec(v_unused_2932_);
                    v_unused_2933_ = lean_ctor_get(v_tree_2889_, 3);
                    lean_dec(v_unused_2933_);
                    v_unused_2934_ = lean_ctor_get(v_tree_2889_, 2);
                    lean_dec(v_unused_2934_);
                    v_unused_2935_ = lean_ctor_get(v_tree_2889_, 1);
                    lean_dec(v_unused_2935_);
                    v_unused_2936_ = lean_ctor_get(v_tree_2889_, 0);
                    lean_dec(v_unused_2936_);
                    v___x_2926_ = v_tree_2889_;
                    v_isShared_2927_ = v_isSharedCheck_2931_;
                    state = 57;
                    continue;
                } else {
                    lean_dec(v_tree_2889_);
                    v___x_2926_ = lean_box(0);
                    v_isShared_2927_ = v_isSharedCheck_2931_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                if v_isShared_2927_ == 0 {
                    lean_ctor_set(v___x_2926_, 4, v___x_2924_);
                    lean_ctor_set(v___x_2926_, 3, v___y_2919_);
                    lean_ctor_set(v___x_2926_, 2, v_v_2907_);
                    lean_ctor_set(v___x_2926_, 1, v_k_2906_);
                    lean_ctor_set(v___x_2926_, 0, v___x_2917_);
                    v___x_2929_ = v___x_2926_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2917_);
                    lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_k_2906_);
                    lean_ctor_set(v_reuseFailAlloc_2930_, 2, v_v_2907_);
                    lean_ctor_set(v_reuseFailAlloc_2930_, 3, v___y_2919_);
                    lean_ctor_set(v_reuseFailAlloc_2930_, 4, v___x_2924_);
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
                lean_dec(v___y_2940_);
                lean_dec(v___x_2938_);
                if v_isShared_2887_ == 0 {
                    lean_ctor_set(v___x_2886_, 4, v_l_2908_);
                    lean_ctor_set(v___x_2886_, 3, v_l_2735_);
                    lean_ctor_set(v___x_2886_, 2, v_v_2734_);
                    lean_ctor_set(v___x_2886_, 1, v_k_2733_);
                    lean_ctor_set(v___x_2886_, 0, v___x_2941_);
                    v___x_2943_ = v___x_2886_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2941_);
                    lean_ctor_set(v_reuseFailAlloc_2947_, 1, v_k_2733_);
                    lean_ctor_set(v_reuseFailAlloc_2947_, 2, v_v_2734_);
                    lean_ctor_set(v_reuseFailAlloc_2947_, 3, v_l_2735_);
                    lean_ctor_set(v_reuseFailAlloc_2947_, 4, v_l_2908_);
                    v___x_2943_ = v_reuseFailAlloc_2947_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                v___x_2944_ = lean_nat_add(v___x_2742_, v_size_2892_);
                if lean_obj_tag(v_r_2909_) == 0 {
                    v_size_2945_ = lean_ctor_get(v_r_2909_, 0);
                    lean_inc(v_size_2945_);
                    v___y_2919_ = v___x_2943_;
                    v___y_2920_ = v___x_2944_;
                    v___y_2921_ = v_size_2945_;
                    state = 55;
                    continue;
                } else {
                    v___x_2946_ = lean_unsigned_to_nat(0);
                    v___y_2919_ = v___x_2943_;
                    v___y_2920_ = v___x_2944_;
                    v___y_2921_ = v___x_2946_;
                    state = 55;
                    continue;
                }
            }
            61 => {
                if v_isShared_2903_ == 0 {
                    lean_ctor_set(v___x_2902_, 4, v___x_2961_);
                    lean_ctor_set(v___x_2902_, 0, v___x_2957_);
                    v___x_2963_ = v___x_2902_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2957_);
                    lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_k_2733_);
                    lean_ctor_set(v_reuseFailAlloc_2964_, 2, v_v_2734_);
                    lean_ctor_set(v_reuseFailAlloc_2964_, 3, v_l_2735_);
                    lean_ctor_set(v_reuseFailAlloc_2964_, 4, v___x_2961_);
                    v___x_2963_ = v_reuseFailAlloc_2964_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_2963_;
            }
            63 => {
                if lean_obj_tag(v_r_2736_) == 0 {
                    v_k_2975_ = lean_ctor_get(v___x_2888_, 0);
                    lean_inc(v_k_2975_);
                    v_v_2976_ = lean_ctor_get(v___x_2888_, 1);
                    lean_inc(v_v_2976_);
                    lean_dec_ref(v___x_2888_);
                    v_size_2977_ = lean_ctor_get(v_r_2736_, 0);
                    v___x_2978_ = lean_nat_add(v___x_2742_, v_size_2732_);
                    lean_dec(v_size_2732_);
                    v___x_2979_ = lean_nat_add(v___x_2742_, v_size_2977_);
                    if v_isShared_2887_ == 0 {
                        lean_ctor_set(v___x_2886_, 4, v_tree_2889_);
                        lean_ctor_set(v___x_2886_, 3, v_r_2736_);
                        lean_ctor_set(v___x_2886_, 2, v_v_2976_);
                        lean_ctor_set(v___x_2886_, 1, v_k_2975_);
                        lean_ctor_set(v___x_2886_, 0, v___x_2979_);
                        v___x_2981_ = v___x_2886_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2979_);
                        lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_k_2975_);
                        lean_ctor_set(v_reuseFailAlloc_2985_, 2, v_v_2976_);
                        lean_ctor_set(v_reuseFailAlloc_2985_, 3, v_r_2736_);
                        lean_ctor_set(v_reuseFailAlloc_2985_, 4, v_tree_2889_);
                        v___x_2981_ = v_reuseFailAlloc_2985_;
                        state = 64;
                        continue;
                    }
                } else {
                    lean_dec(v_size_2732_);
                    v_k_2986_ = lean_ctor_get(v___x_2888_, 0);
                    lean_inc(v_k_2986_);
                    v_v_2987_ = lean_ctor_get(v___x_2888_, 1);
                    lean_inc(v_v_2987_);
                    lean_dec_ref(v___x_2888_);
                    v___x_2988_ = lean_unsigned_to_nat(3);
                    if v_isShared_2887_ == 0 {
                        lean_ctor_set(v___x_2886_, 4, v_r_2736_);
                        lean_ctor_set(v___x_2886_, 3, v_r_2736_);
                        lean_ctor_set(v___x_2886_, 2, v_v_2987_);
                        lean_ctor_set(v___x_2886_, 1, v_k_2986_);
                        lean_ctor_set(v___x_2886_, 0, v___x_2742_);
                        v___x_2990_ = v___x_2886_;
                        state = 66;
                        continue;
                    } else {
                        v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2742_);
                        lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_k_2986_);
                        lean_ctor_set(v_reuseFailAlloc_2994_, 2, v_v_2987_);
                        lean_ctor_set(v_reuseFailAlloc_2994_, 3, v_r_2736_);
                        lean_ctor_set(v_reuseFailAlloc_2994_, 4, v_r_2736_);
                        v___x_2990_ = v_reuseFailAlloc_2994_;
                        state = 66;
                        continue;
                    }
                }
            }
            64 => {
                if v_isShared_2974_ == 0 {
                    lean_ctor_set(v___x_2973_, 4, v___x_2981_);
                    lean_ctor_set(v___x_2973_, 0, v___x_2978_);
                    v___x_2983_ = v___x_2973_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2978_);
                    lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_k_2733_);
                    lean_ctor_set(v_reuseFailAlloc_2984_, 2, v_v_2734_);
                    lean_ctor_set(v_reuseFailAlloc_2984_, 3, v_l_2735_);
                    lean_ctor_set(v_reuseFailAlloc_2984_, 4, v___x_2981_);
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
                    lean_ctor_set(v___x_2973_, 4, v___x_2990_);
                    lean_ctor_set(v___x_2973_, 0, v___x_2988_);
                    v___x_2992_ = v___x_2973_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2988_);
                    lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_k_2733_);
                    lean_ctor_set(v_reuseFailAlloc_2993_, 2, v_v_2734_);
                    lean_ctor_set(v_reuseFailAlloc_2993_, 3, v_l_2735_);
                    lean_ctor_set(v_reuseFailAlloc_2993_, 4, v___x_2990_);
                    v___x_2992_ = v_reuseFailAlloc_2993_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_2992_;
            }
            68 => {
                v_k_3004_ = lean_ctor_get(v___x_2888_, 0);
                lean_inc(v_k_3004_);
                v_v_3005_ = lean_ctor_get(v___x_2888_, 1);
                lean_inc(v_v_3005_);
                lean_dec_ref(v___x_2888_);
                v_k_3006_ = lean_ctor_get(v_r_2736_, 1);
                v_v_3007_ = lean_ctor_get(v_r_2736_, 2);
                v_isSharedCheck_3021_ = (!lean_is_exclusive(v_r_2736_)) as u8;
                if v_isSharedCheck_3021_ == 0 {
                    v_unused_3022_ = lean_ctor_get(v_r_2736_, 4);
                    lean_dec(v_unused_3022_);
                    v_unused_3023_ = lean_ctor_get(v_r_2736_, 3);
                    lean_dec(v_unused_3023_);
                    v_unused_3024_ = lean_ctor_get(v_r_2736_, 0);
                    lean_dec(v_unused_3024_);
                    v___x_3009_ = v_r_2736_;
                    v_isShared_3010_ = v_isSharedCheck_3021_;
                    state = 69;
                    continue;
                } else {
                    lean_inc(v_v_3007_);
                    lean_inc(v_k_3006_);
                    lean_dec(v_r_2736_);
                    v___x_3009_ = lean_box(0);
                    v_isShared_3010_ = v_isSharedCheck_3021_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                v___x_3011_ = lean_unsigned_to_nat(3);
                if v_isShared_3010_ == 0 {
                    lean_ctor_set(v___x_3009_, 4, v_l_2735_);
                    lean_ctor_set(v___x_3009_, 3, v_l_2735_);
                    lean_ctor_set(v___x_3009_, 2, v_v_2734_);
                    lean_ctor_set(v___x_3009_, 1, v_k_2733_);
                    lean_ctor_set(v___x_3009_, 0, v___x_2742_);
                    v___x_3013_ = v___x_3009_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_2742_);
                    lean_ctor_set(v_reuseFailAlloc_3020_, 1, v_k_2733_);
                    lean_ctor_set(v_reuseFailAlloc_3020_, 2, v_v_2734_);
                    lean_ctor_set(v_reuseFailAlloc_3020_, 3, v_l_2735_);
                    lean_ctor_set(v_reuseFailAlloc_3020_, 4, v_l_2735_);
                    v___x_3013_ = v_reuseFailAlloc_3020_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                if v_isShared_2887_ == 0 {
                    lean_ctor_set(v___x_2886_, 4, v_l_2735_);
                    lean_ctor_set(v___x_2886_, 3, v_l_2735_);
                    lean_ctor_set(v___x_2886_, 2, v_v_3005_);
                    lean_ctor_set(v___x_2886_, 1, v_k_3004_);
                    lean_ctor_set(v___x_2886_, 0, v___x_2742_);
                    v___x_3015_ = v___x_2886_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_2742_);
                    lean_ctor_set(v_reuseFailAlloc_3019_, 1, v_k_3004_);
                    lean_ctor_set(v_reuseFailAlloc_3019_, 2, v_v_3005_);
                    lean_ctor_set(v_reuseFailAlloc_3019_, 3, v_l_2735_);
                    lean_ctor_set(v_reuseFailAlloc_3019_, 4, v_l_2735_);
                    v___x_3015_ = v_reuseFailAlloc_3019_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_3003_ == 0 {
                    lean_ctor_set(v___x_3002_, 4, v___x_3015_);
                    lean_ctor_set(v___x_3002_, 3, v___x_3013_);
                    lean_ctor_set(v___x_3002_, 2, v_v_3007_);
                    lean_ctor_set(v___x_3002_, 1, v_k_3006_);
                    lean_ctor_set(v___x_3002_, 0, v___x_3011_);
                    v___x_3017_ = v___x_3002_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3011_);
                    lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_k_3006_);
                    lean_ctor_set(v_reuseFailAlloc_3018_, 2, v_v_3007_);
                    lean_ctor_set(v_reuseFailAlloc_3018_, 3, v___x_3013_);
                    lean_ctor_set(v_reuseFailAlloc_3018_, 4, v___x_3015_);
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
                v_size_3062_ = lean_ctor_get(v_l_3049_, 0);
                v_size_3063_ = lean_ctor_get(v_r_3050_, 0);
                v_k_3064_ = lean_ctor_get(v_r_3050_, 1);
                v_v_3065_ = lean_ctor_get(v_r_3050_, 2);
                v_l_3066_ = lean_ctor_get(v_r_3050_, 3);
                v_r_3067_ = lean_ctor_get(v_r_3050_, 4);
                v___x_3068_ = lean_unsigned_to_nat(2);
                v___x_3069_ = lean_nat_mul(v___x_3068_, v_size_3062_);
                v___x_3070_ = lean_nat_dec_lt(v_size_3063_, v___x_3069_);
                lean_dec(v___x_3069_);
                if v___x_3070_ == 0 {
                    lean_inc(v_r_3067_);
                    lean_inc(v_l_3066_);
                    lean_inc(v_v_3065_);
                    lean_inc(v_k_3064_);
                    v_isSharedCheck_3099_ = (!lean_is_exclusive(v_r_3050_)) as u8;
                    if v_isSharedCheck_3099_ == 0 {
                        v_unused_3100_ = lean_ctor_get(v_r_3050_, 4);
                        lean_dec(v_unused_3100_);
                        v_unused_3101_ = lean_ctor_get(v_r_3050_, 3);
                        lean_dec(v_unused_3101_);
                        v_unused_3102_ = lean_ctor_get(v_r_3050_, 2);
                        lean_dec(v_unused_3102_);
                        v_unused_3103_ = lean_ctor_get(v_r_3050_, 1);
                        lean_dec(v_unused_3103_);
                        v_unused_3104_ = lean_ctor_get(v_r_3050_, 0);
                        lean_dec(v_unused_3104_);
                        v___x_3072_ = v_r_3050_;
                        v_isShared_3073_ = v_isSharedCheck_3099_;
                        state = 76;
                        continue;
                    } else {
                        lean_dec(v_r_3050_);
                        v___x_3072_ = lean_box(0);
                        v_isShared_3073_ = v_isSharedCheck_3099_;
                        state = 76;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2555_);
                    v___x_3105_ = lean_nat_add(v___x_3044_, v_size_3046_);
                    lean_dec(v_size_3046_);
                    v___x_3106_ = lean_nat_add(v___x_3105_, v_size_3045_);
                    lean_dec(v___x_3105_);
                    v___x_3107_ = lean_nat_add(v___x_3044_, v_size_3045_);
                    lean_dec(v_size_3045_);
                    v___x_3108_ = lean_nat_add(v___x_3107_, v_size_3063_);
                    lean_dec(v___x_3107_);
                    lean_inc_ref(v_impl_3043_);
                    if v_isShared_3061_ == 0 {
                        lean_ctor_set(v___x_3060_, 4, v_impl_3043_);
                        lean_ctor_set(v___x_3060_, 3, v_r_3050_);
                        lean_ctor_set(v___x_3060_, 2, v_v_2551_);
                        lean_ctor_set(v___x_3060_, 1, v_k_2550_);
                        lean_ctor_set(v___x_3060_, 0, v___x_3108_);
                        v___x_3110_ = v___x_3060_;
                        state = 82;
                        continue;
                    } else {
                        v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3108_);
                        lean_ctor_set(v_reuseFailAlloc_3123_, 1, v_k_2550_);
                        lean_ctor_set(v_reuseFailAlloc_3123_, 2, v_v_2551_);
                        lean_ctor_set(v_reuseFailAlloc_3123_, 3, v_r_3050_);
                        lean_ctor_set(v_reuseFailAlloc_3123_, 4, v_impl_3043_);
                        v___x_3110_ = v_reuseFailAlloc_3123_;
                        state = 82;
                        continue;
                    }
                }
            }
            76 => {
                v___x_3074_ = lean_nat_add(v___x_3044_, v_size_3046_);
                lean_dec(v_size_3046_);
                v___x_3075_ = lean_nat_add(v___x_3074_, v_size_3045_);
                lean_dec(v___x_3074_);
                v___x_3087_ = lean_nat_add(v___x_3044_, v_size_3062_);
                if lean_obj_tag(v_l_3066_) == 0 {
                    v_size_3097_ = lean_ctor_get(v_l_3066_, 0);
                    lean_inc(v_size_3097_);
                    v___y_3089_ = v_size_3097_;
                    state = 80;
                    continue;
                } else {
                    v___x_3098_ = lean_unsigned_to_nat(0);
                    v___y_3089_ = v___x_3098_;
                    state = 80;
                    continue;
                }
            }
            77 => {
                v___x_3080_ = lean_nat_add(v___y_3078_, v___y_3079_);
                lean_dec(v___y_3079_);
                lean_dec(v___y_3078_);
                if v_isShared_3073_ == 0 {
                    lean_ctor_set(v___x_3072_, 4, v_impl_3043_);
                    lean_ctor_set(v___x_3072_, 3, v_r_3067_);
                    lean_ctor_set(v___x_3072_, 2, v_v_2551_);
                    lean_ctor_set(v___x_3072_, 1, v_k_2550_);
                    lean_ctor_set(v___x_3072_, 0, v___x_3080_);
                    v___x_3082_ = v___x_3072_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3080_);
                    lean_ctor_set(v_reuseFailAlloc_3086_, 1, v_k_2550_);
                    lean_ctor_set(v_reuseFailAlloc_3086_, 2, v_v_2551_);
                    lean_ctor_set(v_reuseFailAlloc_3086_, 3, v_r_3067_);
                    lean_ctor_set(v_reuseFailAlloc_3086_, 4, v_impl_3043_);
                    v___x_3082_ = v_reuseFailAlloc_3086_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                if v_isShared_3061_ == 0 {
                    lean_ctor_set(v___x_3060_, 4, v___x_3082_);
                    lean_ctor_set(v___x_3060_, 3, v___y_3077_);
                    lean_ctor_set(v___x_3060_, 2, v_v_3065_);
                    lean_ctor_set(v___x_3060_, 1, v_k_3064_);
                    lean_ctor_set(v___x_3060_, 0, v___x_3075_);
                    v___x_3084_ = v___x_3060_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3075_);
                    lean_ctor_set(v_reuseFailAlloc_3085_, 1, v_k_3064_);
                    lean_ctor_set(v_reuseFailAlloc_3085_, 2, v_v_3065_);
                    lean_ctor_set(v_reuseFailAlloc_3085_, 3, v___y_3077_);
                    lean_ctor_set(v_reuseFailAlloc_3085_, 4, v___x_3082_);
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
                lean_dec(v___y_3089_);
                lean_dec(v___x_3087_);
                if v_isShared_2556_ == 0 {
                    lean_ctor_set(v___x_2555_, 4, v_l_3066_);
                    lean_ctor_set(v___x_2555_, 3, v_l_3049_);
                    lean_ctor_set(v___x_2555_, 2, v_v_3048_);
                    lean_ctor_set(v___x_2555_, 1, v_k_3047_);
                    lean_ctor_set(v___x_2555_, 0, v___x_3090_);
                    v___x_3092_ = v___x_2555_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3090_);
                    lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_k_3047_);
                    lean_ctor_set(v_reuseFailAlloc_3096_, 2, v_v_3048_);
                    lean_ctor_set(v_reuseFailAlloc_3096_, 3, v_l_3049_);
                    lean_ctor_set(v_reuseFailAlloc_3096_, 4, v_l_3066_);
                    v___x_3092_ = v_reuseFailAlloc_3096_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                v___x_3093_ = lean_nat_add(v___x_3044_, v_size_3045_);
                lean_dec(v_size_3045_);
                if lean_obj_tag(v_r_3067_) == 0 {
                    v_size_3094_ = lean_ctor_get(v_r_3067_, 0);
                    lean_inc(v_size_3094_);
                    v___y_3077_ = v___x_3092_;
                    v___y_3078_ = v___x_3093_;
                    v___y_3079_ = v_size_3094_;
                    state = 77;
                    continue;
                } else {
                    v___x_3095_ = lean_unsigned_to_nat(0);
                    v___y_3077_ = v___x_3092_;
                    v___y_3078_ = v___x_3093_;
                    v___y_3079_ = v___x_3095_;
                    state = 77;
                    continue;
                }
            }
            82 => {
                v_isSharedCheck_3117_ = (!lean_is_exclusive(v_impl_3043_)) as u8;
                if v_isSharedCheck_3117_ == 0 {
                    v_unused_3118_ = lean_ctor_get(v_impl_3043_, 4);
                    lean_dec(v_unused_3118_);
                    v_unused_3119_ = lean_ctor_get(v_impl_3043_, 3);
                    lean_dec(v_unused_3119_);
                    v_unused_3120_ = lean_ctor_get(v_impl_3043_, 2);
                    lean_dec(v_unused_3120_);
                    v_unused_3121_ = lean_ctor_get(v_impl_3043_, 1);
                    lean_dec(v_unused_3121_);
                    v_unused_3122_ = lean_ctor_get(v_impl_3043_, 0);
                    lean_dec(v_unused_3122_);
                    v___x_3112_ = v_impl_3043_;
                    v_isShared_3113_ = v_isSharedCheck_3117_;
                    state = 83;
                    continue;
                } else {
                    lean_dec(v_impl_3043_);
                    v___x_3112_ = lean_box(0);
                    v_isShared_3113_ = v_isSharedCheck_3117_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                if v_isShared_3113_ == 0 {
                    lean_ctor_set(v___x_3112_, 4, v___x_3110_);
                    lean_ctor_set(v___x_3112_, 3, v_l_3049_);
                    lean_ctor_set(v___x_3112_, 2, v_v_3048_);
                    lean_ctor_set(v___x_3112_, 1, v_k_3047_);
                    lean_ctor_set(v___x_3112_, 0, v___x_3106_);
                    v___x_3115_ = v___x_3112_;
                    state = 84;
                    continue;
                } else {
                    v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3106_);
                    lean_ctor_set(v_reuseFailAlloc_3116_, 1, v_k_3047_);
                    lean_ctor_set(v_reuseFailAlloc_3116_, 2, v_v_3048_);
                    lean_ctor_set(v_reuseFailAlloc_3116_, 3, v_l_3049_);
                    lean_ctor_set(v_reuseFailAlloc_3116_, 4, v___x_3110_);
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
                v_size_3143_ = lean_ctor_get(v_r_3136_, 0);
                v___x_3144_ = lean_nat_add(v___x_3044_, v_size_3137_);
                lean_dec(v_size_3137_);
                v___x_3145_ = lean_nat_add(v___x_3044_, v_size_3143_);
                if v_isShared_3142_ == 0 {
                    lean_ctor_set(v___x_3141_, 4, v_impl_3043_);
                    lean_ctor_set(v___x_3141_, 3, v_r_3136_);
                    lean_ctor_set(v___x_3141_, 2, v_v_2551_);
                    lean_ctor_set(v___x_3141_, 1, v_k_2550_);
                    lean_ctor_set(v___x_3141_, 0, v___x_3145_);
                    v___x_3147_ = v___x_3141_;
                    state = 87;
                    continue;
                } else {
                    v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3145_);
                    lean_ctor_set(v_reuseFailAlloc_3151_, 1, v_k_2550_);
                    lean_ctor_set(v_reuseFailAlloc_3151_, 2, v_v_2551_);
                    lean_ctor_set(v_reuseFailAlloc_3151_, 3, v_r_3136_);
                    lean_ctor_set(v_reuseFailAlloc_3151_, 4, v_impl_3043_);
                    v___x_3147_ = v_reuseFailAlloc_3151_;
                    state = 87;
                    continue;
                }
            }
            87 => {
                if v_isShared_2556_ == 0 {
                    lean_ctor_set(v___x_2555_, 4, v___x_3147_);
                    lean_ctor_set(v___x_2555_, 3, v_l_3135_);
                    lean_ctor_set(v___x_2555_, 2, v_v_3139_);
                    lean_ctor_set(v___x_2555_, 1, v_k_3138_);
                    lean_ctor_set(v___x_2555_, 0, v___x_3144_);
                    v___x_3149_ = v___x_2555_;
                    state = 88;
                    continue;
                } else {
                    v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3144_);
                    lean_ctor_set(v_reuseFailAlloc_3150_, 1, v_k_3138_);
                    lean_ctor_set(v_reuseFailAlloc_3150_, 2, v_v_3139_);
                    lean_ctor_set(v_reuseFailAlloc_3150_, 3, v_l_3135_);
                    lean_ctor_set(v_reuseFailAlloc_3150_, 4, v___x_3147_);
                    v___x_3149_ = v_reuseFailAlloc_3150_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                return v___x_3149_;
            }
            89 => {
                v___x_3160_ = lean_unsigned_to_nat(3);
                if v_isShared_3159_ == 0 {
                    lean_ctor_set(v___x_3158_, 3, v_r_3136_);
                    lean_ctor_set(v___x_3158_, 2, v_v_2551_);
                    lean_ctor_set(v___x_3158_, 1, v_k_2550_);
                    lean_ctor_set(v___x_3158_, 0, v___x_3044_);
                    v___x_3162_ = v___x_3158_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3044_);
                    lean_ctor_set(v_reuseFailAlloc_3166_, 1, v_k_2550_);
                    lean_ctor_set(v_reuseFailAlloc_3166_, 2, v_v_2551_);
                    lean_ctor_set(v_reuseFailAlloc_3166_, 3, v_r_3136_);
                    lean_ctor_set(v_reuseFailAlloc_3166_, 4, v_r_3136_);
                    v___x_3162_ = v_reuseFailAlloc_3166_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_2556_ == 0 {
                    lean_ctor_set(v___x_2555_, 4, v___x_3162_);
                    lean_ctor_set(v___x_2555_, 3, v_l_3135_);
                    lean_ctor_set(v___x_2555_, 2, v_v_3156_);
                    lean_ctor_set(v___x_2555_, 1, v_k_3155_);
                    lean_ctor_set(v___x_2555_, 0, v___x_3160_);
                    v___x_3164_ = v___x_2555_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3160_);
                    lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_k_3155_);
                    lean_ctor_set(v_reuseFailAlloc_3165_, 2, v_v_3156_);
                    lean_ctor_set(v_reuseFailAlloc_3165_, 3, v_l_3135_);
                    lean_ctor_set(v_reuseFailAlloc_3165_, 4, v___x_3162_);
                    v___x_3164_ = v_reuseFailAlloc_3165_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_3164_;
            }
            92 => {
                v_k_3177_ = lean_ctor_get(v_r_3171_, 1);
                v_v_3178_ = lean_ctor_get(v_r_3171_, 2);
                v_isSharedCheck_3192_ = (!lean_is_exclusive(v_r_3171_)) as u8;
                if v_isSharedCheck_3192_ == 0 {
                    v_unused_3193_ = lean_ctor_get(v_r_3171_, 4);
                    lean_dec(v_unused_3193_);
                    v_unused_3194_ = lean_ctor_get(v_r_3171_, 3);
                    lean_dec(v_unused_3194_);
                    v_unused_3195_ = lean_ctor_get(v_r_3171_, 0);
                    lean_dec(v_unused_3195_);
                    v___x_3180_ = v_r_3171_;
                    v_isShared_3181_ = v_isSharedCheck_3192_;
                    state = 93;
                    continue;
                } else {
                    lean_inc(v_v_3178_);
                    lean_inc(v_k_3177_);
                    lean_dec(v_r_3171_);
                    v___x_3180_ = lean_box(0);
                    v_isShared_3181_ = v_isSharedCheck_3192_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                v___x_3182_ = lean_unsigned_to_nat(3);
                if v_isShared_3181_ == 0 {
                    lean_ctor_set(v___x_3180_, 4, v_l_3135_);
                    lean_ctor_set(v___x_3180_, 3, v_l_3135_);
                    lean_ctor_set(v___x_3180_, 2, v_v_3173_);
                    lean_ctor_set(v___x_3180_, 1, v_k_3172_);
                    lean_ctor_set(v___x_3180_, 0, v___x_3044_);
                    v___x_3184_ = v___x_3180_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3044_);
                    lean_ctor_set(v_reuseFailAlloc_3191_, 1, v_k_3172_);
                    lean_ctor_set(v_reuseFailAlloc_3191_, 2, v_v_3173_);
                    lean_ctor_set(v_reuseFailAlloc_3191_, 3, v_l_3135_);
                    lean_ctor_set(v_reuseFailAlloc_3191_, 4, v_l_3135_);
                    v___x_3184_ = v_reuseFailAlloc_3191_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                if v_isShared_3176_ == 0 {
                    lean_ctor_set(v___x_3175_, 4, v_l_3135_);
                    lean_ctor_set(v___x_3175_, 2, v_v_2551_);
                    lean_ctor_set(v___x_3175_, 1, v_k_2550_);
                    lean_ctor_set(v___x_3175_, 0, v___x_3044_);
                    v___x_3186_ = v___x_3175_;
                    state = 95;
                    continue;
                } else {
                    v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3044_);
                    lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_k_2550_);
                    lean_ctor_set(v_reuseFailAlloc_3190_, 2, v_v_2551_);
                    lean_ctor_set(v_reuseFailAlloc_3190_, 3, v_l_3135_);
                    lean_ctor_set(v_reuseFailAlloc_3190_, 4, v_l_3135_);
                    v___x_3186_ = v_reuseFailAlloc_3190_;
                    state = 95;
                    continue;
                }
            }
            95 => {
                if v_isShared_2556_ == 0 {
                    lean_ctor_set(v___x_2555_, 4, v___x_3186_);
                    lean_ctor_set(v___x_2555_, 3, v___x_3184_);
                    lean_ctor_set(v___x_2555_, 2, v_v_3178_);
                    lean_ctor_set(v___x_2555_, 1, v_k_3177_);
                    lean_ctor_set(v___x_2555_, 0, v___x_3182_);
                    v___x_3188_ = v___x_2555_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3182_);
                    lean_ctor_set(v_reuseFailAlloc_3189_, 1, v_k_3177_);
                    lean_ctor_set(v_reuseFailAlloc_3189_, 2, v_v_3178_);
                    lean_ctor_set(v_reuseFailAlloc_3189_, 3, v___x_3184_);
                    lean_ctor_set(v_reuseFailAlloc_3189_, 4, v___x_3186_);
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
    mut v_k_3209_: *mut LeanObject,
    mut v_t_3210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3211_: *mut LeanObject = core::ptr::null_mut();
    v_res_3211_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(
        v_k_3209_, v_t_3210_,
    );
    lean_dec(v_k_3209_);
    return v_res_3211_;
}
pub unsafe fn l_Lean_Options_erase(
    mut v_o_3212_: *mut LeanObject,
    mut v_k_3213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3217_: u8 = 0;
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: u8 = 0;
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3214_ = lean_ctor_get(v_o_3212_, 0);
                v_isSharedCheck_3225_ = (!lean_is_exclusive(v_o_3212_)) as u8;
                if v_isSharedCheck_3225_ == 0 {
                    v___x_3216_ = v_o_3212_;
                    v_isShared_3217_ = v_isSharedCheck_3225_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_3214_);
                    lean_dec(v_o_3212_);
                    v___x_3216_ = lean_box(0);
                    v_isShared_3217_ = v_isSharedCheck_3225_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_map_3214_);
                v___x_3218_ =
                    l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(
                        v_k_3213_,
                        v_map_3214_,
                    );
                v___x_3219_ = lean_box(0);
                v___x_3220_ =
                    l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(
                        v___x_3219_,
                        v_map_3214_,
                    );
                lean_dec(v_map_3214_);
                v___x_3221_ = l_List_any___at___00Lean_Options_erase_spec__2(v___x_3220_);
                lean_dec(v___x_3220_);
                if v_isShared_3217_ == 0 {
                    lean_ctor_set(v___x_3216_, 0, v___x_3218_);
                    v___x_3223_ = v___x_3216_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3218_);
                    v___x_3223_ = v_reuseFailAlloc_3224_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_3223_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3221_,
                );
                return v___x_3223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_erase___boxed(
    mut v_o_3226_: *mut LeanObject,
    mut v_k_3227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3228_: *mut LeanObject = core::ptr::null_mut();
    v_res_3228_ = l_Lean_Options_erase(v_o_3226_, v_k_3227_);
    lean_dec(v_k_3227_);
    return v_res_3228_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0(
    mut v_00_u03b2_3229_: *mut LeanObject,
    mut v_k_3230_: *mut LeanObject,
    mut v_t_3231_: *mut LeanObject,
    mut v_h_3232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    v___x_3233_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(
        v_k_3230_, v_t_3231_,
    );
    return v___x_3233_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___boxed(
    mut v_00_u03b2_3234_: *mut LeanObject,
    mut v_k_3235_: *mut LeanObject,
    mut v_t_3236_: *mut LeanObject,
    mut v_h_3237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3238_: *mut LeanObject = core::ptr::null_mut();
    v_res_3238_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0(
        v_00_u03b2_3234_,
        v_k_3235_,
        v_t_3236_,
        v_h_3237_,
    );
    lean_dec(v_k_3235_);
    return v_res_3238_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(
    mut v_b_u2082_3239_: *mut LeanObject,
    mut v_f_3240_: *mut LeanObject,
    mut v_a_3241_: *mut LeanObject,
    mut v_x_3242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3247_: u8 = 0;
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3252_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3242_) == 0 {
                    lean_dec(v_a_3241_);
                    lean_dec_ref(v_f_3240_);
                    v___x_3243_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3243_, 0, v_b_u2082_3239_);
                    return v___x_3243_;
                } else {
                    v_val_3244_ = lean_ctor_get(v_x_3242_, 0);
                    v_isSharedCheck_3252_ = (!lean_is_exclusive(v_x_3242_)) as u8;
                    if v_isSharedCheck_3252_ == 0 {
                        v___x_3246_ = v_x_3242_;
                        v_isShared_3247_ = v_isSharedCheck_3252_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3244_);
                        lean_dec(v_x_3242_);
                        v___x_3246_ = lean_box(0);
                        v_isShared_3247_ = v_isSharedCheck_3252_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3248_ = lean_apply_3(v_f_3240_, v_a_3241_, v_val_3244_, v_b_u2082_3239_);
                if v_isShared_3247_ == 0 {
                    lean_ctor_set(v___x_3246_, 0, v___x_3248_);
                    v___x_3250_ = v___x_3246_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
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
    mut v_b_u2082_3253_: *mut LeanObject,
    mut v_f_3254_: *mut LeanObject,
    mut v_a_3255_: *mut LeanObject,
    mut v_k_3256_: *mut LeanObject,
    mut v_t_3257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3265_: u8 = 0;
    let mut v___x_3266_: u8 = 0;
    let mut v_impl_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3277_: u8 = 0;
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_3257_) == 0 {
                    v_size_3258_ = lean_ctor_get(v_t_3257_, 0);
                    v_k_3259_ = lean_ctor_get(v_t_3257_, 1);
                    v_v_3260_ = lean_ctor_get(v_t_3257_, 2);
                    v_l_3261_ = lean_ctor_get(v_t_3257_, 3);
                    v_r_3262_ = lean_ctor_get(v_t_3257_, 4);
                    v_isSharedCheck_3277_ = (!lean_is_exclusive(v_t_3257_)) as u8;
                    if v_isSharedCheck_3277_ == 0 {
                        v___x_3264_ = v_t_3257_;
                        v_isShared_3265_ = v_isSharedCheck_3277_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_3262_);
                        lean_inc(v_l_3261_);
                        lean_inc(v_v_3260_);
                        lean_inc(v_k_3259_);
                        lean_inc(v_size_3258_);
                        lean_dec(v_t_3257_);
                        v___x_3264_ = lean_box(0);
                        v_isShared_3265_ = v_isSharedCheck_3277_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3278_ = lean_box(0);
                    v___x_3279_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(v_b_u2082_3253_, v_f_3254_, v_a_3255_, v___x_3278_);
                    v_val_3280_ = lean_ctor_get(v___x_3279_, 0);
                    lean_inc(v_val_3280_);
                    lean_dec(v___x_3279_);
                    v___x_3281_ = lean_unsigned_to_nat(1);
                    v___x_3282_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_3282_, 0, v___x_3281_);
                    lean_ctor_set(v___x_3282_, 1, v_k_3256_);
                    lean_ctor_set(v___x_3282_, 2, v_val_3280_);
                    lean_ctor_set(v___x_3282_, 3, v_t_3257_);
                    lean_ctor_set(v___x_3282_, 4, v_t_3257_);
                    return v___x_3282_;
                }
            }
            1 => {
                v___x_3266_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3256_, v_k_3259_);
                match v___x_3266_ {
                    0 => {
                        lean_del_object(v___x_3264_);
                        lean_dec(v_size_3258_);
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
                        lean_dec(v_k_3259_);
                        v___x_3269_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3269_, 0, v_v_3260_);
                        v___x_3270_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(v_b_u2082_3253_, v_f_3254_, v_a_3255_, v___x_3269_);
                        v_val_3271_ = lean_ctor_get(v___x_3270_, 0);
                        lean_inc(v_val_3271_);
                        lean_dec(v___x_3270_);
                        if v_isShared_3265_ == 0 {
                            lean_ctor_set(v___x_3264_, 2, v_val_3271_);
                            lean_ctor_set(v___x_3264_, 1, v_k_3256_);
                            v___x_3273_ = v___x_3264_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_size_3258_);
                            lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_k_3256_);
                            lean_ctor_set(v_reuseFailAlloc_3274_, 2, v_val_3271_);
                            lean_ctor_set(v_reuseFailAlloc_3274_, 3, v_l_3261_);
                            lean_ctor_set(v_reuseFailAlloc_3274_, 4, v_r_3262_);
                            v___x_3273_ = v_reuseFailAlloc_3274_;
                            state = 2;
                            continue;
                        }
                    }
                    _ => {
                        lean_del_object(v___x_3264_);
                        lean_dec(v_size_3258_);
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
    mut v_f_3283_: *mut LeanObject,
    mut v_init_3284_: *mut LeanObject,
    mut v_x_3285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3285_) == 0 {
                    v_k_3286_ = lean_ctor_get(v_x_3285_, 1);
                    lean_inc_n(v_k_3286_, 2);
                    v_v_3287_ = lean_ctor_get(v_x_3285_, 2);
                    lean_inc(v_v_3287_);
                    v_l_3288_ = lean_ctor_get(v_x_3285_, 3);
                    lean_inc(v_l_3288_);
                    v_r_3289_ = lean_ctor_get(v_x_3285_, 4);
                    lean_inc(v_r_3289_);
                    lean_dec_ref_known(v_x_3285_, 5);
                    lean_inc_ref_n(v_f_3283_, 2);
                    v___x_3290_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_3283_, v_init_3284_, v_l_3288_);
                    v___x_3291_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_v_3287_, v_f_3283_, v_k_3286_, v_k_3286_, v___x_3290_);
                    v_init_3284_ = v___x_3291_;
                    v_x_3285_ = v_r_3289_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_f_3283_);
                    return v_init_3284_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_mergeBy(
    mut v_f_3293_: *mut LeanObject,
    mut v_o1_3294_: *mut LeanObject,
    mut v_o2_3295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3297_: u8 = 0;
    let mut v_map_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3299_: u8 = 0;
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3302_: u8 = 0;
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3296_ = lean_ctor_get(v_o1_3294_, 0);
                lean_inc(v_map_3296_);
                v_hasTrace_3297_ = lean_ctor_get_uint8(
                    v_o1_3294_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                lean_dec_ref(v_o1_3294_);
                v_map_3298_ = lean_ctor_get(v_o2_3295_, 0);
                v_hasTrace_3299_ = lean_ctor_get_uint8(
                    v_o2_3295_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3310_ = (!lean_is_exclusive(v_o2_3295_)) as u8;
                if v_isSharedCheck_3310_ == 0 {
                    v___x_3301_ = v_o2_3295_;
                    v_isShared_3302_ = v_isSharedCheck_3310_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_3298_);
                    lean_dec(v_o2_3295_);
                    v___x_3301_ = lean_box(0);
                    v_isShared_3302_ = v_isSharedCheck_3310_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3303_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_3293_, v_map_3296_, v_map_3298_);
                if v_hasTrace_3297_ == 0 {
                    if v_isShared_3302_ == 0 {
                        lean_ctor_set(v___x_3301_, 0, v___x_3303_);
                        v___x_3305_ = v___x_3301_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3303_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_3306_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v_hasTrace_3299_,
                        );
                        v___x_3305_ = v_reuseFailAlloc_3306_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_3302_ == 0 {
                        lean_ctor_set(v___x_3301_, 0, v___x_3303_);
                        v___x_3308_ = v___x_3301_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3303_);
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
                lean_ctor_set_uint8(
                    v___x_3308_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_hasTrace_3297_,
                );
                return v___x_3308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0(
    mut v_b_u2082_3311_: *mut LeanObject,
    mut v_f_3312_: *mut LeanObject,
    mut v_a_3313_: *mut LeanObject,
    mut v_k_3314_: *mut LeanObject,
    mut v_t_3315_: *mut LeanObject,
    mut v_hl_3316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_f_3318_: *mut LeanObject,
    mut v_init_3319_: *mut LeanObject,
    mut v_t_3320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    v___x_3321_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_3318_, v_init_3319_, v_t_3320_);
    return v___x_3321_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__12() -> *mut LeanObject {
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    v___x_3354_ = l_Lean_OptionDecl_declName___autoParam___closed__10;
    v___x_3355_ = l_Lean_mkAtom(v___x_3354_);
    return v___x_3355_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__13() -> *mut LeanObject {
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    v___x_3356_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__12),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__12_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__12,
    );
    v___x_3357_ = l_Lean_OptionDecl_declName___autoParam___closed__5;
    v___x_3358_ = lean_array_push(v___x_3357_, v___x_3356_);
    return v___x_3358_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__18() -> *mut LeanObject {
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    v___x_3367_ = l_Lean_OptionDecl_declName___autoParam___closed__17;
    v___x_3368_ = l_Lean_mkAtom(v___x_3367_);
    return v___x_3368_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__19() -> *mut LeanObject {
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    v___x_3369_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__18),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__18_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__18,
    );
    v___x_3370_ = l_Lean_OptionDecl_declName___autoParam___closed__5;
    v___x_3371_ = lean_array_push(v___x_3370_, v___x_3369_);
    return v___x_3371_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__20() -> *mut LeanObject {
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    v___x_3372_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__19),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__19_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__19,
    );
    v___x_3373_ = l_Lean_OptionDecl_declName___autoParam___closed__16;
    v___x_3374_ = lean_box(2);
    v___x_3375_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3375_, 0, v___x_3374_);
    lean_ctor_set(v___x_3375_, 1, v___x_3373_);
    lean_ctor_set(v___x_3375_, 2, v___x_3372_);
    return v___x_3375_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__21() -> *mut LeanObject {
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    v___x_3376_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__20),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__20_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__20,
    );
    v___x_3377_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__13),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__13_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__13,
    );
    v___x_3378_ = lean_array_push(v___x_3377_, v___x_3376_);
    return v___x_3378_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__22() -> *mut LeanObject {
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    v___x_3379_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__21),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__21_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__21,
    );
    v___x_3380_ = l_Lean_OptionDecl_declName___autoParam___closed__11;
    v___x_3381_ = lean_box(2);
    v___x_3382_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3382_, 0, v___x_3381_);
    lean_ctor_set(v___x_3382_, 1, v___x_3380_);
    lean_ctor_set(v___x_3382_, 2, v___x_3379_);
    return v___x_3382_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__23() -> *mut LeanObject {
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    v___x_3383_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__22),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__22_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__22,
    );
    v___x_3384_ = l_Lean_OptionDecl_declName___autoParam___closed__5;
    v___x_3385_ = lean_array_push(v___x_3384_, v___x_3383_);
    return v___x_3385_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__24() -> *mut LeanObject {
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    v___x_3386_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__23),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__23_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__23,
    );
    v___x_3387_ = l_Lean_OptionDecl_declName___autoParam___closed__9;
    v___x_3388_ = lean_box(2);
    v___x_3389_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3389_, 0, v___x_3388_);
    lean_ctor_set(v___x_3389_, 1, v___x_3387_);
    lean_ctor_set(v___x_3389_, 2, v___x_3386_);
    return v___x_3389_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__25() -> *mut LeanObject {
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    v___x_3390_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__24),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__24_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__24,
    );
    v___x_3391_ = l_Lean_OptionDecl_declName___autoParam___closed__5;
    v___x_3392_ = lean_array_push(v___x_3391_, v___x_3390_);
    return v___x_3392_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__26() -> *mut LeanObject {
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    v___x_3393_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__25),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__25_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__25,
    );
    v___x_3394_ = l_Lean_OptionDecl_declName___autoParam___closed__7;
    v___x_3395_ = lean_box(2);
    v___x_3396_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3396_, 0, v___x_3395_);
    lean_ctor_set(v___x_3396_, 1, v___x_3394_);
    lean_ctor_set(v___x_3396_, 2, v___x_3393_);
    return v___x_3396_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__27() -> *mut LeanObject {
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    v___x_3397_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__26),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__26_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__26,
    );
    v___x_3398_ = l_Lean_OptionDecl_declName___autoParam___closed__5;
    v___x_3399_ = lean_array_push(v___x_3398_, v___x_3397_);
    return v___x_3399_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam___closed__28() -> *mut LeanObject {
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    v___x_3400_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__27),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__27_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__27,
    );
    v___x_3401_ = l_Lean_OptionDecl_declName___autoParam___closed__4;
    v___x_3402_ = lean_box(2);
    v___x_3403_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3403_, 0, v___x_3402_);
    lean_ctor_set(v___x_3403_, 1, v___x_3401_);
    lean_ctor_set(v___x_3403_, 2, v___x_3400_);
    return v___x_3403_;
}
pub unsafe fn _init_l_Lean_OptionDecl_declName___autoParam() -> *mut LeanObject {
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    v___x_3404_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__28),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__28_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__28,
    );
    return v___x_3404_;
}
pub unsafe fn _init_l_Lean_instInhabitedOptionDecl_default___closed__3() -> *mut LeanObject {
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    v___x_3411_ = lean_box(0);
    v___x_3412_ = l_Lean_instInhabitedOptionDeprecation_default___closed__0;
    v___x_3413_ = l_Lean_instInhabitedDataValue_default;
    v___x_3414_ = l_Lean_instInhabitedOptionDecl_default___closed__2;
    v___x_3415_ = lean_box(0);
    v___x_3416_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3416_, 0, v___x_3415_);
    lean_ctor_set(v___x_3416_, 1, v___x_3414_);
    lean_ctor_set(v___x_3416_, 2, v___x_3413_);
    lean_ctor_set(v___x_3416_, 3, v___x_3412_);
    lean_ctor_set(v___x_3416_, 4, v___x_3411_);
    return v___x_3416_;
}
pub unsafe fn _init_l_Lean_instInhabitedOptionDecl_default() -> *mut LeanObject {
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    v___x_3417_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedOptionDecl_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedOptionDecl_default___closed__3_once),
        _init_l_Lean_instInhabitedOptionDecl_default___closed__3,
    );
    return v___x_3417_;
}
pub unsafe fn _init_l_Lean_instInhabitedOptionDecl() -> *mut LeanObject {
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    v___x_3418_ = l_Lean_instInhabitedOptionDecl_default;
    return v___x_3418_;
}
pub unsafe fn l_Lean_OptionDecl_fullDescr(mut v_self_3424_: *mut LeanObject) -> *mut LeanObject {
    let mut v_descr_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: u8 = 0;
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: u8 = 0;
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3429_ = lean_ctor_get(v_self_3424_, 0);
                lean_inc(v_name_3429_);
                v_descr_3430_ = lean_ctor_get(v_self_3424_, 3);
                lean_inc_ref(v_descr_3430_);
                lean_dec_ref(v_self_3424_);
                v___x_3431_ = l_Lean_OptionDecl_fullDescr___closed__2;
                v___x_3432_ = l_Lean_Name_isPrefixOf(v___x_3431_, v_name_3429_);
                lean_dec(v_name_3429_);
                if v___x_3432_ == 0 {
                    return v_descr_3430_;
                } else {
                    v___x_3433_ = lean_string_utf8_byte_size(v_descr_3430_);
                    v___x_3434_ = lean_unsigned_to_nat(0);
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
pub unsafe fn _init_l_Lean_instInhabitedOptionDecls() -> *mut LeanObject {
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    v___x_3438_ = lean_box(1);
    return v___x_3438_;
}
pub unsafe fn l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    v___x_3440_ = lean_box(1);
    v___x_3441_ = lean_st_mk_ref(v___x_3440_);
    v___x_3442_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3442_, 0, v___x_3441_);
    return v___x_3442_;
}
pub unsafe fn l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2____boxed(
    mut v_a_3443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3444_: *mut LeanObject = core::ptr::null_mut();
    v_res_3444_ = l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_();
    return v_res_3444_;
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Data_Options_0__Lean_OptionDecl_sameDecl_spec__0(
    mut v_x_3445_: *mut LeanObject,
    mut v_x_3446_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_3445_) == 0 {
        if lean_obj_tag(v_x_3446_) == 0 {
            let mut v___x_3447_: u8 = 0;
            v___x_3447_ = 1;
            return v___x_3447_;
        } else {
            let mut v___x_3448_: u8 = 0;
            v___x_3448_ = 0;
            return v___x_3448_;
        }
    } else {
        if lean_obj_tag(v_x_3446_) == 0 {
            let mut v___x_3449_: u8 = 0;
            v___x_3449_ = 0;
            return v___x_3449_;
        } else {
            let mut v_val_3450_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_3451_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3452_: u8 = 0;
            v_val_3450_ = lean_ctor_get(v_x_3445_, 0);
            v_val_3451_ = lean_ctor_get(v_x_3446_, 0);
            v___x_3452_ = lean_string_dec_eq(v_val_3450_, v_val_3451_);
            return v___x_3452_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Data_Options_0__Lean_OptionDecl_sameDecl_spec__0___boxed(
    mut v_x_3453_: *mut LeanObject,
    mut v_x_3454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3455_: u8 = 0;
    let mut v_r_3456_: *mut LeanObject = core::ptr::null_mut();
    v_res_3455_ = l_Option_instBEq_beq___at___00__private_Lean_Data_Options_0__Lean_OptionDecl_sameDecl_spec__0(v_x_3453_, v_x_3454_);
    lean_dec(v_x_3454_);
    lean_dec(v_x_3453_);
    v_r_3456_ = lean_box((v_res_3455_) as usize);
    return v_r_3456_;
}
pub unsafe fn l___private_Lean_Data_Options_0__Lean_OptionDecl_sameDecl(
    mut v_a_3457_: *mut LeanObject,
    mut v_b_3458_: *mut LeanObject,
) -> u8 {
    let mut v_name_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3468_: u8 = 0;
    let mut v___x_3469_: u8 = 0;
    let mut v___x_3470_: u8 = 0;
    let mut v_val_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_since_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_since_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: u8 = 0;
    let mut v___x_3478_: u8 = 0;
    let mut v___x_3479_: u8 = 0;
    let mut v___x_3480_: u8 = 0;
    let mut v___x_3481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3459_ = lean_ctor_get(v_a_3457_, 0);
                lean_inc(v_name_3459_);
                v_defValue_3460_ = lean_ctor_get(v_a_3457_, 2);
                lean_inc_ref(v_defValue_3460_);
                v_descr_3461_ = lean_ctor_get(v_a_3457_, 3);
                lean_inc_ref(v_descr_3461_);
                v_deprecation_x3f_3462_ = lean_ctor_get(v_a_3457_, 4);
                lean_inc(v_deprecation_x3f_3462_);
                lean_dec_ref(v_a_3457_);
                v_name_3463_ = lean_ctor_get(v_b_3458_, 0);
                lean_inc(v_name_3463_);
                v_defValue_3464_ = lean_ctor_get(v_b_3458_, 2);
                lean_inc_ref(v_defValue_3464_);
                v_descr_3465_ = lean_ctor_get(v_b_3458_, 3);
                lean_inc_ref(v_descr_3465_);
                v_deprecation_x3f_3466_ = lean_ctor_get(v_b_3458_, 4);
                lean_inc(v_deprecation_x3f_3466_);
                lean_dec_ref(v_b_3458_);
                v___x_3480_ = lean_name_eq(v_name_3459_, v_name_3463_);
                lean_dec(v_name_3463_);
                lean_dec(v_name_3459_);
                if v___x_3480_ == 0 {
                    lean_dec_ref(v_defValue_3464_);
                    lean_dec_ref(v_defValue_3460_);
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
                    lean_dec(v_deprecation_x3f_3466_);
                    lean_dec_ref(v_descr_3465_);
                    lean_dec(v_deprecation_x3f_3462_);
                    lean_dec_ref(v_descr_3461_);
                    return v___y_3468_;
                } else {
                    v___x_3469_ = lean_string_dec_eq(v_descr_3461_, v_descr_3465_);
                    lean_dec_ref(v_descr_3465_);
                    lean_dec_ref(v_descr_3461_);
                    if v___x_3469_ == 0 {
                        lean_dec(v_deprecation_x3f_3466_);
                        lean_dec(v_deprecation_x3f_3462_);
                        return v___x_3469_;
                    } else {
                        if lean_obj_tag(v_deprecation_x3f_3462_) == 0 {
                            if lean_obj_tag(v_deprecation_x3f_3466_) == 0 {
                                return v___x_3469_;
                            } else {
                                lean_dec(v_deprecation_x3f_3466_);
                                v___x_3470_ = 0;
                                return v___x_3470_;
                            }
                        } else {
                            if lean_obj_tag(v_deprecation_x3f_3466_) == 1 {
                                v_val_3471_ = lean_ctor_get(v_deprecation_x3f_3462_, 0);
                                lean_inc(v_val_3471_);
                                lean_dec_ref_known(v_deprecation_x3f_3462_, 1);
                                v_val_3472_ = lean_ctor_get(v_deprecation_x3f_3466_, 0);
                                lean_inc(v_val_3472_);
                                lean_dec_ref_known(v_deprecation_x3f_3466_, 1);
                                v_since_3473_ = lean_ctor_get(v_val_3471_, 0);
                                lean_inc_ref(v_since_3473_);
                                v_text_x3f_3474_ = lean_ctor_get(v_val_3471_, 1);
                                lean_inc(v_text_x3f_3474_);
                                lean_dec(v_val_3471_);
                                v_since_3475_ = lean_ctor_get(v_val_3472_, 0);
                                lean_inc_ref(v_since_3475_);
                                v_text_x3f_3476_ = lean_ctor_get(v_val_3472_, 1);
                                lean_inc(v_text_x3f_3476_);
                                lean_dec(v_val_3472_);
                                v___x_3477_ = lean_string_dec_eq(v_since_3473_, v_since_3475_);
                                lean_dec_ref(v_since_3475_);
                                lean_dec_ref(v_since_3473_);
                                if v___x_3477_ == 0 {
                                    lean_dec(v_text_x3f_3476_);
                                    lean_dec(v_text_x3f_3474_);
                                    return v___x_3477_;
                                } else {
                                    v___x_3478_ = l_Option_instBEq_beq___at___00__private_Lean_Data_Options_0__Lean_OptionDecl_sameDecl_spec__0(v_text_x3f_3474_, v_text_x3f_3476_);
                                    lean_dec(v_text_x3f_3476_);
                                    lean_dec(v_text_x3f_3474_);
                                    return v___x_3478_;
                                }
                            } else {
                                lean_dec_ref_known(v_deprecation_x3f_3462_, 1);
                                lean_dec(v_deprecation_x3f_3466_);
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
    mut v_a_3482_: *mut LeanObject,
    mut v_b_3483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3484_: u8 = 0;
    let mut v_r_3485_: *mut LeanObject = core::ptr::null_mut();
    v_res_3484_ = l___private_Lean_Data_Options_0__Lean_OptionDecl_sameDecl(v_a_3482_, v_b_3483_);
    v_r_3485_ = lean_box((v_res_3484_) as usize);
    return v_r_3485_;
}
pub unsafe fn _init_l_Lean_registerOption___closed__1() -> *mut LeanObject {
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    v___x_3487_ = l_Lean_registerOption___closed__0;
    v___x_3488_ = lean_mk_io_user_error(v___x_3487_);
    return v___x_3488_;
}
pub unsafe fn lean_register_option(
    mut v_name_3491_: *mut LeanObject,
    mut v_decl_3492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v___x_3499_: u8 = 0;
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: u8 = 0;
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: u8 = 0;
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3528_: u8 = 0;
    let mut v_a_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3532_: u8 = 0;
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3536_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3494_ = l_Lean_initializing();
                if lean_obj_tag(v___x_3494_) == 0 {
                    v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
                    v_isSharedCheck_3528_ = (!lean_is_exclusive(v___x_3494_)) as u8;
                    if v_isSharedCheck_3528_ == 0 {
                        v___x_3497_ = v___x_3494_;
                        v_isShared_3498_ = v_isSharedCheck_3528_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3495_);
                        lean_dec(v___x_3494_);
                        v___x_3497_ = lean_box(0);
                        v_isShared_3498_ = v_isSharedCheck_3528_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_decl_3492_);
                    lean_dec(v_name_3491_);
                    v_a_3529_ = lean_ctor_get(v___x_3494_, 0);
                    v_isSharedCheck_3536_ = (!lean_is_exclusive(v___x_3494_)) as u8;
                    if v_isSharedCheck_3536_ == 0 {
                        v___x_3531_ = v___x_3494_;
                        v_isShared_3532_ = v_isSharedCheck_3536_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3529_);
                        lean_dec(v___x_3494_);
                        v___x_3531_ = lean_box(0);
                        v_isShared_3532_ = v_isSharedCheck_3536_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3499_ = (lean_unbox(v_a_3495_) as u8);
                if v___x_3499_ == 0 {
                    lean_dec(v_a_3495_);
                    lean_dec_ref(v_decl_3492_);
                    lean_dec(v_name_3491_);
                    v___x_3500_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_registerOption___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_registerOption___closed__1_once),
                        _init_l_Lean_registerOption___closed__1,
                    );
                    if v_isShared_3498_ == 0 {
                        lean_ctor_set_tag(v___x_3497_, 1);
                        lean_ctor_set(v___x_3497_, 0, v___x_3500_);
                        v___x_3502_ = v___x_3497_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3500_);
                        v___x_3502_ = v_reuseFailAlloc_3503_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3504_ = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
                    v___x_3505_ = lean_st_ref_get(v___x_3504_);
                    v___x_3506_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3505_, v_name_3491_);
                    if lean_obj_tag(v___x_3506_) == 1 {
                        lean_dec(v___x_3505_);
                        v_val_3507_ = lean_ctor_get(v___x_3506_, 0);
                        lean_inc(v_val_3507_);
                        lean_dec_ref_known(v___x_3506_, 1);
                        v___x_3508_ = l___private_Lean_Data_Options_0__Lean_OptionDecl_sameDecl(
                            v_decl_3492_,
                            v_val_3507_,
                        );
                        if v___x_3508_ == 0 {
                            v___x_3509_ = l_Lean_registerOption___closed__2;
                            v___x_3510_ = (lean_unbox(v_a_3495_) as u8);
                            lean_dec(v_a_3495_);
                            v___x_3511_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_name_3491_,
                                    v___x_3510_,
                                );
                            v___x_3512_ = lean_string_append(v___x_3509_, v___x_3511_);
                            lean_dec_ref(v___x_3511_);
                            v___x_3513_ = l_Lean_registerOption___closed__3;
                            v___x_3514_ = lean_string_append(v___x_3512_, v___x_3513_);
                            v___x_3515_ = lean_mk_io_user_error(v___x_3514_);
                            if v_isShared_3498_ == 0 {
                                lean_ctor_set_tag(v___x_3497_, 1);
                                lean_ctor_set(v___x_3497_, 0, v___x_3515_);
                                v___x_3517_ = v___x_3497_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3515_);
                                v___x_3517_ = v_reuseFailAlloc_3518_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3495_);
                            lean_dec(v_name_3491_);
                            v___x_3519_ = lean_box(0);
                            if v_isShared_3498_ == 0 {
                                lean_ctor_set(v___x_3497_, 0, v___x_3519_);
                                v___x_3521_ = v___x_3497_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3522_, 0, v___x_3519_);
                                v___x_3521_ = v_reuseFailAlloc_3522_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_3506_);
                        lean_dec(v_a_3495_);
                        v___x_3523_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_3491_, v_decl_3492_, v___x_3505_);
                        v___x_3524_ = lean_st_ref_set(v___x_3504_, v___x_3523_);
                        if v_isShared_3498_ == 0 {
                            lean_ctor_set(v___x_3497_, 0, v___x_3524_);
                            v___x_3526_ = v___x_3497_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
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
                    v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
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
    mut v_name_3537_: *mut LeanObject,
    mut v_decl_3538_: *mut LeanObject,
    mut v_a_3539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3540_: *mut LeanObject = core::ptr::null_mut();
    v_res_3540_ = lean_register_option(v_name_3537_, v_decl_3538_);
    return v_res_3540_;
}
pub unsafe fn l_Lean_getOptionDecls() -> *mut LeanObject {
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    v___x_3542_ = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
    v___x_3543_ = lean_st_ref_get(v___x_3542_);
    v___x_3544_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3544_, 0, v___x_3543_);
    return v___x_3544_;
}
pub unsafe fn l_Lean_getOptionDecls___boxed(mut v_a_3545_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3546_: *mut LeanObject = core::ptr::null_mut();
    v_res_3546_ = l_Lean_getOptionDecls();
    return v_res_3546_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(
    mut v_init_3547_: *mut LeanObject,
    mut v_x_3548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3548_) == 0 {
                    v_k_3549_ = lean_ctor_get(v_x_3548_, 1);
                    v_v_3550_ = lean_ctor_get(v_x_3548_, 2);
                    v_l_3551_ = lean_ctor_get(v_x_3548_, 3);
                    v_r_3552_ = lean_ctor_get(v_x_3548_, 4);
                    v___x_3553_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_3547_, v_l_3551_);
                    lean_inc(v_v_3550_);
                    lean_inc(v_k_3549_);
                    v___x_3554_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3554_, 0, v_k_3549_);
                    lean_ctor_set(v___x_3554_, 1, v_v_3550_);
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
    mut v_init_3557_: *mut LeanObject,
    mut v_x_3558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3559_: *mut LeanObject = core::ptr::null_mut();
    v_res_3559_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_3557_, v_x_3558_);
    lean_dec(v_x_3558_);
    return v_res_3559_;
}
pub unsafe fn lean_get_option_decls_array() -> *mut LeanObject {
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3567_: u8 = 0;
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3573_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3563_ = l_Lean_getOptionDecls();
                v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
                v_isSharedCheck_3573_ = (!lean_is_exclusive(v___x_3563_)) as u8;
                if v_isSharedCheck_3573_ == 0 {
                    v___x_3566_ = v___x_3563_;
                    v_isShared_3567_ = v_isSharedCheck_3573_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3564_);
                    lean_dec(v___x_3563_);
                    v___x_3566_ = lean_box(0);
                    v_isShared_3567_ = v_isSharedCheck_3573_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3568_ = l_Lean_getOptionDeclsArray___closed__0;
                v___x_3569_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v___x_3568_, v_a_3564_);
                lean_dec(v_a_3564_);
                if v_isShared_3567_ == 0 {
                    lean_ctor_set(v___x_3566_, 0, v___x_3569_);
                    v___x_3571_ = v___x_3566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3569_);
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
    mut v_a_3574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3575_: *mut LeanObject = core::ptr::null_mut();
    v_res_3575_ = lean_get_option_decls_array();
    return v_res_3575_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(
    mut v_init_3576_: *mut LeanObject,
    mut v_t_3577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    v___x_3578_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_3576_, v_t_3577_);
    return v___x_3578_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0___boxed(
    mut v_init_3579_: *mut LeanObject,
    mut v_t_3580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3581_: *mut LeanObject = core::ptr::null_mut();
    v_res_3581_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(
        v_init_3579_,
        v_t_3580_,
    );
    lean_dec(v_t_3580_);
    return v_res_3581_;
}
pub unsafe fn l_Lean_getOptionDecl(mut v_name_3584_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3590_: u8 = 0;
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: u8 = 0;
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3586_ = l_Lean_getOptionDecls();
                v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
                v_isSharedCheck_3606_ = (!lean_is_exclusive(v___x_3586_)) as u8;
                if v_isSharedCheck_3606_ == 0 {
                    v___x_3589_ = v___x_3586_;
                    v_isShared_3590_ = v_isSharedCheck_3606_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3587_);
                    lean_dec(v___x_3586_);
                    v___x_3589_ = lean_box(0);
                    v_isShared_3590_ = v_isSharedCheck_3606_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3591_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_3587_, v_name_3584_);
                lean_dec(v_a_3587_);
                if lean_obj_tag(v___x_3591_) == 1 {
                    lean_dec(v_name_3584_);
                    v_val_3592_ = lean_ctor_get(v___x_3591_, 0);
                    lean_inc(v_val_3592_);
                    lean_dec_ref_known(v___x_3591_, 1);
                    if v_isShared_3590_ == 0 {
                        lean_ctor_set(v___x_3589_, 0, v_val_3592_);
                        v___x_3594_ = v___x_3589_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_val_3592_);
                        v___x_3594_ = v_reuseFailAlloc_3595_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3591_);
                    v___x_3596_ = l_Lean_getOptionDecl___closed__0;
                    v___x_3597_ = 1;
                    v___x_3598_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_3584_,
                        v___x_3597_,
                    );
                    v___x_3599_ = lean_string_append(v___x_3596_, v___x_3598_);
                    lean_dec_ref(v___x_3598_);
                    v___x_3600_ = l_Lean_getOptionDecl___closed__1;
                    v___x_3601_ = lean_string_append(v___x_3599_, v___x_3600_);
                    v___x_3602_ = lean_mk_io_user_error(v___x_3601_);
                    if v_isShared_3590_ == 0 {
                        lean_ctor_set_tag(v___x_3589_, 1);
                        lean_ctor_set(v___x_3589_, 0, v___x_3602_);
                        v___x_3604_ = v___x_3589_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3602_);
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
    mut v_name_3607_: *mut LeanObject,
    mut v_a_3608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3609_: *mut LeanObject = core::ptr::null_mut();
    v_res_3609_ = l_Lean_getOptionDecl(v_name_3607_);
    return v_res_3609_;
}
pub unsafe fn l_Lean_getOptionDefaultValue(mut v_name_3610_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3616_: u8 = 0;
    let mut v_defValue_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3621_: u8 = 0;
    let mut v_a_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3625_: u8 = 0;
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3629_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3612_ = l_Lean_getOptionDecl(v_name_3610_);
                if lean_obj_tag(v___x_3612_) == 0 {
                    v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
                    v_isSharedCheck_3621_ = (!lean_is_exclusive(v___x_3612_)) as u8;
                    if v_isSharedCheck_3621_ == 0 {
                        v___x_3615_ = v___x_3612_;
                        v_isShared_3616_ = v_isSharedCheck_3621_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3613_);
                        lean_dec(v___x_3612_);
                        v___x_3615_ = lean_box(0);
                        v_isShared_3616_ = v_isSharedCheck_3621_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3622_ = lean_ctor_get(v___x_3612_, 0);
                    v_isSharedCheck_3629_ = (!lean_is_exclusive(v___x_3612_)) as u8;
                    if v_isSharedCheck_3629_ == 0 {
                        v___x_3624_ = v___x_3612_;
                        v_isShared_3625_ = v_isSharedCheck_3629_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3622_);
                        lean_dec(v___x_3612_);
                        v___x_3624_ = lean_box(0);
                        v_isShared_3625_ = v_isSharedCheck_3629_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_defValue_3617_ = lean_ctor_get(v_a_3613_, 2);
                lean_inc_ref(v_defValue_3617_);
                lean_dec(v_a_3613_);
                if v_isShared_3616_ == 0 {
                    lean_ctor_set(v___x_3615_, 0, v_defValue_3617_);
                    v___x_3619_ = v___x_3615_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_defValue_3617_);
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
                    v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
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
    mut v_name_3630_: *mut LeanObject,
    mut v_a_3631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3632_: *mut LeanObject = core::ptr::null_mut();
    v_res_3632_ = l_Lean_getOptionDefaultValue(v_name_3630_);
    return v_res_3632_;
}
pub unsafe fn l_Lean_getOptionDescr(mut v_name_3633_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3639_: u8 = 0;
    let mut v_descr_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3644_: u8 = 0;
    let mut v_a_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3648_: u8 = 0;
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3652_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3635_ = l_Lean_getOptionDecl(v_name_3633_);
                if lean_obj_tag(v___x_3635_) == 0 {
                    v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
                    v_isSharedCheck_3644_ = (!lean_is_exclusive(v___x_3635_)) as u8;
                    if v_isSharedCheck_3644_ == 0 {
                        v___x_3638_ = v___x_3635_;
                        v_isShared_3639_ = v_isSharedCheck_3644_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3636_);
                        lean_dec(v___x_3635_);
                        v___x_3638_ = lean_box(0);
                        v_isShared_3639_ = v_isSharedCheck_3644_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3645_ = lean_ctor_get(v___x_3635_, 0);
                    v_isSharedCheck_3652_ = (!lean_is_exclusive(v___x_3635_)) as u8;
                    if v_isSharedCheck_3652_ == 0 {
                        v___x_3647_ = v___x_3635_;
                        v_isShared_3648_ = v_isSharedCheck_3652_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3645_);
                        lean_dec(v___x_3635_);
                        v___x_3647_ = lean_box(0);
                        v_isShared_3648_ = v_isSharedCheck_3652_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_descr_3640_ = lean_ctor_get(v_a_3636_, 3);
                lean_inc_ref(v_descr_3640_);
                lean_dec(v_a_3636_);
                if v_isShared_3639_ == 0 {
                    lean_ctor_set(v___x_3638_, 0, v_descr_3640_);
                    v___x_3642_ = v___x_3638_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_descr_3640_);
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
                    v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
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
    mut v_name_3653_: *mut LeanObject,
    mut v_a_3654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3655_: *mut LeanObject = core::ptr::null_mut();
    v_res_3655_ = l_Lean_getOptionDescr(v_name_3653_);
    return v_res_3655_;
}
pub unsafe fn l_Lean_instMonadOptionsOfMonadLift___redArg(
    mut v_inst_3656_: *mut LeanObject,
    mut v_inst_3657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    v___x_3658_ = lean_apply_2(v_inst_3656_, lean_box(0), v_inst_3657_);
    return v___x_3658_;
}
pub unsafe fn l_Lean_instMonadOptionsOfMonadLift(
    mut v_m_3659_: *mut LeanObject,
    mut v_n_3660_: *mut LeanObject,
    mut v_inst_3661_: *mut LeanObject,
    mut v_inst_3662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    v___x_3663_ = lean_apply_2(v_inst_3661_, lean_box(0), v_inst_3662_);
    return v___x_3663_;
}
pub unsafe fn l_Lean_getBoolOption___redArg___lam__0(
    mut v_k_3664_: *mut LeanObject,
    mut v_toPure_3665_: *mut LeanObject,
    mut v_defValue_3666_: u8,
    mut v_opts_3667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    v_map_3668_ = lean_ctor_get(v_opts_3667_, 0);
    v___x_3669_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3668_,
            v_k_3664_,
        );
    if lean_obj_tag(v___x_3669_) == 0 {
        let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
        v___x_3670_ = lean_box((v_defValue_3666_) as usize);
        v___x_3671_ = lean_apply_2(v_toPure_3665_, lean_box(0), v___x_3670_);
        return v___x_3671_;
    } else {
        let mut v_val_3672_: *mut LeanObject = core::ptr::null_mut();
        v_val_3672_ = lean_ctor_get(v___x_3669_, 0);
        lean_inc(v_val_3672_);
        lean_dec_ref_known(v___x_3669_, 1);
        if lean_obj_tag(v_val_3672_) == 1 {
            let mut v_v_3673_: u8 = 0;
            let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
            v_v_3673_ = lean_ctor_get_uint8(v_val_3672_, 0 as u32);
            lean_dec_ref_known(v_val_3672_, 0);
            v___x_3674_ = lean_box((v_v_3673_) as usize);
            v___x_3675_ = lean_apply_2(v_toPure_3665_, lean_box(0), v___x_3674_);
            return v___x_3675_;
        } else {
            let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_val_3672_);
            v___x_3676_ = lean_box((v_defValue_3666_) as usize);
            v___x_3677_ = lean_apply_2(v_toPure_3665_, lean_box(0), v___x_3676_);
            return v___x_3677_;
        }
    }
}
pub unsafe fn l_Lean_getBoolOption___redArg___lam__0___boxed(
    mut v_k_3678_: *mut LeanObject,
    mut v_toPure_3679_: *mut LeanObject,
    mut v_defValue_3680_: *mut LeanObject,
    mut v_opts_3681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_boxed_3682_: u8 = 0;
    let mut v_res_3683_: *mut LeanObject = core::ptr::null_mut();
    v_defValue_boxed_3682_ = (lean_unbox(v_defValue_3680_) as u8);
    v_res_3683_ = l_Lean_getBoolOption___redArg___lam__0(
        v_k_3678_,
        v_toPure_3679_,
        v_defValue_boxed_3682_,
        v_opts_3681_,
    );
    lean_dec_ref(v_opts_3681_);
    lean_dec(v_k_3678_);
    return v_res_3683_;
}
pub unsafe fn l_Lean_getBoolOption___redArg(
    mut v_inst_3684_: *mut LeanObject,
    mut v_inst_3685_: *mut LeanObject,
    mut v_k_3686_: *mut LeanObject,
    mut v_defValue_3687_: u8,
) -> *mut LeanObject {
    let mut v_toApplicative_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3688_ = lean_ctor_get(v_inst_3684_, 0);
    lean_inc_ref(v_toApplicative_3688_);
    v_toBind_3689_ = lean_ctor_get(v_inst_3684_, 1);
    lean_inc(v_toBind_3689_);
    lean_dec_ref(v_inst_3684_);
    v_toPure_3690_ = lean_ctor_get(v_toApplicative_3688_, 1);
    lean_inc(v_toPure_3690_);
    lean_dec_ref(v_toApplicative_3688_);
    v___x_3691_ = lean_box((v_defValue_3687_) as usize);
    v___f_3692_ = lean_alloc_closure(
        l_Lean_getBoolOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3692_, 0, v_k_3686_);
    lean_closure_set(v___f_3692_, 1, v_toPure_3690_);
    lean_closure_set(v___f_3692_, 2, v___x_3691_);
    v___x_3693_ = lean_apply_4(
        v_toBind_3689_,
        lean_box(0),
        lean_box(0),
        v_inst_3685_,
        v___f_3692_,
    );
    return v___x_3693_;
}
pub unsafe fn l_Lean_getBoolOption___redArg___boxed(
    mut v_inst_3694_: *mut LeanObject,
    mut v_inst_3695_: *mut LeanObject,
    mut v_k_3696_: *mut LeanObject,
    mut v_defValue_3697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_boxed_3698_: u8 = 0;
    let mut v_res_3699_: *mut LeanObject = core::ptr::null_mut();
    v_defValue_boxed_3698_ = (lean_unbox(v_defValue_3697_) as u8);
    v_res_3699_ = l_Lean_getBoolOption___redArg(
        v_inst_3694_,
        v_inst_3695_,
        v_k_3696_,
        v_defValue_boxed_3698_,
    );
    return v_res_3699_;
}
pub unsafe fn l_Lean_getBoolOption(
    mut v_m_3700_: *mut LeanObject,
    mut v_inst_3701_: *mut LeanObject,
    mut v_inst_3702_: *mut LeanObject,
    mut v_k_3703_: *mut LeanObject,
    mut v_defValue_3704_: u8,
) -> *mut LeanObject {
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    v___x_3705_ =
        l_Lean_getBoolOption___redArg(v_inst_3701_, v_inst_3702_, v_k_3703_, v_defValue_3704_);
    return v___x_3705_;
}
pub unsafe fn l_Lean_getBoolOption___boxed(
    mut v_m_3706_: *mut LeanObject,
    mut v_inst_3707_: *mut LeanObject,
    mut v_inst_3708_: *mut LeanObject,
    mut v_k_3709_: *mut LeanObject,
    mut v_defValue_3710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_boxed_3711_: u8 = 0;
    let mut v_res_3712_: *mut LeanObject = core::ptr::null_mut();
    v_defValue_boxed_3711_ = (lean_unbox(v_defValue_3710_) as u8);
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
    mut v_k_3713_: *mut LeanObject,
    mut v_toPure_3714_: *mut LeanObject,
    mut v_defValue_3715_: *mut LeanObject,
    mut v_opts_3716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    v_map_3717_ = lean_ctor_get(v_opts_3716_, 0);
    v___x_3718_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3717_,
            v_k_3713_,
        );
    if lean_obj_tag(v___x_3718_) == 0 {
        let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
        v___x_3719_ = lean_apply_2(v_toPure_3714_, lean_box(0), v_defValue_3715_);
        return v___x_3719_;
    } else {
        let mut v_val_3720_: *mut LeanObject = core::ptr::null_mut();
        v_val_3720_ = lean_ctor_get(v___x_3718_, 0);
        lean_inc(v_val_3720_);
        lean_dec_ref_known(v___x_3718_, 1);
        if lean_obj_tag(v_val_3720_) == 3 {
            let mut v_v_3721_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_defValue_3715_);
            v_v_3721_ = lean_ctor_get(v_val_3720_, 0);
            lean_inc(v_v_3721_);
            lean_dec_ref_known(v_val_3720_, 1);
            v___x_3722_ = lean_apply_2(v_toPure_3714_, lean_box(0), v_v_3721_);
            return v___x_3722_;
        } else {
            let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_val_3720_);
            v___x_3723_ = lean_apply_2(v_toPure_3714_, lean_box(0), v_defValue_3715_);
            return v___x_3723_;
        }
    }
}
pub unsafe fn l_Lean_getNatOption___redArg___lam__0___boxed(
    mut v_k_3724_: *mut LeanObject,
    mut v_toPure_3725_: *mut LeanObject,
    mut v_defValue_3726_: *mut LeanObject,
    mut v_opts_3727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3728_: *mut LeanObject = core::ptr::null_mut();
    v_res_3728_ = l_Lean_getNatOption___redArg___lam__0(
        v_k_3724_,
        v_toPure_3725_,
        v_defValue_3726_,
        v_opts_3727_,
    );
    lean_dec_ref(v_opts_3727_);
    lean_dec(v_k_3724_);
    return v_res_3728_;
}
pub unsafe fn l_Lean_getNatOption___redArg(
    mut v_inst_3729_: *mut LeanObject,
    mut v_inst_3730_: *mut LeanObject,
    mut v_k_3731_: *mut LeanObject,
    mut v_defValue_3732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3733_ = lean_ctor_get(v_inst_3729_, 0);
    lean_inc_ref(v_toApplicative_3733_);
    v_toBind_3734_ = lean_ctor_get(v_inst_3729_, 1);
    lean_inc(v_toBind_3734_);
    lean_dec_ref(v_inst_3729_);
    v_toPure_3735_ = lean_ctor_get(v_toApplicative_3733_, 1);
    lean_inc(v_toPure_3735_);
    lean_dec_ref(v_toApplicative_3733_);
    v___f_3736_ = lean_alloc_closure(
        l_Lean_getNatOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3736_, 0, v_k_3731_);
    lean_closure_set(v___f_3736_, 1, v_toPure_3735_);
    lean_closure_set(v___f_3736_, 2, v_defValue_3732_);
    v___x_3737_ = lean_apply_4(
        v_toBind_3734_,
        lean_box(0),
        lean_box(0),
        v_inst_3730_,
        v___f_3736_,
    );
    return v___x_3737_;
}
pub unsafe fn l_Lean_getNatOption(
    mut v_m_3738_: *mut LeanObject,
    mut v_inst_3739_: *mut LeanObject,
    mut v_inst_3740_: *mut LeanObject,
    mut v_k_3741_: *mut LeanObject,
    mut v_defValue_3742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    v___x_3743_ =
        l_Lean_getNatOption___redArg(v_inst_3739_, v_inst_3740_, v_k_3741_, v_defValue_3742_);
    return v___x_3743_;
}
pub unsafe fn l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0(
    mut v_inst_3744_: *mut LeanObject,
    mut v_f_3745_: *mut LeanObject,
    mut v_00_u03b2_3746_: *mut LeanObject,
    mut v___y_3747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    v___x_3748_ = lean_apply_3(v_inst_3744_, lean_box(0), v_f_3745_, v___y_3747_);
    return v___x_3748_;
}
pub unsafe fn l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1(
    mut v_inst_3749_: *mut LeanObject,
    mut v_inst_3750_: *mut LeanObject,
    mut v_00_u03b1_3751_: *mut LeanObject,
    mut v_f_3752_: *mut LeanObject,
    mut v_x_3753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    v___f_3754_ = lean_alloc_closure(
        l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_3754_, 0, v_inst_3749_);
    lean_closure_set(v___f_3754_, 1, v_f_3752_);
    v___x_3755_ = lean_apply_3(v_inst_3750_, lean_box(0), v___f_3754_, v_x_3753_);
    return v___x_3755_;
}
pub unsafe fn l_Lean_instMonadWithOptionsOfMonadFunctor___redArg(
    mut v_inst_3756_: *mut LeanObject,
    mut v_inst_3757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3758_: *mut LeanObject = core::ptr::null_mut();
    v___f_3758_ = lean_alloc_closure(
        l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_3758_, 0, v_inst_3757_);
    lean_closure_set(v___f_3758_, 1, v_inst_3756_);
    return v___f_3758_;
}
pub unsafe fn l_Lean_instMonadWithOptionsOfMonadFunctor(
    mut v_m_3759_: *mut LeanObject,
    mut v_n_3760_: *mut LeanObject,
    mut v_inst_3761_: *mut LeanObject,
    mut v_inst_3762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3763_: *mut LeanObject = core::ptr::null_mut();
    v___f_3763_ = lean_alloc_closure(
        l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_3763_, 0, v_inst_3762_);
    lean_closure_set(v___f_3763_, 1, v_inst_3761_);
    return v___f_3763_;
}
pub unsafe fn l_Lean_withInPattern___redArg___lam__0(
    mut v___x_3767_: *mut LeanObject,
    mut v_o_3768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: u8 = 0;
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    v___x_3769_ = l_Lean_withInPattern___redArg___lam__0___closed__1;
    v___x_3770_ = 1;
    v___x_3771_ = lean_box((v___x_3770_) as usize);
    v___x_3772_ = l_Lean_Options_set___redArg(v___x_3767_, v_o_3768_, v___x_3769_, v___x_3771_);
    return v___x_3772_;
}
pub unsafe fn _init_l_Lean_withInPattern___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3774_: *mut LeanObject = core::ptr::null_mut();
    v___x_3773_ = l_Lean_KVMap_instValueBool;
    v___f_3774_ = lean_alloc_closure(
        l_Lean_withInPattern___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3774_, 0, v___x_3773_);
    return v___f_3774_;
}
pub unsafe fn l_Lean_withInPattern___redArg(
    mut v_inst_3775_: *mut LeanObject,
    mut v_x_3776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    v___f_3777_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_withInPattern___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_withInPattern___redArg___closed__0_once),
        _init_l_Lean_withInPattern___redArg___closed__0,
    );
    v___x_3778_ = lean_apply_3(v_inst_3775_, lean_box(0), v___f_3777_, v_x_3776_);
    return v___x_3778_;
}
pub unsafe fn l_Lean_withInPattern(
    mut v_m_3779_: *mut LeanObject,
    mut v_00_u03b1_3780_: *mut LeanObject,
    mut v_inst_3781_: *mut LeanObject,
    mut v_x_3782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    v___x_3783_ = l_Lean_withInPattern___redArg(v_inst_3781_, v_x_3782_);
    return v___x_3783_;
}
pub unsafe fn l_Lean_Options_getInPattern(mut v_o_3784_: *mut LeanObject) -> u8 {
    let mut v_map_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: u8 = 0;
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    v_map_3785_ = lean_ctor_get(v_o_3784_, 0);
    v___x_3786_ = l_Lean_withInPattern___redArg___lam__0___closed__1;
    v___x_3787_ = 0;
    v___x_3788_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3785_,
            v___x_3786_,
        );
    if lean_obj_tag(v___x_3788_) == 0 {
        return v___x_3787_;
    } else {
        let mut v_val_3789_: *mut LeanObject = core::ptr::null_mut();
        v_val_3789_ = lean_ctor_get(v___x_3788_, 0);
        lean_inc(v_val_3789_);
        lean_dec_ref_known(v___x_3788_, 1);
        if lean_obj_tag(v_val_3789_) == 1 {
            let mut v_v_3790_: u8 = 0;
            v_v_3790_ = lean_ctor_get_uint8(v_val_3789_, 0 as u32);
            lean_dec_ref_known(v_val_3789_, 0);
            return v_v_3790_;
        } else {
            lean_dec(v_val_3789_);
            return v___x_3787_;
        }
    }
}
pub unsafe fn l_Lean_Options_getInPattern___boxed(
    mut v_o_3791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3792_: u8 = 0;
    let mut v_r_3793_: *mut LeanObject = core::ptr::null_mut();
    v_res_3792_ = l_Lean_Options_getInPattern(v_o_3791_);
    lean_dec_ref(v_o_3791_);
    v_r_3793_ = lean_box((v_res_3792_) as usize);
    return v_r_3793_;
}
pub unsafe fn l_Lean_instInhabitedOption_default___redArg(
    mut v_inst_3794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    v___x_3795_ = lean_box(0);
    v___x_3796_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3796_, 0, v___x_3795_);
    lean_ctor_set(v___x_3796_, 1, v_inst_3794_);
    return v___x_3796_;
}
pub unsafe fn l_Lean_instInhabitedOption_default(
    mut v_00_u03b1_3797_: *mut LeanObject,
    mut v_inst_3798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    v___x_3799_ = l_Lean_instInhabitedOption_default___redArg(v_inst_3798_);
    return v___x_3799_;
}
pub unsafe fn l_Lean_instInhabitedOption___redArg(
    mut v_inst_3800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    v___x_3801_ = l_Lean_instInhabitedOption_default___redArg(v_inst_3800_);
    return v___x_3801_;
}
pub unsafe fn l_Lean_instInhabitedOption(
    mut v_a_3802_: *mut LeanObject,
    mut v_inst_3803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    v___x_3804_ = l_Lean_instInhabitedOption_default___redArg(v_inst_3803_);
    return v___x_3804_;
}
pub unsafe fn l_Lean_Option_get_x3f___redArg(
    mut v_inst_3805_: *mut LeanObject,
    mut v_opts_3806_: *mut LeanObject,
    mut v_opt_3807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofDataValue_x3f_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    v_name_3808_ = lean_ctor_get(v_opt_3807_, 0);
    v_map_3809_ = lean_ctor_get(v_opts_3806_, 0);
    v_ofDataValue_x3f_3810_ = lean_ctor_get(v_inst_3805_, 1);
    lean_inc_ref(v_ofDataValue_x3f_3810_);
    lean_dec_ref(v_inst_3805_);
    v___x_3811_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3809_,
            v_name_3808_,
        );
    if lean_obj_tag(v___x_3811_) == 0 {
        let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_ofDataValue_x3f_3810_);
        v___x_3812_ = lean_box(0);
        return v___x_3812_;
    } else {
        let mut v_val_3813_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
        v_val_3813_ = lean_ctor_get(v___x_3811_, 0);
        lean_inc(v_val_3813_);
        lean_dec_ref_known(v___x_3811_, 1);
        v___x_3814_ = lean_apply_1(v_ofDataValue_x3f_3810_, v_val_3813_);
        return v___x_3814_;
    }
}
pub unsafe fn l_Lean_Option_get_x3f___redArg___boxed(
    mut v_inst_3815_: *mut LeanObject,
    mut v_opts_3816_: *mut LeanObject,
    mut v_opt_3817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3818_: *mut LeanObject = core::ptr::null_mut();
    v_res_3818_ = l_Lean_Option_get_x3f___redArg(v_inst_3815_, v_opts_3816_, v_opt_3817_);
    lean_dec_ref(v_opt_3817_);
    lean_dec_ref(v_opts_3816_);
    return v_res_3818_;
}
pub unsafe fn l_Lean_Option_get_x3f(
    mut v_00_u03b1_3819_: *mut LeanObject,
    mut v_inst_3820_: *mut LeanObject,
    mut v_opts_3821_: *mut LeanObject,
    mut v_opt_3822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    v___x_3823_ = l_Lean_Option_get_x3f___redArg(v_inst_3820_, v_opts_3821_, v_opt_3822_);
    return v___x_3823_;
}
pub unsafe fn l_Lean_Option_get_x3f___boxed(
    mut v_00_u03b1_3824_: *mut LeanObject,
    mut v_inst_3825_: *mut LeanObject,
    mut v_opts_3826_: *mut LeanObject,
    mut v_opt_3827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3828_: *mut LeanObject = core::ptr::null_mut();
    v_res_3828_ = l_Lean_Option_get_x3f(v_00_u03b1_3824_, v_inst_3825_, v_opts_3826_, v_opt_3827_);
    lean_dec_ref(v_opt_3827_);
    lean_dec_ref(v_opts_3826_);
    return v_res_3828_;
}
pub unsafe fn l_Lean_Option_get___redArg(
    mut v_inst_3829_: *mut LeanObject,
    mut v_opts_3830_: *mut LeanObject,
    mut v_opt_3831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofDataValue_x3f_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    v_name_3832_ = lean_ctor_get(v_opt_3831_, 0);
    v_defValue_3833_ = lean_ctor_get(v_opt_3831_, 1);
    v_map_3834_ = lean_ctor_get(v_opts_3830_, 0);
    v_ofDataValue_x3f_3835_ = lean_ctor_get(v_inst_3829_, 1);
    lean_inc_ref(v_ofDataValue_x3f_3835_);
    lean_dec_ref(v_inst_3829_);
    v___x_3836_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3834_,
            v_name_3832_,
        );
    if lean_obj_tag(v___x_3836_) == 0 {
        lean_dec_ref(v_ofDataValue_x3f_3835_);
        lean_inc(v_defValue_3833_);
        return v_defValue_3833_;
    } else {
        let mut v_val_3837_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
        v_val_3837_ = lean_ctor_get(v___x_3836_, 0);
        lean_inc(v_val_3837_);
        lean_dec_ref_known(v___x_3836_, 1);
        v___x_3838_ = lean_apply_1(v_ofDataValue_x3f_3835_, v_val_3837_);
        if lean_obj_tag(v___x_3838_) == 0 {
            lean_inc(v_defValue_3833_);
            return v_defValue_3833_;
        } else {
            let mut v_val_3839_: *mut LeanObject = core::ptr::null_mut();
            v_val_3839_ = lean_ctor_get(v___x_3838_, 0);
            lean_inc(v_val_3839_);
            lean_dec_ref_known(v___x_3838_, 1);
            return v_val_3839_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___redArg___boxed(
    mut v_inst_3840_: *mut LeanObject,
    mut v_opts_3841_: *mut LeanObject,
    mut v_opt_3842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3843_: *mut LeanObject = core::ptr::null_mut();
    v_res_3843_ = l_Lean_Option_get___redArg(v_inst_3840_, v_opts_3841_, v_opt_3842_);
    lean_dec_ref(v_opt_3842_);
    lean_dec_ref(v_opts_3841_);
    return v_res_3843_;
}
pub unsafe fn l_Lean_Option_get(
    mut v_00_u03b1_3844_: *mut LeanObject,
    mut v_inst_3845_: *mut LeanObject,
    mut v_opts_3846_: *mut LeanObject,
    mut v_opt_3847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    v___x_3848_ = l_Lean_Option_get___redArg(v_inst_3845_, v_opts_3846_, v_opt_3847_);
    return v___x_3848_;
}
pub unsafe fn l_Lean_Option_get___boxed(
    mut v_00_u03b1_3849_: *mut LeanObject,
    mut v_inst_3850_: *mut LeanObject,
    mut v_opts_3851_: *mut LeanObject,
    mut v_opt_3852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3853_: *mut LeanObject = core::ptr::null_mut();
    v_res_3853_ = l_Lean_Option_get(v_00_u03b1_3849_, v_inst_3850_, v_opts_3851_, v_opt_3852_);
    lean_dec_ref(v_opt_3852_);
    lean_dec_ref(v_opts_3851_);
    return v_res_3853_;
}
pub unsafe fn lean_options_get_bool(
    mut v_opts_3854_: *mut LeanObject,
    mut v_name_3855_: *mut LeanObject,
    mut v_defValue_3856_: u8,
) -> u8 {
    let mut v_map_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    v_map_3857_ = lean_ctor_get(v_opts_3854_, 0);
    lean_inc(v_map_3857_);
    lean_dec_ref(v_opts_3854_);
    v___x_3858_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3857_,
            v_name_3855_,
        );
    lean_dec(v_name_3855_);
    lean_dec(v_map_3857_);
    if lean_obj_tag(v___x_3858_) == 0 {
        return v_defValue_3856_;
    } else {
        let mut v_val_3859_: *mut LeanObject = core::ptr::null_mut();
        v_val_3859_ = lean_ctor_get(v___x_3858_, 0);
        lean_inc(v_val_3859_);
        lean_dec_ref_known(v___x_3858_, 1);
        if lean_obj_tag(v_val_3859_) == 1 {
            let mut v_v_3860_: u8 = 0;
            v_v_3860_ = lean_ctor_get_uint8(v_val_3859_, 0 as u32);
            lean_dec_ref_known(v_val_3859_, 0);
            return v_v_3860_;
        } else {
            lean_dec(v_val_3859_);
            return v_defValue_3856_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_Options_0__Lean_Option_getBool___boxed(
    mut v_opts_3861_: *mut LeanObject,
    mut v_name_3862_: *mut LeanObject,
    mut v_defValue_3863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_boxed_3864_: u8 = 0;
    let mut v_res_3865_: u8 = 0;
    let mut v_r_3866_: *mut LeanObject = core::ptr::null_mut();
    v_defValue_boxed_3864_ = (lean_unbox(v_defValue_3863_) as u8);
    v_res_3865_ = lean_options_get_bool(v_opts_3861_, v_name_3862_, v_defValue_boxed_3864_);
    v_r_3866_ = lean_box((v_res_3865_) as usize);
    return v_r_3866_;
}
pub unsafe fn l_Lean_Option_getM___redArg___lam__0(
    mut v_inst_3867_: *mut LeanObject,
    mut v_opt_3868_: *mut LeanObject,
    mut v_toPure_3869_: *mut LeanObject,
    mut v_____do__lift_3870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    v___x_3871_ = l_Lean_Option_get___redArg(v_inst_3867_, v_____do__lift_3870_, v_opt_3868_);
    v___x_3872_ = lean_apply_2(v_toPure_3869_, lean_box(0), v___x_3871_);
    return v___x_3872_;
}
pub unsafe fn l_Lean_Option_getM___redArg___lam__0___boxed(
    mut v_inst_3873_: *mut LeanObject,
    mut v_opt_3874_: *mut LeanObject,
    mut v_toPure_3875_: *mut LeanObject,
    mut v_____do__lift_3876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3877_: *mut LeanObject = core::ptr::null_mut();
    v_res_3877_ = l_Lean_Option_getM___redArg___lam__0(
        v_inst_3873_,
        v_opt_3874_,
        v_toPure_3875_,
        v_____do__lift_3876_,
    );
    lean_dec_ref(v_____do__lift_3876_);
    lean_dec_ref(v_opt_3874_);
    return v_res_3877_;
}
pub unsafe fn l_Lean_Option_getM___redArg(
    mut v_inst_3878_: *mut LeanObject,
    mut v_inst_3879_: *mut LeanObject,
    mut v_inst_3880_: *mut LeanObject,
    mut v_opt_3881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3882_ = lean_ctor_get(v_inst_3878_, 0);
    lean_inc_ref(v_toApplicative_3882_);
    v_toBind_3883_ = lean_ctor_get(v_inst_3878_, 1);
    lean_inc(v_toBind_3883_);
    lean_dec_ref(v_inst_3878_);
    v_toPure_3884_ = lean_ctor_get(v_toApplicative_3882_, 1);
    lean_inc(v_toPure_3884_);
    lean_dec_ref(v_toApplicative_3882_);
    v___f_3885_ = lean_alloc_closure(
        l_Lean_Option_getM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3885_, 0, v_inst_3880_);
    lean_closure_set(v___f_3885_, 1, v_opt_3881_);
    lean_closure_set(v___f_3885_, 2, v_toPure_3884_);
    v___x_3886_ = lean_apply_4(
        v_toBind_3883_,
        lean_box(0),
        lean_box(0),
        v_inst_3879_,
        v___f_3885_,
    );
    return v___x_3886_;
}
pub unsafe fn l_Lean_Option_getM(
    mut v_m_3887_: *mut LeanObject,
    mut v_00_u03b1_3888_: *mut LeanObject,
    mut v_inst_3889_: *mut LeanObject,
    mut v_inst_3890_: *mut LeanObject,
    mut v_inst_3891_: *mut LeanObject,
    mut v_opt_3892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    v___x_3893_ =
        l_Lean_Option_getM___redArg(v_inst_3889_, v_inst_3890_, v_inst_3891_, v_opt_3892_);
    return v___x_3893_;
}
pub unsafe fn l_Lean_Option_set___redArg(
    mut v_inst_3894_: *mut LeanObject,
    mut v_opts_3895_: *mut LeanObject,
    mut v_opt_3896_: *mut LeanObject,
    mut v_val_3897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    v_name_3898_ = lean_ctor_get(v_opt_3896_, 0);
    lean_inc(v_name_3898_);
    lean_dec_ref(v_opt_3896_);
    v___x_3899_ =
        l_Lean_Options_set___redArg(v_inst_3894_, v_opts_3895_, v_name_3898_, v_val_3897_);
    return v___x_3899_;
}
pub unsafe fn l_Lean_Option_set(
    mut v_00_u03b1_3900_: *mut LeanObject,
    mut v_inst_3901_: *mut LeanObject,
    mut v_opts_3902_: *mut LeanObject,
    mut v_opt_3903_: *mut LeanObject,
    mut v_val_3904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    v___x_3905_ = l_Lean_Option_set___redArg(v_inst_3901_, v_opts_3902_, v_opt_3903_, v_val_3904_);
    return v___x_3905_;
}
pub unsafe fn l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(
    mut v_o_3906_: *mut LeanObject,
    mut v_k_3907_: *mut LeanObject,
    mut v_v_3908_: u8,
) -> *mut LeanObject {
    let mut v_map_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3910_: u8 = 0;
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3913_: u8 = 0;
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: u8 = 0;
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3924_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3909_ = lean_ctor_get(v_o_3906_, 0);
                v_hasTrace_3910_ = lean_ctor_get_uint8(
                    v_o_3906_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3924_ = (!lean_is_exclusive(v_o_3906_)) as u8;
                if v_isSharedCheck_3924_ == 0 {
                    v___x_3912_ = v_o_3906_;
                    v_isShared_3913_ = v_isSharedCheck_3924_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_3909_);
                    lean_dec(v_o_3906_);
                    v___x_3912_ = lean_box(0);
                    v_isShared_3913_ = v_isSharedCheck_3924_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3914_ = lean_alloc_ctor(1, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_3914_, 0 as u32, v_v_3908_);
                lean_inc(v_k_3907_);
                v___x_3915_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3907_, v___x_3914_, v_map_3909_);
                if v_hasTrace_3910_ == 0 {
                    v___x_3916_ = l_Lean_Options_insert___closed__1;
                    v___x_3917_ = l_Lean_Name_isPrefixOf(v___x_3916_, v_k_3907_);
                    lean_dec(v_k_3907_);
                    if v_isShared_3913_ == 0 {
                        lean_ctor_set(v___x_3912_, 0, v___x_3915_);
                        v___x_3919_ = v___x_3912_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3915_);
                        v___x_3919_ = v_reuseFailAlloc_3920_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_k_3907_);
                    if v_isShared_3913_ == 0 {
                        lean_ctor_set(v___x_3912_, 0, v___x_3915_);
                        v___x_3922_ = v___x_3912_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3915_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_3923_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v_hasTrace_3910_,
                        );
                        v___x_3922_ = v_reuseFailAlloc_3923_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_3919_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_o_3925_: *mut LeanObject,
    mut v_k_3926_: *mut LeanObject,
    mut v_v_3927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_3928_: u8 = 0;
    let mut v_res_3929_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_3928_ = (lean_unbox(v_v_3927_) as u8);
    v_res_3929_ =
        l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(
            v_o_3925_,
            v_k_3926_,
            v_v_boxed_3928_,
        );
    return v_res_3929_;
}
pub unsafe fn lean_options_update_bool(
    mut v_opts_3930_: *mut LeanObject,
    mut v_name_3931_: *mut LeanObject,
    mut v_val_3932_: u8,
) -> *mut LeanObject {
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    v___x_3933_ =
        l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(
            v_opts_3930_,
            v_name_3931_,
            v_val_3932_,
        );
    return v___x_3933_;
}
pub unsafe fn l___private_Lean_Data_Options_0__Lean_Option_updateBool___boxed(
    mut v_opts_3934_: *mut LeanObject,
    mut v_name_3935_: *mut LeanObject,
    mut v_val_3936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_boxed_3937_: u8 = 0;
    let mut v_res_3938_: *mut LeanObject = core::ptr::null_mut();
    v_val_boxed_3937_ = (lean_unbox(v_val_3936_) as u8);
    v_res_3938_ = lean_options_update_bool(v_opts_3934_, v_name_3935_, v_val_boxed_3937_);
    return v_res_3938_;
}
pub unsafe fn l_Lean_Option_setIfNotSet___redArg(
    mut v_inst_3939_: *mut LeanObject,
    mut v_opts_3940_: *mut LeanObject,
    mut v_opt_3941_: *mut LeanObject,
    mut v_val_3942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: u8 = 0;
    v_name_3943_ = lean_ctor_get(v_opt_3941_, 0);
    v_map_3944_ = lean_ctor_get(v_opts_3940_, 0);
    v___x_3945_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(
            v_name_3943_,
            v_map_3944_,
        );
    if v___x_3945_ == 0 {
        let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
        v___x_3946_ =
            l_Lean_Option_set___redArg(v_inst_3939_, v_opts_3940_, v_opt_3941_, v_val_3942_);
        return v___x_3946_;
    } else {
        lean_dec(v_val_3942_);
        lean_dec_ref(v_opt_3941_);
        lean_dec_ref(v_inst_3939_);
        return v_opts_3940_;
    }
}
pub unsafe fn l_Lean_Option_setIfNotSet(
    mut v_00_u03b1_3947_: *mut LeanObject,
    mut v_inst_3948_: *mut LeanObject,
    mut v_opts_3949_: *mut LeanObject,
    mut v_opt_3950_: *mut LeanObject,
    mut v_val_3951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    v___x_3952_ =
        l_Lean_Option_setIfNotSet___redArg(v_inst_3948_, v_opts_3949_, v_opt_3950_, v_val_3951_);
    return v___x_3952_;
}
pub unsafe fn _init_l_Lean_Option_register___auto__1() -> *mut LeanObject {
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    v___x_3953_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__28),
        core::ptr::addr_of_mut!(l_Lean_OptionDecl_declName___autoParam___closed__28_once),
        _init_l_Lean_OptionDecl_declName___autoParam___closed__28,
    );
    return v___x_3953_;
}
pub unsafe fn l_Lean_Option_register___redArg(
    mut v_inst_3954_: *mut LeanObject,
    mut v_name_3955_: *mut LeanObject,
    mut v_decl_3956_: *mut LeanObject,
    mut v_ref_3957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toDataValue_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3962_: u8 = 0;
    let mut v_defValue_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3971_: u8 = 0;
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3978_: u8 = 0;
    let mut v_unused_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3983_: u8 = 0;
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3987_: u8 = 0;
    let mut v_isSharedCheck_3988_: u8 = 0;
    let mut v_unused_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toDataValue_3959_ = lean_ctor_get(v_inst_3954_, 0);
                v_isSharedCheck_3988_ = (!lean_is_exclusive(v_inst_3954_)) as u8;
                if v_isSharedCheck_3988_ == 0 {
                    v_unused_3989_ = lean_ctor_get(v_inst_3954_, 1);
                    lean_dec(v_unused_3989_);
                    v___x_3961_ = v_inst_3954_;
                    v_isShared_3962_ = v_isSharedCheck_3988_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toDataValue_3959_);
                    lean_dec(v_inst_3954_);
                    v___x_3961_ = lean_box(0);
                    v_isShared_3962_ = v_isSharedCheck_3988_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_defValue_3963_ = lean_ctor_get(v_decl_3956_, 0);
                lean_inc_n(v_defValue_3963_, 2);
                v_descr_3964_ = lean_ctor_get(v_decl_3956_, 1);
                lean_inc_ref(v_descr_3964_);
                v_deprecation_x3f_3965_ = lean_ctor_get(v_decl_3956_, 2);
                lean_inc(v_deprecation_x3f_3965_);
                lean_dec_ref(v_decl_3956_);
                v___x_3966_ = lean_apply_1(v_toDataValue_3959_, v_defValue_3963_);
                lean_inc_n(v_name_3955_, 2);
                v___x_3967_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_3967_, 0, v_name_3955_);
                lean_ctor_set(v___x_3967_, 1, v_ref_3957_);
                lean_ctor_set(v___x_3967_, 2, v___x_3966_);
                lean_ctor_set(v___x_3967_, 3, v_descr_3964_);
                lean_ctor_set(v___x_3967_, 4, v_deprecation_x3f_3965_);
                v___x_3968_ = lean_register_option(v_name_3955_, v___x_3967_);
                if lean_obj_tag(v___x_3968_) == 0 {
                    v_isSharedCheck_3978_ = (!lean_is_exclusive(v___x_3968_)) as u8;
                    if v_isSharedCheck_3978_ == 0 {
                        v_unused_3979_ = lean_ctor_get(v___x_3968_, 0);
                        lean_dec(v_unused_3979_);
                        v___x_3970_ = v___x_3968_;
                        v_isShared_3971_ = v_isSharedCheck_3978_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_3968_);
                        v___x_3970_ = lean_box(0);
                        v_isShared_3971_ = v_isSharedCheck_3978_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_defValue_3963_);
                    lean_del_object(v___x_3961_);
                    lean_dec(v_name_3955_);
                    v_a_3980_ = lean_ctor_get(v___x_3968_, 0);
                    v_isSharedCheck_3987_ = (!lean_is_exclusive(v___x_3968_)) as u8;
                    if v_isSharedCheck_3987_ == 0 {
                        v___x_3982_ = v___x_3968_;
                        v_isShared_3983_ = v_isSharedCheck_3987_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3980_);
                        lean_dec(v___x_3968_);
                        v___x_3982_ = lean_box(0);
                        v_isShared_3983_ = v_isSharedCheck_3987_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3962_ == 0 {
                    lean_ctor_set(v___x_3961_, 1, v_defValue_3963_);
                    lean_ctor_set(v___x_3961_, 0, v_name_3955_);
                    v___x_3973_ = v___x_3961_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_name_3955_);
                    lean_ctor_set(v_reuseFailAlloc_3977_, 1, v_defValue_3963_);
                    v___x_3973_ = v_reuseFailAlloc_3977_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3971_ == 0 {
                    lean_ctor_set(v___x_3970_, 0, v___x_3973_);
                    v___x_3975_ = v___x_3970_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3976_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3973_);
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
                    v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
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
    mut v_inst_3990_: *mut LeanObject,
    mut v_name_3991_: *mut LeanObject,
    mut v_decl_3992_: *mut LeanObject,
    mut v_ref_3993_: *mut LeanObject,
    mut v_a_3994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3995_: *mut LeanObject = core::ptr::null_mut();
    v_res_3995_ =
        l_Lean_Option_register___redArg(v_inst_3990_, v_name_3991_, v_decl_3992_, v_ref_3993_);
    return v_res_3995_;
}
pub unsafe fn l_Lean_Option_register(
    mut v_00_u03b1_3996_: *mut LeanObject,
    mut v_inst_3997_: *mut LeanObject,
    mut v_name_3998_: *mut LeanObject,
    mut v_decl_3999_: *mut LeanObject,
    mut v_ref_4000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    v___x_4002_ =
        l_Lean_Option_register___redArg(v_inst_3997_, v_name_3998_, v_decl_3999_, v_ref_4000_);
    return v___x_4002_;
}
pub unsafe fn l_Lean_Option_register___boxed(
    mut v_00_u03b1_4003_: *mut LeanObject,
    mut v_inst_4004_: *mut LeanObject,
    mut v_name_4005_: *mut LeanObject,
    mut v_decl_4006_: *mut LeanObject,
    mut v_ref_4007_: *mut LeanObject,
    mut v_a_4008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4009_: *mut LeanObject = core::ptr::null_mut();
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
-> *mut LeanObject {
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    v___x_4097_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__5;
    v___x_4098_ = l_String_toRawSubstring_x27(v___x_4097_);
    return v___x_4098_;
}
pub unsafe fn _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17()
-> *mut LeanObject {
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    v___x_4118_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__16;
    v___x_4119_ = l_String_toRawSubstring_x27(v___x_4118_);
    return v___x_4119_;
}
pub unsafe fn _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29()
-> *mut LeanObject {
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    v___x_4146_ = l_Array_mkArray0(lean_box(0));
    return v___x_4146_;
}
pub unsafe fn l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(
    mut v_x_4147_: *mut LeanObject,
    mut v_a_4148_: *mut LeanObject,
    mut v_a_4149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: u8 = 0;
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4199_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_val_4241_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___y_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: u8 = 0;
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4295_: u8 = 0;
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4299_: u8 = 0;
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4305_: u8 = 0;
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4150_ = l_Lean_OptionDecl_declName___autoParam___closed__0;
                v___x_4151_ = l_Lean_Option_registerBuiltinOption___closed__2;
                lean_inc(v_x_4147_);
                v___x_4152_ = l_Lean_Syntax_isOfKind(v_x_4147_, v___x_4151_);
                if v___x_4152_ == 0 {
                    lean_dec(v_x_4147_);
                    v___x_4153_ = lean_box(1);
                    v___x_4154_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4154_, 0, v___x_4153_);
                    lean_ctor_set(v___x_4154_, 1, v_a_4149_);
                    return v___x_4154_;
                } else {
                    v___x_4155_ = lean_unsigned_to_nat(0);
                    v___x_4156_ = l_Lean_Syntax_getArg(v_x_4147_, v___x_4155_);
                    v___x_4157_ = lean_unsigned_to_nat(1);
                    v___x_4158_ = l_Lean_Syntax_getArg(v_x_4147_, v___x_4157_);
                    v___x_4159_ = lean_unsigned_to_nat(3);
                    v_name_4160_ = l_Lean_Syntax_getArg(v_x_4147_, v___x_4159_);
                    v___x_4161_ = lean_unsigned_to_nat(5);
                    v___x_4162_ = l_Lean_Syntax_getArg(v_x_4147_, v___x_4161_);
                    v___x_4163_ = lean_unsigned_to_nat(7);
                    v___x_4164_ = l_Lean_Syntax_getArg(v_x_4147_, v___x_4163_);
                    lean_dec(v_x_4147_);
                    v___x_4300_ = l_Lean_Syntax_getOptional_x3f(v___x_4158_);
                    lean_dec(v___x_4158_);
                    if lean_obj_tag(v___x_4300_) == 0 {
                        v___x_4301_ = lean_box(0);
                        v___y_4289_ = v___x_4301_;
                        state = 5;
                        continue;
                    } else {
                        v_val_4302_ = lean_ctor_get(v___x_4300_, 0);
                        v_isSharedCheck_4309_ = (!lean_is_exclusive(v___x_4300_)) as u8;
                        if v_isSharedCheck_4309_ == 0 {
                            v___x_4304_ = v___x_4300_;
                            v_isShared_4305_ = v_isSharedCheck_4309_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_val_4302_);
                            lean_dec(v___x_4300_);
                            v___x_4304_ = lean_box(0);
                            v_isShared_4305_ = v_isSharedCheck_4309_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc_n(v___y_4170_, 2);
                lean_inc_n(v___y_4174_, 6);
                v___x_4179_ =
                    l_Lean_Syntax_node2(v___y_4174_, v___y_4170_, v___y_4178_, v___x_4164_);
                v___x_4180_ =
                    l_Lean_Syntax_node2(v___y_4174_, v___y_4169_, v___y_4166_, v___x_4179_);
                v___x_4181_ = l_Lean_Syntax_node1(v___y_4174_, v___y_4176_, v___x_4180_);
                v___x_4182_ =
                    l_Lean_Syntax_node2(v___y_4174_, v___y_4175_, v___x_4181_, v___y_4168_);
                v___x_4183_ = l_Lean_Syntax_node1(v___y_4174_, v___y_4170_, v___x_4182_);
                v___x_4184_ = l_Lean_Syntax_node1(v___y_4174_, v___y_4177_, v___x_4183_);
                lean_inc(v___y_4173_);
                v___x_4185_ = l_Lean_Syntax_node4(
                    v___y_4174_,
                    v___y_4173_,
                    v___y_4171_,
                    v___y_4172_,
                    v___y_4167_,
                    v___x_4184_,
                );
                v___x_4186_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4186_, 0, v___x_4185_);
                lean_ctor_set(v___x_4186_, 1, v_a_4149_);
                return v___x_4186_;
            }
            2 => {
                lean_inc_ref(v___y_4192_);
                v___x_4200_ = l_Array_append___redArg(v___y_4192_, v___y_4199_);
                lean_dec_ref(v___y_4199_);
                lean_inc_n(v___y_4190_, 3);
                lean_inc_n(v___y_4196_, 12);
                v___x_4201_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4201_, 0, v___y_4196_);
                lean_ctor_set(v___x_4201_, 1, v___y_4190_);
                lean_ctor_set(v___x_4201_, 2, v___x_4200_);
                lean_inc_n(v___y_4189_, 5);
                lean_inc(v___y_4195_);
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
                lean_inc_ref(v___y_4188_);
                lean_inc_ref_n(v___y_4194_, 6);
                v___x_4204_ =
                    l_Lean_Name_mkStr4(v___x_4150_, v___y_4194_, v___y_4188_, v___x_4203_);
                v___x_4205_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1;
                v___x_4206_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4206_, 0, v___y_4196_);
                lean_ctor_set(v___x_4206_, 1, v___x_4205_);
                v___x_4207_ = l_Lean_Syntax_node1(v___y_4196_, v___x_4204_, v___x_4206_);
                v___x_4208_ = l_Lean_OptionDecl_declName___autoParam___closed__14;
                v___x_4209_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2;
                v___x_4210_ =
                    l_Lean_Name_mkStr4(v___x_4150_, v___y_4194_, v___x_4208_, v___x_4209_);
                v___x_4211_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3;
                v___x_4212_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4212_, 0, v___y_4196_);
                lean_ctor_set(v___x_4212_, 1, v___x_4211_);
                v___x_4213_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4;
                v___x_4214_ =
                    l_Lean_Name_mkStr4(v___x_4150_, v___y_4194_, v___x_4208_, v___x_4213_);
                v___x_4215_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6), core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once), _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
                v___x_4216_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7;
                lean_inc_n(v___y_4191_, 2);
                lean_inc_n(v___y_4197_, 2);
                v___x_4217_ = l_Lean_addMacroScope(v___y_4197_, v___x_4216_, v___y_4191_);
                v___x_4218_ = lean_box(0);
                v___x_4219_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11;
                v___x_4220_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4220_, 0, v___y_4196_);
                lean_ctor_set(v___x_4220_, 1, v___x_4215_);
                lean_ctor_set(v___x_4220_, 2, v___x_4217_);
                lean_ctor_set(v___x_4220_, 3, v___x_4219_);
                v___x_4221_ = l_Lean_Syntax_node1(v___y_4196_, v___y_4190_, v___x_4162_);
                lean_inc(v___x_4214_);
                v___x_4222_ =
                    l_Lean_Syntax_node2(v___y_4196_, v___x_4214_, v___x_4220_, v___x_4221_);
                v___x_4223_ =
                    l_Lean_Syntax_node2(v___y_4196_, v___x_4210_, v___x_4212_, v___x_4222_);
                v___x_4224_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12;
                v___x_4225_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4225_, 0, v___y_4196_);
                lean_ctor_set(v___x_4225_, 1, v___x_4224_);
                lean_inc(v_name_4160_);
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
                v___x_4233_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17), core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once), _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
                v___x_4234_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19;
                v___x_4235_ = l_Lean_addMacroScope(v___y_4197_, v___x_4234_, v___y_4191_);
                v___x_4236_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21;
                v___x_4237_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4237_, 0, v___y_4196_);
                lean_ctor_set(v___x_4237_, 1, v___x_4233_);
                lean_ctor_set(v___x_4237_, 2, v___x_4235_);
                lean_ctor_set(v___x_4237_, 3, v___x_4236_);
                v___x_4238_ = l_Lean_TSyntax_getId(v_name_4160_);
                lean_dec(v_name_4160_);
                lean_inc(v___x_4238_);
                v___x_4239_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                    v___x_4218_,
                    v___x_4238_,
                );
                if lean_obj_tag(v___x_4239_) == 0 {
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
                    lean_dec(v___x_4238_);
                    v_val_4241_ = lean_ctor_get(v___x_4239_, 0);
                    lean_inc(v_val_4241_);
                    lean_dec_ref_known(v___x_4239_, 1);
                    v___x_4242_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22;
                    lean_inc_ref(v___y_4194_);
                    v___x_4243_ =
                        l_Lean_Name_mkStr4(v___x_4150_, v___y_4194_, v___x_4208_, v___x_4242_);
                    v___x_4244_ = l_Lean_getOptionDecl___closed__1;
                    v___x_4245_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23;
                    v___x_4246_ = lean_string_intercalate(v___x_4245_, v_val_4241_);
                    v___x_4247_ = lean_string_append(v___x_4244_, v___x_4246_);
                    lean_dec_ref(v___x_4246_);
                    v___x_4248_ = lean_box(2);
                    v___x_4249_ = l_Lean_Syntax_mkNameLit(v___x_4247_, v___x_4248_);
                    v___x_4250_ = lean_mk_empty_array_with_capacity(v___x_4157_);
                    v___x_4251_ = lean_array_push(v___x_4250_, v___x_4249_);
                    v___x_4252_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_4252_, 0, v___x_4248_);
                    lean_ctor_set(v___x_4252_, 1, v___x_4243_);
                    lean_ctor_set(v___x_4252_, 2, v___x_4251_);
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
                lean_inc_ref_n(v___y_4258_, 2);
                v___x_4265_ = l_Array_append___redArg(v___y_4258_, v___y_4264_);
                lean_dec_ref(v___y_4264_);
                lean_inc_n(v___y_4255_, 2);
                lean_inc_n(v___y_4262_, 2);
                v___x_4266_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4266_, 0, v___y_4262_);
                lean_ctor_set(v___x_4266_, 1, v___y_4255_);
                lean_ctor_set(v___x_4266_, 2, v___x_4265_);
                v___x_4267_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4267_, 0, v___y_4262_);
                lean_ctor_set(v___x_4267_, 1, v___y_4255_);
                lean_ctor_set(v___x_4267_, 2, v___y_4258_);
                if lean_obj_tag(v___y_4256_) == 1 {
                    v_val_4268_ = lean_ctor_get(v___y_4256_, 0);
                    lean_inc(v_val_4268_);
                    lean_dec_ref_known(v___y_4256_, 1);
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
                    lean_dec(v___y_4256_);
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
                v_quotContext_4274_ = lean_ctor_get(v_a_4148_, 1);
                v_currMacroScope_4275_ = lean_ctor_get(v_a_4148_, 2);
                v_ref_4276_ = lean_ctor_get(v_a_4148_, 5);
                v___x_4277_ = 0;
                v___x_4278_ = l_Lean_SourceInfo_fromRef(v_ref_4276_, v___x_4277_);
                v___x_4279_ = l_Lean_OptionDecl_declName___autoParam___closed__1;
                v___x_4280_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24;
                v___x_4281_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26;
                v___x_4282_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28;
                v___x_4283_ = l_Lean_OptionDecl_declName___autoParam___closed__9;
                v___x_4284_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29), core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once), _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29);
                if lean_obj_tag(v___y_4273_) == 1 {
                    v_val_4285_ = lean_ctor_get(v___y_4273_, 0);
                    lean_inc(v_val_4285_);
                    lean_dec_ref_known(v___y_4273_, 1);
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
                    lean_dec(v___y_4273_);
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
                lean_dec(v___x_4156_);
                if lean_obj_tag(v___x_4290_) == 0 {
                    v___x_4291_ = lean_box(0);
                    v___y_4272_ = v___y_4289_;
                    v___y_4273_ = v___x_4291_;
                    state = 4;
                    continue;
                } else {
                    v_val_4292_ = lean_ctor_get(v___x_4290_, 0);
                    v_isSharedCheck_4299_ = (!lean_is_exclusive(v___x_4290_)) as u8;
                    if v_isSharedCheck_4299_ == 0 {
                        v___x_4294_ = v___x_4290_;
                        v_isShared_4295_ = v_isSharedCheck_4299_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_val_4292_);
                        lean_dec(v___x_4290_);
                        v___x_4294_ = lean_box(0);
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
                    v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_val_4292_);
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
                    v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_val_4302_);
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
    mut v_x_4310_: *mut LeanObject,
    mut v_a_4311_: *mut LeanObject,
    mut v_a_4312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4313_: *mut LeanObject = core::ptr::null_mut();
    v_res_4313_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(v_x_4310_, v_a_4311_, v_a_4312_);
    lean_dec_ref(v_a_4311_);
    return v_res_4313_;
}
pub unsafe fn l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(
    mut v_x_4390_: *mut LeanObject,
    mut v_a_4391_: *mut LeanObject,
    mut v_a_4392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: u8 = 0;
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: u8 = 0;
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___y_4441_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_val_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4393_ = l_Lean_Option_registerOption___closed__1;
                lean_inc(v_x_4390_);
                v___x_4394_ = l_Lean_Syntax_isOfKind(v_x_4390_, v___x_4393_);
                if v___x_4394_ == 0 {
                    lean_dec(v_x_4390_);
                    v___x_4395_ = lean_box(1);
                    v___x_4396_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4396_, 0, v___x_4395_);
                    lean_ctor_set(v___x_4396_, 1, v_a_4392_);
                    return v___x_4396_;
                } else {
                    v_quotContext_4397_ = lean_ctor_get(v_a_4391_, 1);
                    v_currMacroScope_4398_ = lean_ctor_get(v_a_4391_, 2);
                    v_ref_4399_ = lean_ctor_get(v_a_4391_, 5);
                    v___x_4400_ = lean_unsigned_to_nat(0);
                    v___x_4401_ = l_Lean_Syntax_getArg(v_x_4390_, v___x_4400_);
                    v___x_4402_ = lean_unsigned_to_nat(2);
                    v_name_4403_ = l_Lean_Syntax_getArg(v_x_4390_, v___x_4402_);
                    v___x_4404_ = lean_unsigned_to_nat(4);
                    v___x_4405_ = l_Lean_Syntax_getArg(v_x_4390_, v___x_4404_);
                    v___x_4406_ = lean_unsigned_to_nat(6);
                    v___x_4407_ = l_Lean_Syntax_getArg(v_x_4390_, v___x_4406_);
                    lean_dec(v_x_4390_);
                    v___x_4408_ = 0;
                    v___x_4409_ = l_Lean_SourceInfo_fromRef(v_ref_4399_, v___x_4408_);
                    v___x_4410_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25;
                    v___x_4411_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26;
                    v___x_4412_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0;
                    lean_inc_n(v___x_4409_, 10);
                    v___x_4413_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4413_, 0, v___x_4409_);
                    lean_ctor_set(v___x_4413_, 1, v___x_4410_);
                    v___x_4414_ = l_Lean_Syntax_node1(v___x_4409_, v___x_4412_, v___x_4413_);
                    v___x_4415_ = l_Lean_OptionDecl_declName___autoParam___closed__9;
                    v___x_4416_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1;
                    v___x_4417_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3;
                    v___x_4418_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4418_, 0, v___x_4409_);
                    lean_ctor_set(v___x_4418_, 1, v___x_4417_);
                    v___x_4419_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2;
                    v___x_4420_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6), core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once), _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
                    v___x_4421_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7;
                    lean_inc_n(v_currMacroScope_4398_, 2);
                    lean_inc_n(v_quotContext_4397_, 2);
                    v___x_4422_ = l_Lean_addMacroScope(
                        v_quotContext_4397_,
                        v___x_4421_,
                        v_currMacroScope_4398_,
                    );
                    v___x_4423_ = lean_box(0);
                    v___x_4424_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11;
                    v___x_4425_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_4425_, 0, v___x_4409_);
                    lean_ctor_set(v___x_4425_, 1, v___x_4420_);
                    lean_ctor_set(v___x_4425_, 2, v___x_4422_);
                    lean_ctor_set(v___x_4425_, 3, v___x_4424_);
                    v___x_4426_ = l_Lean_Syntax_node1(v___x_4409_, v___x_4415_, v___x_4405_);
                    v___x_4427_ =
                        l_Lean_Syntax_node2(v___x_4409_, v___x_4419_, v___x_4425_, v___x_4426_);
                    v___x_4428_ =
                        l_Lean_Syntax_node2(v___x_4409_, v___x_4416_, v___x_4418_, v___x_4427_);
                    v___x_4429_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12;
                    v___x_4430_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4430_, 0, v___x_4409_);
                    lean_ctor_set(v___x_4430_, 1, v___x_4429_);
                    lean_inc(v_name_4403_);
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
                    v___x_4435_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17), core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once), _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
                    v___x_4436_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19;
                    v___x_4437_ = l_Lean_addMacroScope(
                        v_quotContext_4397_,
                        v___x_4436_,
                        v_currMacroScope_4398_,
                    );
                    v___x_4438_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21;
                    v___x_4439_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_4439_, 0, v___x_4409_);
                    lean_ctor_set(v___x_4439_, 1, v___x_4435_);
                    lean_ctor_set(v___x_4439_, 2, v___x_4437_);
                    lean_ctor_set(v___x_4439_, 3, v___x_4438_);
                    v___x_4452_ = l_Lean_TSyntax_getId(v_name_4403_);
                    lean_dec(v_name_4403_);
                    lean_inc(v___x_4452_);
                    v___x_4453_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                        v___x_4423_,
                        v___x_4452_,
                    );
                    if lean_obj_tag(v___x_4453_) == 0 {
                        v___x_4454_ = l_Lean_quoteNameMk(v___x_4452_);
                        v___y_4441_ = v___x_4454_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_4452_);
                        v_val_4455_ = lean_ctor_get(v___x_4453_, 0);
                        lean_inc(v_val_4455_);
                        lean_dec_ref_known(v___x_4453_, 1);
                        v___x_4456_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6;
                        v___x_4457_ = l_Lean_getOptionDecl___closed__1;
                        v___x_4458_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23;
                        v___x_4459_ = lean_string_intercalate(v___x_4458_, v_val_4455_);
                        v___x_4460_ = lean_string_append(v___x_4457_, v___x_4459_);
                        lean_dec_ref(v___x_4459_);
                        v___x_4461_ = lean_box(2);
                        v___x_4462_ = l_Lean_Syntax_mkNameLit(v___x_4460_, v___x_4461_);
                        v___x_4463_ = lean_unsigned_to_nat(1);
                        v___x_4464_ = lean_mk_empty_array_with_capacity(v___x_4463_);
                        v___x_4465_ = lean_array_push(v___x_4464_, v___x_4462_);
                        v___x_4466_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_4466_, 0, v___x_4461_);
                        lean_ctor_set(v___x_4466_, 1, v___x_4456_);
                        lean_ctor_set(v___x_4466_, 2, v___x_4465_);
                        v___y_4441_ = v___x_4466_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_n(v___x_4409_, 7);
                v___x_4442_ =
                    l_Lean_Syntax_node2(v___x_4409_, v___x_4415_, v___y_4441_, v___x_4407_);
                v___x_4443_ =
                    l_Lean_Syntax_node2(v___x_4409_, v___x_4419_, v___x_4439_, v___x_4442_);
                v___x_4444_ = l_Lean_Syntax_node1(v___x_4409_, v___x_4434_, v___x_4443_);
                v___x_4445_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29), core::ptr::addr_of_mut!(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once), _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29);
                v___x_4446_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4446_, 0, v___x_4409_);
                lean_ctor_set(v___x_4446_, 1, v___x_4415_);
                lean_ctor_set(v___x_4446_, 2, v___x_4445_);
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
                v___x_4451_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4451_, 0, v___x_4450_);
                lean_ctor_set(v___x_4451_, 1, v_a_4392_);
                return v___x_4451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___boxed(
    mut v_x_4467_: *mut LeanObject,
    mut v_a_4468_: *mut LeanObject,
    mut v_a_4469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4470_: *mut LeanObject = core::ptr::null_mut();
    v_res_4470_ =
        l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(
            v_x_4467_, v_a_4468_, v_a_4469_,
        );
    lean_dec_ref(v_a_4468_);
    return v_res_4470_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Options(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_ImportingFlag(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_KVMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_instInhabitedOptionDecl_default = _init_l_Lean_instInhabitedOptionDecl_default();
    lean_mark_persistent(l_Lean_instInhabitedOptionDecl_default);
    l_Lean_instInhabitedOptionDecl = _init_l_Lean_instInhabitedOptionDecl();
    lean_mark_persistent(l_Lean_instInhabitedOptionDecl);
    l_Lean_instInhabitedOptionDecls = _init_l_Lean_instInhabitedOptionDecls();
    lean_mark_persistent(l_Lean_instInhabitedOptionDecls);
    res = l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Data_Options_0__Lean_optionDeclsRef = lean_io_result_get_value(res);
    lean_mark_persistent(l___private_Lean_Data_Options_0__Lean_optionDeclsRef);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Options(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_OptionDecl_declName___autoParam = _init_l_Lean_OptionDecl_declName___autoParam();
    lean_mark_persistent(l_Lean_OptionDecl_declName___autoParam);
    l_Lean_Option_register___auto__1 = _init_l_Lean_Option_register___auto__1();
    lean_mark_persistent(l_Lean_Option_register___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Options(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_ImportingFlag(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_KVMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_NameMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_Options(builtin);
}
