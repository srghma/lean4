// Lean compiler output
// Module: Lake.Config.OutFormat
// Imports: Lean.Setup Init.Data.String.TakeDrop
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map,
};
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_Pos_prevn;
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Prelude::l_List_foldl___redArg;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Setup::{initialize_Lean_Setup, runtime_initialize_Lean_Setup};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_extract;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_mk, lean_nat_dec_le, lean_nat_dec_lt,
    lean_string_utf8_byte_size, lean_usize_dec_eq,
};
pub static l_Lake_listToLines___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [10, 0],
};
static mut l_Lake_listToLines___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_listToLines___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_listToLines___redArg___closed__0_value: crate::leanh::LeanStringObject<1> =
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
static mut l_Lake_listToLines___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_listToLines___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_arrayToLines___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_arrayToLines___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_arrayToLines___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_arrayToLines___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_arrayToLines___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_arrayToLines___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_arrayToLines___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_arrayToLines___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_arrayToLines___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_arrayToLines___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_arrayToLines___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_arrayToLines___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_arrayToLines___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_arrayToLines___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_arrayToLines___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_arrayToLines___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_arrayToLines___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_arrayToLines___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_arrayToLines___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_arrayToLines___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_arrayToLines___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTextJson___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_compress as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToTextJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTextJson___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToTextJson: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTextJson___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instQueryText___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instQueryText___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instQueryText___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instQueryText___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instQueryTextUnit___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instQueryTextUnit___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instQueryTextUnit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instQueryTextUnit___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instQueryTextUnit: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instQueryTextUnit___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instQueryJson___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instQueryJson___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instQueryJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instQueryJson___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instQueryJsonUnit___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instQueryJsonUnit___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instQueryJsonUnit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instQueryJsonUnit___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instQueryJsonUnit: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instQueryJsonUnit___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_nullFormat___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_nullFormat___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_ppImport___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [105, 109, 112, 111, 114, 116, 32, 0],
    };
static mut l_Lake_ppImport___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ppImport___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ppImport___closed__1_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [97, 108, 108, 32, 0],
    };
static mut l_Lake_ppImport___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ppImport___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ppImport___closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [109, 101, 116, 97, 32, 0],
    };
static mut l_Lake_ppImport___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ppImport___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ppImport___closed__3_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [112, 117, 98, 108, 105, 99, 32, 0],
    };
static mut l_Lake_ppImport___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ppImport___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ppModuleHeader___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [112, 114, 101, 108, 117, 100, 101, 0],
    };
static mut l_Lake_ppModuleHeader___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ppModuleHeader___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ppModuleHeader___closed__1_value: crate::leanh::LeanStringObject<15> =
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
            109, 111, 100, 117, 108, 101, 32, 112, 114, 101, 108, 117, 100, 101, 0,
        ],
    };
static mut l_Lake_ppModuleHeader___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ppModuleHeader___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Config_OutFormat_0__Lake_instQueryTextModuleHeader___closed__0_value:
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
    m_fun: l_Lake_ppModuleHeader___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Config_OutFormat_0__Lake_instQueryTextModuleHeader___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_OutFormat_0__Lake_instQueryTextModuleHeader___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lake_Config_OutFormat_0__Lake_instQueryTextModuleHeader:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_OutFormat_0__Lake_instQueryTextModuleHeader___closed__0_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_OutFormat_ctorIdx(mut v_x_418_: u8) -> *mut crate::leanh::LeanObject {
    if v_x_418_ == 0 {
        let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_419_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_419_;
    } else {
        let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_420_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_420_;
    }
}
pub unsafe fn l_Lake_OutFormat_ctorIdx___boxed(
    mut v_x_421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_422_: u8 = 0;
    let mut v_res_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_422_ = (crate::leanh::lean_unbox(v_x_421_) as u8);
    v_res_423_ = l_Lake_OutFormat_ctorIdx(v_x_boxed_422_);
    return v_res_423_;
}
pub unsafe fn l_Lake_OutFormat_toCtorIdx(mut v_x_424_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_425_ = l_Lake_OutFormat_ctorIdx(v_x_424_);
    return v___x_425_;
}
pub unsafe fn l_Lake_OutFormat_toCtorIdx___boxed(
    mut v_x_426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_427_: u8 = 0;
    let mut v_res_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_427_ = (crate::leanh::lean_unbox(v_x_426_) as u8);
    v_res_428_ = l_Lake_OutFormat_toCtorIdx(v_x_4__boxed_427_);
    return v_res_428_;
}
pub unsafe fn l_Lake_OutFormat_ctorElim___redArg(
    mut v_k_429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_429_);
    return v_k_429_;
}
pub unsafe fn l_Lake_OutFormat_ctorElim___redArg___boxed(
    mut v_k_430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_431_ = l_Lake_OutFormat_ctorElim___redArg(v_k_430_);
    crate::leanh::lean_dec(v_k_430_);
    return v_res_431_;
}
pub unsafe fn l_Lake_OutFormat_ctorElim(
    mut v_motive_432_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_433_: *mut crate::leanh::LeanObject,
    mut v_t_434_: u8,
    mut v_h_435_: *mut crate::leanh::LeanObject,
    mut v_k_436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_436_);
    return v_k_436_;
}
pub unsafe fn l_Lake_OutFormat_ctorElim___boxed(
    mut v_motive_437_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_438_: *mut crate::leanh::LeanObject,
    mut v_t_439_: *mut crate::leanh::LeanObject,
    mut v_h_440_: *mut crate::leanh::LeanObject,
    mut v_k_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_442_: u8 = 0;
    let mut v_res_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_442_ = (crate::leanh::lean_unbox(v_t_439_) as u8);
    v_res_443_ = l_Lake_OutFormat_ctorElim(
        v_motive_437_,
        v_ctorIdx_438_,
        v_t_boxed_442_,
        v_h_440_,
        v_k_441_,
    );
    crate::leanh::lean_dec(v_k_441_);
    crate::leanh::lean_dec(v_ctorIdx_438_);
    return v_res_443_;
}
pub unsafe fn l_Lake_OutFormat_text_elim___redArg(
    mut v_text_444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_text_444_);
    return v_text_444_;
}
pub unsafe fn l_Lake_OutFormat_text_elim___redArg___boxed(
    mut v_text_445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_446_ = l_Lake_OutFormat_text_elim___redArg(v_text_445_);
    crate::leanh::lean_dec(v_text_445_);
    return v_res_446_;
}
pub unsafe fn l_Lake_OutFormat_text_elim(
    mut v_motive_447_: *mut crate::leanh::LeanObject,
    mut v_t_448_: u8,
    mut v_h_449_: *mut crate::leanh::LeanObject,
    mut v_text_450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_text_450_);
    return v_text_450_;
}
pub unsafe fn l_Lake_OutFormat_text_elim___boxed(
    mut v_motive_451_: *mut crate::leanh::LeanObject,
    mut v_t_452_: *mut crate::leanh::LeanObject,
    mut v_h_453_: *mut crate::leanh::LeanObject,
    mut v_text_454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_455_: u8 = 0;
    let mut v_res_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_455_ = (crate::leanh::lean_unbox(v_t_452_) as u8);
    v_res_456_ = l_Lake_OutFormat_text_elim(v_motive_451_, v_t_boxed_455_, v_h_453_, v_text_454_);
    crate::leanh::lean_dec(v_text_454_);
    return v_res_456_;
}
pub unsafe fn l_Lake_OutFormat_json_elim___redArg(
    mut v_json_457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_json_457_);
    return v_json_457_;
}
pub unsafe fn l_Lake_OutFormat_json_elim___redArg___boxed(
    mut v_json_458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_459_ = l_Lake_OutFormat_json_elim___redArg(v_json_458_);
    crate::leanh::lean_dec(v_json_458_);
    return v_res_459_;
}
pub unsafe fn l_Lake_OutFormat_json_elim(
    mut v_motive_460_: *mut crate::leanh::LeanObject,
    mut v_t_461_: u8,
    mut v_h_462_: *mut crate::leanh::LeanObject,
    mut v_json_463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_json_463_);
    return v_json_463_;
}
pub unsafe fn l_Lake_OutFormat_json_elim___boxed(
    mut v_motive_464_: *mut crate::leanh::LeanObject,
    mut v_t_465_: *mut crate::leanh::LeanObject,
    mut v_h_466_: *mut crate::leanh::LeanObject,
    mut v_json_467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_468_: u8 = 0;
    let mut v_res_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_468_ = (crate::leanh::lean_unbox(v_t_465_) as u8);
    v_res_469_ = l_Lake_OutFormat_json_elim(v_motive_464_, v_t_boxed_468_, v_h_466_, v_json_467_);
    crate::leanh::lean_dec(v_json_467_);
    return v_res_469_;
}
pub unsafe fn l_Lake_instToTextOfToString___redArg(
    mut v_inst_470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_470_);
    return v_inst_470_;
}
pub unsafe fn l_Lake_instToTextOfToString___redArg___boxed(
    mut v_inst_471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_472_ = l_Lake_instToTextOfToString___redArg(v_inst_471_);
    crate::leanh::lean_dec_ref(v_inst_471_);
    return v_res_472_;
}
pub unsafe fn l_Lake_instToTextOfToString(
    mut v_00_u03b1_473_: *mut crate::leanh::LeanObject,
    mut v_inst_474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_474_);
    return v_inst_474_;
}
pub unsafe fn l_Lake_instToTextOfToString___boxed(
    mut v_00_u03b1_475_: *mut crate::leanh::LeanObject,
    mut v_inst_476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_477_ = l_Lake_instToTextOfToString(v_00_u03b1_475_, v_inst_476_);
    crate::leanh::lean_dec_ref(v_inst_476_);
    return v_res_477_;
}
pub unsafe fn l_Lake_listToLines___redArg___lam__0(
    mut v_f_479_: *mut crate::leanh::LeanObject,
    mut v_x1_480_: *mut crate::leanh::LeanObject,
    mut v_x2_481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_482_ = crate::leanh::lean_apply_1(v_f_479_, v_x2_481_);
    v___x_483_ = lean_string_append(v_x1_480_, v___x_482_);
    crate::leanh::lean_dec_ref(v___x_482_);
    v___x_484_ = l_Lake_listToLines___redArg___lam__0___closed__0;
    v___x_485_ = lean_string_append(v___x_483_, v___x_484_);
    return v___x_485_;
}
pub unsafe fn l_Lake_listToLines___redArg(
    mut v_as_487_: *mut crate::leanh::LeanObject,
    mut v_f_488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_489_ = crate::leanh::lean_alloc_closure(
        l_Lake_listToLines___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_489_, 0, v_f_488_);
    v___x_490_ = l_Lake_listToLines___redArg___closed__0;
    v___x_491_ = l_List_foldl___redArg(v___f_489_, v___x_490_, v_as_487_);
    v___x_492_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_493_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_494_ = lean_string_utf8_byte_size(v___x_491_);
    crate::leanh::lean_inc(v___x_491_);
    v___x_495_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_495_, 0, v___x_491_);
    crate::leanh::lean_ctor_set(v___x_495_, 1, v___x_493_);
    crate::leanh::lean_ctor_set(v___x_495_, 2, v___x_494_);
    v___x_496_ = l_String_Slice_Pos_prevn(v___x_495_, v___x_494_, v___x_492_);
    crate::leanh::lean_dec_ref_known(v___x_495_, 3);
    v___x_497_ = lean_string_utf8_extract(v___x_491_, v___x_493_, v___x_496_);
    crate::leanh::lean_dec(v___x_496_);
    crate::leanh::lean_dec(v___x_491_);
    return v___x_497_;
}
pub unsafe fn l_Lake_listToLines(
    mut v_00_u03b1_498_: *mut crate::leanh::LeanObject,
    mut v_as_499_: *mut crate::leanh::LeanObject,
    mut v_f_500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_501_ = crate::leanh::lean_alloc_closure(
        l_Lake_listToLines___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_501_, 0, v_f_500_);
    v___x_502_ = l_Lake_listToLines___redArg___closed__0;
    v___x_503_ = l_List_foldl___redArg(v___f_501_, v___x_502_, v_as_499_);
    v___x_504_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_505_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_506_ = lean_string_utf8_byte_size(v___x_503_);
    crate::leanh::lean_inc(v___x_503_);
    v___x_507_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_507_, 0, v___x_503_);
    crate::leanh::lean_ctor_set(v___x_507_, 1, v___x_505_);
    crate::leanh::lean_ctor_set(v___x_507_, 2, v___x_506_);
    v___x_508_ = l_String_Slice_Pos_prevn(v___x_507_, v___x_506_, v___x_504_);
    crate::leanh::lean_dec_ref_known(v___x_507_, 3);
    v___x_509_ = lean_string_utf8_extract(v___x_503_, v___x_505_, v___x_508_);
    crate::leanh::lean_dec(v___x_508_);
    crate::leanh::lean_dec(v___x_503_);
    return v___x_509_;
}
pub unsafe fn l_Lake_arrayToLines___redArg(
    mut v_as_529_: *mut crate::leanh::LeanObject,
    mut v_f_530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: u8 = 0;
    let mut v___f_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: u8 = 0;
    let mut v___x_546_: usize = 0;
    let mut v___x_547_: usize = 0;
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: usize = 0;
    let mut v___x_550_: usize = 0;
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_539_ = l_Lake_listToLines___redArg___closed__0;
                v___x_540_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_541_ = lean_array_get_size(v_as_529_);
                v___x_542_ = l_Lake_arrayToLines___redArg___closed__9;
                v___x_543_ = lean_nat_dec_lt(v___x_540_, v___x_541_);
                if v___x_543_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_530_);
                    crate::leanh::lean_dec_ref(v_as_529_);
                    v___y_532_ = v___x_539_;
                    state = 1;
                    continue;
                } else {
                    v___f_544_ = crate::leanh::lean_alloc_closure(
                        l_Lake_listToLines___redArg___lam__0 as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_544_, 0, v_f_530_);
                    v___x_545_ = lean_nat_dec_le(v___x_541_, v___x_541_);
                    if v___x_545_ == 0 {
                        if v___x_543_ == 0 {
                            crate::leanh::lean_dec_ref(v___f_544_);
                            crate::leanh::lean_dec_ref(v_as_529_);
                            v___y_532_ = v___x_539_;
                            state = 1;
                            continue;
                        } else {
                            v___x_546_ = 0usize;
                            v___x_547_ = lean_usize_of_nat(v___x_541_);
                            v___x_548_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_542_,
                                    v___f_544_,
                                    v_as_529_,
                                    v___x_546_,
                                    v___x_547_,
                                    v___x_539_,
                                );
                            v___y_532_ = v___x_548_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_549_ = 0usize;
                        v___x_550_ = lean_usize_of_nat(v___x_541_);
                        v___x_551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_542_,
                            v___f_544_,
                            v_as_529_,
                            v___x_549_,
                            v___x_550_,
                            v___x_539_,
                        );
                        v___y_532_ = v___x_551_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_533_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_534_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_535_ = lean_string_utf8_byte_size(v___y_532_);
                crate::leanh::lean_inc_ref(v___y_532_);
                v___x_536_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_536_, 0, v___y_532_);
                crate::leanh::lean_ctor_set(v___x_536_, 1, v___x_534_);
                crate::leanh::lean_ctor_set(v___x_536_, 2, v___x_535_);
                v___x_537_ = l_String_Slice_Pos_prevn(v___x_536_, v___x_535_, v___x_533_);
                crate::leanh::lean_dec_ref_known(v___x_536_, 3);
                v___x_538_ = lean_string_utf8_extract(v___y_532_, v___x_534_, v___x_537_);
                crate::leanh::lean_dec(v___x_537_);
                crate::leanh::lean_dec_ref(v___y_532_);
                return v___x_538_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_arrayToLines(
    mut v_00_u03b1_552_: *mut crate::leanh::LeanObject,
    mut v_as_553_: *mut crate::leanh::LeanObject,
    mut v_f_554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: u8 = 0;
    let mut v___f_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: u8 = 0;
    let mut v___x_570_: usize = 0;
    let mut v___x_571_: usize = 0;
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: usize = 0;
    let mut v___x_574_: usize = 0;
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_563_ = l_Lake_listToLines___redArg___closed__0;
                v___x_564_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_565_ = lean_array_get_size(v_as_553_);
                v___x_566_ = l_Lake_arrayToLines___redArg___closed__9;
                v___x_567_ = lean_nat_dec_lt(v___x_564_, v___x_565_);
                if v___x_567_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_554_);
                    crate::leanh::lean_dec_ref(v_as_553_);
                    v___y_556_ = v___x_563_;
                    state = 1;
                    continue;
                } else {
                    v___f_568_ = crate::leanh::lean_alloc_closure(
                        l_Lake_listToLines___redArg___lam__0 as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_568_, 0, v_f_554_);
                    v___x_569_ = lean_nat_dec_le(v___x_565_, v___x_565_);
                    if v___x_569_ == 0 {
                        if v___x_567_ == 0 {
                            crate::leanh::lean_dec_ref(v___f_568_);
                            crate::leanh::lean_dec_ref(v_as_553_);
                            v___y_556_ = v___x_563_;
                            state = 1;
                            continue;
                        } else {
                            v___x_570_ = 0usize;
                            v___x_571_ = lean_usize_of_nat(v___x_565_);
                            v___x_572_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_566_,
                                    v___f_568_,
                                    v_as_553_,
                                    v___x_570_,
                                    v___x_571_,
                                    v___x_563_,
                                );
                            v___y_556_ = v___x_572_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_573_ = 0usize;
                        v___x_574_ = lean_usize_of_nat(v___x_565_);
                        v___x_575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_566_,
                            v___f_568_,
                            v_as_553_,
                            v___x_573_,
                            v___x_574_,
                            v___x_563_,
                        );
                        v___y_556_ = v___x_575_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_557_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_558_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_559_ = lean_string_utf8_byte_size(v___y_556_);
                crate::leanh::lean_inc_ref(v___y_556_);
                v___x_560_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_560_, 0, v___y_556_);
                crate::leanh::lean_ctor_set(v___x_560_, 1, v___x_558_);
                crate::leanh::lean_ctor_set(v___x_560_, 2, v___x_559_);
                v___x_561_ = l_String_Slice_Pos_prevn(v___x_560_, v___x_559_, v___x_557_);
                crate::leanh::lean_dec_ref_known(v___x_560_, 3);
                v___x_562_ = lean_string_utf8_extract(v___y_556_, v___x_558_, v___x_561_);
                crate::leanh::lean_dec(v___x_561_);
                crate::leanh::lean_dec_ref(v___y_556_);
                return v___x_562_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instToTextList___redArg___lam__0(
    mut v_inst_578_: *mut crate::leanh::LeanObject,
    mut v_x1_579_: *mut crate::leanh::LeanObject,
    mut v_x2_580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_581_ = crate::leanh::lean_apply_1(v_inst_578_, v_x2_580_);
    v___x_582_ = lean_string_append(v_x1_579_, v___x_581_);
    crate::leanh::lean_dec_ref(v___x_581_);
    v___x_583_ = l_Lake_listToLines___redArg___lam__0___closed__0;
    v___x_584_ = lean_string_append(v___x_582_, v___x_583_);
    return v___x_584_;
}
pub unsafe fn l_Lake_instToTextList___redArg___lam__1(
    mut v___f_585_: *mut crate::leanh::LeanObject,
    mut v_x_586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_587_ = l_Lake_listToLines___redArg___closed__0;
    v___x_588_ = l_List_foldl___redArg(v___f_585_, v___x_587_, v_x_586_);
    v___x_589_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_590_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_591_ = lean_string_utf8_byte_size(v___x_588_);
    crate::leanh::lean_inc(v___x_588_);
    v___x_592_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_592_, 0, v___x_588_);
    crate::leanh::lean_ctor_set(v___x_592_, 1, v___x_590_);
    crate::leanh::lean_ctor_set(v___x_592_, 2, v___x_591_);
    v___x_593_ = l_String_Slice_Pos_prevn(v___x_592_, v___x_591_, v___x_589_);
    crate::leanh::lean_dec_ref_known(v___x_592_, 3);
    v___x_594_ = lean_string_utf8_extract(v___x_588_, v___x_590_, v___x_593_);
    crate::leanh::lean_dec(v___x_593_);
    crate::leanh::lean_dec(v___x_588_);
    return v___x_594_;
}
pub unsafe fn l_Lake_instToTextList___redArg(
    mut v_inst_595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_596_ = crate::leanh::lean_alloc_closure(
        l_Lake_instToTextList___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_596_, 0, v_inst_595_);
    v___f_597_ = crate::leanh::lean_alloc_closure(
        l_Lake_instToTextList___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_597_, 0, v___f_596_);
    return v___f_597_;
}
pub unsafe fn l_Lake_instToTextList(
    mut v_00_u03b1_598_: *mut crate::leanh::LeanObject,
    mut v_inst_599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_600_ = l_Lake_instToTextList___redArg(v_inst_599_);
    return v___x_600_;
}
pub unsafe fn l_Lake_instToTextArray___redArg___lam__1(
    mut v___f_601_: *mut crate::leanh::LeanObject,
    mut v_x_602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: u8 = 0;
    let mut v___x_616_: u8 = 0;
    let mut v___x_617_: usize = 0;
    let mut v___x_618_: usize = 0;
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: usize = 0;
    let mut v___x_621_: usize = 0;
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_611_ = l_Lake_listToLines___redArg___closed__0;
                v___x_612_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_613_ = lean_array_get_size(v_x_602_);
                v___x_614_ = l_Lake_arrayToLines___redArg___closed__9;
                v___x_615_ = lean_nat_dec_lt(v___x_612_, v___x_613_);
                if v___x_615_ == 0 {
                    crate::leanh::lean_dec_ref(v_x_602_);
                    crate::leanh::lean_dec_ref(v___f_601_);
                    v___y_604_ = v___x_611_;
                    state = 1;
                    continue;
                } else {
                    v___x_616_ = lean_nat_dec_le(v___x_613_, v___x_613_);
                    if v___x_616_ == 0 {
                        if v___x_615_ == 0 {
                            crate::leanh::lean_dec_ref(v_x_602_);
                            crate::leanh::lean_dec_ref(v___f_601_);
                            v___y_604_ = v___x_611_;
                            state = 1;
                            continue;
                        } else {
                            v___x_617_ = 0usize;
                            v___x_618_ = lean_usize_of_nat(v___x_613_);
                            v___x_619_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_614_,
                                    v___f_601_,
                                    v_x_602_,
                                    v___x_617_,
                                    v___x_618_,
                                    v___x_611_,
                                );
                            v___y_604_ = v___x_619_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_620_ = 0usize;
                        v___x_621_ = lean_usize_of_nat(v___x_613_);
                        v___x_622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_614_,
                            v___f_601_,
                            v_x_602_,
                            v___x_620_,
                            v___x_621_,
                            v___x_611_,
                        );
                        v___y_604_ = v___x_622_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_605_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_606_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_607_ = lean_string_utf8_byte_size(v___y_604_);
                crate::leanh::lean_inc_ref(v___y_604_);
                v___x_608_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_608_, 0, v___y_604_);
                crate::leanh::lean_ctor_set(v___x_608_, 1, v___x_606_);
                crate::leanh::lean_ctor_set(v___x_608_, 2, v___x_607_);
                v___x_609_ = l_String_Slice_Pos_prevn(v___x_608_, v___x_607_, v___x_605_);
                crate::leanh::lean_dec_ref_known(v___x_608_, 3);
                v___x_610_ = lean_string_utf8_extract(v___y_604_, v___x_606_, v___x_609_);
                crate::leanh::lean_dec(v___x_609_);
                crate::leanh::lean_dec_ref(v___y_604_);
                return v___x_610_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instToTextArray___redArg(
    mut v_inst_623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_624_ = crate::leanh::lean_alloc_closure(
        l_Lake_instToTextList___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_624_, 0, v_inst_623_);
    v___f_625_ = crate::leanh::lean_alloc_closure(
        l_Lake_instToTextArray___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_625_, 0, v___f_624_);
    return v___f_625_;
}
pub unsafe fn l_Lake_instToTextArray(
    mut v_00_u03b1_626_: *mut crate::leanh::LeanObject,
    mut v_inst_627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_628_ = l_Lake_instToTextArray___redArg(v_inst_627_);
    return v___x_628_;
}
pub unsafe fn l_Lake_instQueryText___lam__0(
    mut v_x_629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_630_ = l_Lake_listToLines___redArg___closed__0;
    return v___x_630_;
}
pub unsafe fn l_Lake_instQueryText___lam__0___boxed(
    mut v_x_631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_632_ = l_Lake_instQueryText___lam__0(v_x_631_);
    crate::leanh::lean_dec(v_x_631_);
    return v_res_632_;
}
pub unsafe fn l_Lake_instQueryText(
    mut v_00_u03b1_634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_635_ = l_Lake_instQueryText___closed__0;
    return v___f_635_;
}
pub unsafe fn l_Lake_instQueryTextOfToText___redArg(
    mut v_inst_636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_636_);
    return v_inst_636_;
}
pub unsafe fn l_Lake_instQueryTextOfToText___redArg___boxed(
    mut v_inst_637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_638_ = l_Lake_instQueryTextOfToText___redArg(v_inst_637_);
    crate::leanh::lean_dec_ref(v_inst_637_);
    return v_res_638_;
}
pub unsafe fn l_Lake_instQueryTextOfToText(
    mut v_00_u03b1_639_: *mut crate::leanh::LeanObject,
    mut v_inst_640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_640_);
    return v_inst_640_;
}
pub unsafe fn l_Lake_instQueryTextOfToText___boxed(
    mut v_00_u03b1_641_: *mut crate::leanh::LeanObject,
    mut v_inst_642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_643_ = l_Lake_instQueryTextOfToText(v_00_u03b1_641_, v_inst_642_);
    crate::leanh::lean_dec_ref(v_inst_642_);
    return v_res_643_;
}
pub unsafe fn l_Lake_instQueryTextList___redArg(
    mut v_inst_644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_645_ = crate::leanh::lean_alloc_closure(
        l_Lake_instToTextList___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_645_, 0, v_inst_644_);
    v___f_646_ = crate::leanh::lean_alloc_closure(
        l_Lake_instToTextList___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_646_, 0, v___f_645_);
    return v___f_646_;
}
pub unsafe fn l_Lake_instQueryTextList(
    mut v_00_u03b1_647_: *mut crate::leanh::LeanObject,
    mut v_inst_648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_649_ = l_Lake_instQueryTextList___redArg(v_inst_648_);
    return v___x_649_;
}
pub unsafe fn l_Lake_instQueryTextArray___redArg(
    mut v_inst_650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_651_ = crate::leanh::lean_alloc_closure(
        l_Lake_instToTextList___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_651_, 0, v_inst_650_);
    v___f_652_ = crate::leanh::lean_alloc_closure(
        l_Lake_instToTextArray___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_652_, 0, v___f_651_);
    return v___f_652_;
}
pub unsafe fn l_Lake_instQueryTextArray(
    mut v_00_u03b1_653_: *mut crate::leanh::LeanObject,
    mut v_inst_654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_655_ = l_Lake_instQueryTextArray___redArg(v_inst_654_);
    return v___x_655_;
}
pub unsafe fn l_Lake_instQueryTextUnit___lam__0(
    mut v_x_656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_657_ = l_Lake_listToLines___redArg___closed__0;
    return v___x_657_;
}
pub unsafe fn l_Lake_instQueryJson___lam__0(
    mut v_x_660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_661_ = crate::leanh::lean_box(0);
    return v___x_661_;
}
pub unsafe fn l_Lake_instQueryJson___lam__0___boxed(
    mut v_x_662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_663_ = l_Lake_instQueryJson___lam__0(v_x_662_);
    crate::leanh::lean_dec(v_x_662_);
    return v_res_663_;
}
pub unsafe fn l_Lake_instQueryJson(
    mut v_00_u03b1_665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_666_ = l_Lake_instQueryJson___closed__0;
    return v___f_666_;
}
pub unsafe fn l_Lake_instQueryJsonOfToJson___redArg(
    mut v_inst_667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_667_);
    return v_inst_667_;
}
pub unsafe fn l_Lake_instQueryJsonOfToJson___redArg___boxed(
    mut v_inst_668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_669_ = l_Lake_instQueryJsonOfToJson___redArg(v_inst_668_);
    crate::leanh::lean_dec_ref(v_inst_668_);
    return v_res_669_;
}
pub unsafe fn l_Lake_instQueryJsonOfToJson(
    mut v_00_u03b1_670_: *mut crate::leanh::LeanObject,
    mut v_inst_671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_671_);
    return v_inst_671_;
}
pub unsafe fn l_Lake_instQueryJsonOfToJson___boxed(
    mut v_00_u03b1_672_: *mut crate::leanh::LeanObject,
    mut v_inst_673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_674_ = l_Lake_instQueryJsonOfToJson(v_00_u03b1_672_, v_inst_673_);
    crate::leanh::lean_dec_ref(v_inst_673_);
    return v_res_674_;
}
pub unsafe fn l_Lake_instQueryJsonList___redArg___lam__0(
    mut v_inst_675_: *mut crate::leanh::LeanObject,
    mut v_x_676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_677_ = crate::leanh::lean_apply_1(v_inst_675_, v_x_676_);
    return v___x_677_;
}
pub unsafe fn l_Lake_instQueryJsonList___redArg___lam__1(
    mut v___f_678_: *mut crate::leanh::LeanObject,
    mut v_x_679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_682_: usize = 0;
    let mut v___x_683_: usize = 0;
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_680_ = lean_array_mk(v_x_679_);
    v___x_681_ = l_Lake_arrayToLines___redArg___closed__9;
    v_sz_682_ = lean_array_size(v___x_680_);
    v___x_683_ = 0usize;
    v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_681_,
        v___f_678_,
        v_sz_682_,
        v___x_683_,
        v___x_680_,
    );
    v___x_685_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_685_, 0, v___x_684_);
    return v___x_685_;
}
pub unsafe fn l_Lake_instQueryJsonList___redArg(
    mut v_inst_686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_687_ = crate::leanh::lean_alloc_closure(
        l_Lake_instQueryJsonList___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_687_, 0, v_inst_686_);
    v___f_688_ = crate::leanh::lean_alloc_closure(
        l_Lake_instQueryJsonList___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_688_, 0, v___f_687_);
    return v___f_688_;
}
pub unsafe fn l_Lake_instQueryJsonList(
    mut v_00_u03b1_689_: *mut crate::leanh::LeanObject,
    mut v_inst_690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_691_ = l_Lake_instQueryJsonList___redArg(v_inst_690_);
    return v___x_691_;
}
pub unsafe fn l_Lake_instQueryJsonArray___redArg___lam__1(
    mut v___f_692_: *mut crate::leanh::LeanObject,
    mut v_x_693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_695_: usize = 0;
    let mut v___x_696_: usize = 0;
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_694_ = l_Lake_arrayToLines___redArg___closed__9;
    v_sz_695_ = lean_array_size(v_x_693_);
    v___x_696_ = 0usize;
    v___x_697_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_694_,
        v___f_692_,
        v_sz_695_,
        v___x_696_,
        v_x_693_,
    );
    v___x_698_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_698_, 0, v___x_697_);
    return v___x_698_;
}
pub unsafe fn l_Lake_instQueryJsonArray___redArg(
    mut v_inst_699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_700_ = crate::leanh::lean_alloc_closure(
        l_Lake_instQueryJsonList___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_700_, 0, v_inst_699_);
    v___f_701_ = crate::leanh::lean_alloc_closure(
        l_Lake_instQueryJsonArray___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_701_, 0, v___f_700_);
    return v___f_701_;
}
pub unsafe fn l_Lake_instQueryJsonArray(
    mut v_00_u03b1_702_: *mut crate::leanh::LeanObject,
    mut v_inst_703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_704_ = l_Lake_instQueryJsonArray___redArg(v_inst_703_);
    return v___x_704_;
}
pub unsafe fn l_Lake_instQueryJsonUnit___lam__0(
    mut v_x_705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_706_ = crate::leanh::lean_box(0);
    return v___x_706_;
}
pub unsafe fn l_Lake_instFormatQueryOfQueryTextOfQueryJson___redArg(
    mut v_inst_709_: *mut crate::leanh::LeanObject,
    mut v_inst_710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_711_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_711_, 0, v_inst_709_);
    crate::leanh::lean_ctor_set(v___x_711_, 1, v_inst_710_);
    return v___x_711_;
}
pub unsafe fn l_Lake_instFormatQueryOfQueryTextOfQueryJson(
    mut v_00_u03b1_712_: *mut crate::leanh::LeanObject,
    mut v_inst_713_: *mut crate::leanh::LeanObject,
    mut v_inst_714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_715_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_715_, 0, v_inst_713_);
    crate::leanh::lean_ctor_set(v___x_715_, 1, v_inst_714_);
    return v___x_715_;
}
pub unsafe fn _init_l_Lake_nullFormat___redArg___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_716_ = crate::leanh::lean_box(0);
    v___x_717_ = l_Lean_Json_compress(v___x_716_);
    return v___x_717_;
}
pub unsafe fn l_Lake_nullFormat___redArg(mut v_fmt_718_: u8) -> *mut crate::leanh::LeanObject {
    if v_fmt_718_ == 0 {
        let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_719_ = l_Lake_listToLines___redArg___closed__0;
        return v___x_719_;
    } else {
        let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_720_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lake_nullFormat___redArg___closed__0),
            core::ptr::addr_of_mut!(l_Lake_nullFormat___redArg___closed__0_once),
            _init_l_Lake_nullFormat___redArg___closed__0,
        );
        return v___x_720_;
    }
}
pub unsafe fn l_Lake_nullFormat___redArg___boxed(
    mut v_fmt_721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fmt_boxed_722_: u8 = 0;
    let mut v_res_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fmt_boxed_722_ = (crate::leanh::lean_unbox(v_fmt_721_) as u8);
    v_res_723_ = l_Lake_nullFormat___redArg(v_fmt_boxed_722_);
    return v_res_723_;
}
pub unsafe fn l_Lake_nullFormat(
    mut v_00_u03b1_724_: *mut crate::leanh::LeanObject,
    mut v_fmt_725_: u8,
    mut v_x_726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_727_ = l_Lake_nullFormat___redArg(v_fmt_725_);
    return v___x_727_;
}
pub unsafe fn l_Lake_nullFormat___boxed(
    mut v_00_u03b1_728_: *mut crate::leanh::LeanObject,
    mut v_fmt_729_: *mut crate::leanh::LeanObject,
    mut v_x_730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fmt_boxed_731_: u8 = 0;
    let mut v_res_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fmt_boxed_731_ = (crate::leanh::lean_unbox(v_fmt_729_) as u8);
    v_res_732_ = l_Lake_nullFormat(v_00_u03b1_728_, v_fmt_boxed_731_, v_x_730_);
    crate::leanh::lean_dec(v_x_730_);
    return v_res_732_;
}
pub unsafe fn l_Lake_formatQuery___redArg(
    mut v_inst_733_: *mut crate::leanh::LeanObject,
    mut v_fmt_734_: u8,
    mut v_a_735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_fmt_734_ == 0 {
        let mut v_toQueryText_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toQueryText_736_ = crate::leanh::lean_ctor_get(v_inst_733_, 0);
        crate::leanh::lean_inc_ref(v_toQueryText_736_);
        crate::leanh::lean_dec_ref(v_inst_733_);
        v___x_737_ = crate::leanh::lean_apply_1(v_toQueryText_736_, v_a_735_);
        return v___x_737_;
    } else {
        let mut v_toQueryJson_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toQueryJson_738_ = crate::leanh::lean_ctor_get(v_inst_733_, 1);
        crate::leanh::lean_inc_ref(v_toQueryJson_738_);
        crate::leanh::lean_dec_ref(v_inst_733_);
        v___x_739_ = crate::leanh::lean_apply_1(v_toQueryJson_738_, v_a_735_);
        v___x_740_ = l_Lean_Json_compress(v___x_739_);
        return v___x_740_;
    }
}
pub unsafe fn l_Lake_formatQuery___redArg___boxed(
    mut v_inst_741_: *mut crate::leanh::LeanObject,
    mut v_fmt_742_: *mut crate::leanh::LeanObject,
    mut v_a_743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fmt_boxed_744_: u8 = 0;
    let mut v_res_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fmt_boxed_744_ = (crate::leanh::lean_unbox(v_fmt_742_) as u8);
    v_res_745_ = l_Lake_formatQuery___redArg(v_inst_741_, v_fmt_boxed_744_, v_a_743_);
    return v_res_745_;
}
pub unsafe fn l_Lake_formatQuery(
    mut v_00_u03b1_746_: *mut crate::leanh::LeanObject,
    mut v_inst_747_: *mut crate::leanh::LeanObject,
    mut v_fmt_748_: u8,
    mut v_a_749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_750_ = l_Lake_formatQuery___redArg(v_inst_747_, v_fmt_748_, v_a_749_);
    return v___x_750_;
}
pub unsafe fn l_Lake_formatQuery___boxed(
    mut v_00_u03b1_751_: *mut crate::leanh::LeanObject,
    mut v_inst_752_: *mut crate::leanh::LeanObject,
    mut v_fmt_753_: *mut crate::leanh::LeanObject,
    mut v_a_754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fmt_boxed_755_: u8 = 0;
    let mut v_res_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fmt_boxed_755_ = (crate::leanh::lean_unbox(v_fmt_753_) as u8);
    v_res_756_ = l_Lake_formatQuery(v_00_u03b1_751_, v_inst_752_, v_fmt_boxed_755_, v_a_754_);
    return v_res_756_;
}
pub unsafe fn l_Lake_ppImport(
    mut v_imp_761_: *mut crate::leanh::LeanObject,
    mut v_isModule_762_: u8,
    mut v_init_763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: u8 = 0;
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_importAll_772_: u8 = 0;
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isMeta_779_: u8 = 0;
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExported_782_: u8 = 0;
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_isModule_762_ == 0 {
                    v_s_778_ = v_init_763_;
                    state = 3;
                    continue;
                } else {
                    v_isExported_782_ = crate::leanh::lean_ctor_get_uint8(
                        v_imp_761_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    );
                    if v_isExported_782_ == 0 {
                        v_s_778_ = v_init_763_;
                        state = 3;
                        continue;
                    } else {
                        v___x_783_ = l_Lake_ppImport___closed__3;
                        v_s_784_ = lean_string_append(v_init_763_, v___x_783_);
                        v_s_778_ = v_s_784_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_module_766_ = crate::leanh::lean_ctor_get(v_imp_761_, 0);
                crate::leanh::lean_inc(v_module_766_);
                crate::leanh::lean_dec_ref(v_imp_761_);
                v___x_767_ = 1;
                v___x_768_ = l_Lean_Name_toString(v_module_766_, v___x_767_);
                v_s_769_ = lean_string_append(v_s_765_, v___x_768_);
                crate::leanh::lean_dec_ref(v___x_768_);
                return v_s_769_;
            }
            2 => {
                v_importAll_772_ = crate::leanh::lean_ctor_get_uint8(
                    v_imp_761_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_773_ = l_Lake_ppImport___closed__0;
                v_s_774_ = lean_string_append(v_s_771_, v___x_773_);
                if v_importAll_772_ == 0 {
                    v_s_765_ = v_s_774_;
                    state = 1;
                    continue;
                } else {
                    v___x_775_ = l_Lake_ppImport___closed__1;
                    v_s_776_ = lean_string_append(v_s_774_, v___x_775_);
                    v_s_765_ = v_s_776_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_isMeta_779_ = crate::leanh::lean_ctor_get_uint8(
                    v_imp_761_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 2) as u32,
                );
                if v_isMeta_779_ == 0 {
                    v_s_771_ = v_s_778_;
                    state = 2;
                    continue;
                } else {
                    v___x_780_ = l_Lake_ppImport___closed__2;
                    v_s_781_ = lean_string_append(v_s_778_, v___x_780_);
                    v_s_771_ = v_s_781_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ppImport___boxed(
    mut v_imp_785_: *mut crate::leanh::LeanObject,
    mut v_isModule_786_: *mut crate::leanh::LeanObject,
    mut v_init_787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isModule_boxed_788_: u8 = 0;
    let mut v_res_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isModule_boxed_788_ = (crate::leanh::lean_unbox(v_isModule_786_) as u8);
    v_res_789_ = l_Lake_ppImport(v_imp_785_, v_isModule_boxed_788_, v_init_787_);
    return v_res_789_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0(
    mut v_isModule_790_: u8,
    mut v_as_791_: *mut crate::leanh::LeanObject,
    mut v_i_792_: usize,
    mut v_stop_793_: usize,
    mut v_b_794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_795_: u8 = 0;
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: u32 = 0;
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: usize = 0;
    let mut v___x_801_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_795_ = lean_usize_dec_eq(v_i_792_, v_stop_793_);
                if v___x_795_ == 0 {
                    v___x_796_ = lean_array_uget_borrowed(v_as_791_, v_i_792_);
                    v___x_797_ = 10;
                    v___x_798_ = lean_string_push(v_b_794_, v___x_797_);
                    crate::leanh::lean_inc(v___x_796_);
                    v___x_799_ = l_Lake_ppImport(v___x_796_, v_isModule_790_, v___x_798_);
                    v___x_800_ = 1usize;
                    v___x_801_ = lean_usize_add(v_i_792_, v___x_800_);
                    v_i_792_ = v___x_801_;
                    v_b_794_ = v___x_799_;
                    state = 0;
                    continue;
                } else {
                    return v_b_794_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0___boxed(
    mut v_isModule_803_: *mut crate::leanh::LeanObject,
    mut v_as_804_: *mut crate::leanh::LeanObject,
    mut v_i_805_: *mut crate::leanh::LeanObject,
    mut v_stop_806_: *mut crate::leanh::LeanObject,
    mut v_b_807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isModule_boxed_808_: u8 = 0;
    let mut v_i_boxed_809_: usize = 0;
    let mut v_stop_boxed_810_: usize = 0;
    let mut v_res_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isModule_boxed_808_ = (crate::leanh::lean_unbox(v_isModule_803_) as u8);
    v_i_boxed_809_ = crate::leanh::lean_unbox_usize(v_i_805_);
    crate::leanh::lean_dec(v_i_805_);
    v_stop_boxed_810_ = crate::leanh::lean_unbox_usize(v_stop_806_);
    crate::leanh::lean_dec(v_stop_806_);
    v_res_811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0(v_isModule_boxed_808_, v_as_804_, v_i_boxed_809_, v_stop_boxed_810_, v_b_807_);
    crate::leanh::lean_dec_ref(v_as_804_);
    return v_res_811_;
}
pub unsafe fn l_Lake_ppModuleHeader(
    mut v_header_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_imports_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_816_: u8 = 0;
    let mut v___y_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: u8 = 0;
    let mut v___x_822_: u8 = 0;
    let mut v___x_823_: usize = 0;
    let mut v___x_824_: usize = 0;
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: usize = 0;
    let mut v___x_827_: usize = 0;
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_815_ = crate::leanh::lean_ctor_get(v_header_814_, 0);
                v_isModule_816_ = crate::leanh::lean_ctor_get_uint8(
                    v_header_814_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_isModule_816_ == 0 {
                    v___x_829_ = l_Lake_ppModuleHeader___closed__0;
                    v___y_818_ = v___x_829_;
                    state = 1;
                    continue;
                } else {
                    v___x_830_ = l_Lake_ppModuleHeader___closed__1;
                    v___y_818_ = v___x_830_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_819_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_820_ = lean_array_get_size(v_imports_815_);
                v___x_821_ = lean_nat_dec_lt(v___x_819_, v___x_820_);
                if v___x_821_ == 0 {
                    crate::leanh::lean_inc_ref(v___y_818_);
                    return v___y_818_;
                } else {
                    v___x_822_ = lean_nat_dec_le(v___x_820_, v___x_820_);
                    if v___x_822_ == 0 {
                        if v___x_821_ == 0 {
                            crate::leanh::lean_inc_ref(v___y_818_);
                            return v___y_818_;
                        } else {
                            v___x_823_ = 0usize;
                            v___x_824_ = lean_usize_of_nat(v___x_820_);
                            crate::leanh::lean_inc_ref(v___y_818_);
                            v___x_825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0(v_isModule_816_, v_imports_815_, v___x_823_, v___x_824_, v___y_818_);
                            return v___x_825_;
                        }
                    } else {
                        v___x_826_ = 0usize;
                        v___x_827_ = lean_usize_of_nat(v___x_820_);
                        crate::leanh::lean_inc_ref(v___y_818_);
                        v___x_828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0(v_isModule_816_, v_imports_815_, v___x_826_, v___x_827_, v___y_818_);
                        return v___x_828_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ppModuleHeader___boxed(
    mut v_header_831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_832_ = l_Lake_ppModuleHeader(v_header_831_);
    crate::leanh::lean_dec_ref(v_header_831_);
    return v_res_832_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_OutFormat(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Setup(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_OutFormat(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_OutFormat(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Setup(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_OutFormat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_OutFormat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_OutFormat(builtin);
}
