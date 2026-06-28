// Lean compiler output
// Module: Lake.Config.LakeConfig
// Imports: Lake.Config.Cache Lake.Config.MetaClasses Lake.Config.Meta
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lake::Config::Cache::{
    initialize_Lake_Config_Cache, runtime_initialize_Lake_Config_Cache,
};
use crate::r#gen::Lake::Config::Meta::{
    initialize_Lake_Config_Meta, meta_initialize_Lake_Config_Meta,
};
use crate::r#gen::Lake::Config::MetaClasses::{
    initialize_Lake_Config_MetaClasses, runtime_initialize_Lake_Config_MetaClasses,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt, lean_string_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_box, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_uint8_once, lean_unbox, lean_unsigned_to_nat,
    lean_usize_once,
};
pub static mut l_Lake_instInhabitedCacheServiceKind_default: u8 = 0;
pub static mut l_Lake_instInhabitedCacheServiceKind: u8 = 0;
pub static l_Lake_CacheServiceKind_ofString_x3f___closed__0_value: LeanStringObject<10> =
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
        m_data: [114, 101, 115, 101, 114, 118, 111, 105, 114, 0],
    };
static mut l_Lake_CacheServiceKind_ofString_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceKind_ofString_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_CacheServiceKind_ofString_x3f___closed__1_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [115, 51, 0],
    };
static mut l_Lake_CacheServiceKind_ofString_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceKind_ofString_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lake_CacheServiceKind_ofString_x3f___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lake_CacheServiceKind_ofString_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceKind_ofString_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lake_CacheServiceKind_ofString_x3f___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lake_CacheServiceKind_ofString_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceKind_ofString_x3f___closed__3_value) as *mut LeanObject;
pub static l_Lake_instInhabitedCacheServiceConfig_default___closed__0_value: LeanStringObject<1> =
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
static mut l_Lake_instInhabitedCacheServiceConfig_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedCacheServiceConfig_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedCacheServiceConfig_default___closed__1_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 8) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instInhabitedCacheServiceConfig_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedCacheServiceConfig_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedCacheServiceConfig_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedCacheServiceConfig_default___closed__0_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lake_instInhabitedCacheServiceConfig_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedCacheServiceConfig_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_instInhabitedCacheServiceConfig_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedCacheServiceConfig_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_instInhabitedCacheServiceConfig: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedCacheServiceConfig_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_name___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheServiceConfig_name___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheServiceConfig_name___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_name___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_name___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheServiceConfig_name___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheServiceConfig_name___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_name___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_name___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheServiceConfig_name___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheServiceConfig_name___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_name___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_name___proj___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheServiceConfig_name___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheServiceConfig_name___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_name___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_name___proj___closed__4_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_name___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_name___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_name___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_name___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig_name___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_name___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_CacheServiceConfig_name___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_name___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_CacheServiceConfig_name_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_name___proj___closed__4_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_kind___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheServiceConfig_kind___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheServiceConfig_kind___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_kind___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_kind___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheServiceConfig_kind___proj___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheServiceConfig_kind___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_kind___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_kind___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheServiceConfig_kind___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheServiceConfig_kind___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_kind___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_kind___proj___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheServiceConfig_kind___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheServiceConfig_kind___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_kind___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_kind___proj___closed__4_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_kind___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_kind___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_kind___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_kind___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig_kind___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_kind___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_CacheServiceConfig_kind___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_kind___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_CacheServiceConfig_kind_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_kind___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_CacheServiceConfig_type_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_kind___proj___closed__4_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__3_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_name___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lake_CacheServiceConfig_apiEndpoint___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lake_CacheServiceConfig_apiEndpoint_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__0_value: LeanClosureObject<
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
    m_fun: l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__1_value: LeanClosureObject<
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
    m_fun: l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__2_value: LeanClosureObject<
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
    m_fun: l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__3_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_name___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lake_CacheServiceConfig_artifactEndpoint___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lake_CacheServiceConfig_artifactEndpoint_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__0_value: LeanClosureObject<
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
    m_fun: l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__1_value: LeanClosureObject<
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
    m_fun: l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__2_value: LeanClosureObject<
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
    m_fun: l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__3_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_name___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lake_CacheServiceConfig_revisionEndpoint___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lake_CacheServiceConfig_revisionEndpoint_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig___fields___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lake_CacheServiceConfig___fields___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__0_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig___fields___closed__1_value: LeanStringObject<5> =
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
        m_data: [110, 97, 109, 101, 0],
    };
static mut l_Lake_CacheServiceConfig___fields___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__1_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig___fields___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__1_value)
                as *mut LeanObject,
            5949480926448383572 as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig___fields___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__2_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig___fields___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__2_value)
                as *mut LeanObject,
            1 as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig___fields___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__3_value) as *mut LeanObject;
static mut l_Lake_CacheServiceConfig___fields___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_CacheServiceConfig___fields___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_CacheServiceConfig___fields___closed__5_value: LeanStringObject<5> =
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
        m_data: [107, 105, 110, 100, 0],
    };
static mut l_Lake_CacheServiceConfig___fields___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__5_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig___fields___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__5_value)
                as *mut LeanObject,
            11445860042738416218 as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig___fields___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__6_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig___fields___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__6_value)
                as *mut LeanObject,
            1 as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig___fields___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__7_value) as *mut LeanObject;
static mut l_Lake_CacheServiceConfig___fields___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_CacheServiceConfig___fields___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_CacheServiceConfig___fields___closed__9_value: LeanStringObject<5> =
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
        m_data: [116, 121, 112, 101, 0],
    };
static mut l_Lake_CacheServiceConfig___fields___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__9_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig___fields___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__9_value)
                as *mut LeanObject,
            11503787708459150704 as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig___fields___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__10_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig___fields___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__6_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig___fields___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__11_value) as *mut LeanObject;
static mut l_Lake_CacheServiceConfig___fields___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_CacheServiceConfig___fields___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_CacheServiceConfig___fields___closed__13_value: LeanStringObject<12> =
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
        m_data: [97, 112, 105, 69, 110, 100, 112, 111, 105, 110, 116, 0],
    };
static mut l_Lake_CacheServiceConfig___fields___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__13_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig___fields___closed__14_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__13_value)
                as *mut LeanObject,
            7099927019568803161 as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig___fields___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__14_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig___fields___closed__15_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__14_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__14_value)
                as *mut LeanObject,
            1 as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig___fields___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__15_value) as *mut LeanObject;
static mut l_Lake_CacheServiceConfig___fields___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_CacheServiceConfig___fields___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_CacheServiceConfig___fields___closed__17_value: LeanStringObject<17> =
    LeanStringObject {
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
            97, 114, 116, 105, 102, 97, 99, 116, 69, 110, 100, 112, 111, 105, 110, 116, 0,
        ],
    };
static mut l_Lake_CacheServiceConfig___fields___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__17_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig___fields___closed__18_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__17_value)
                as *mut LeanObject,
            3424098782345919221 as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig___fields___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__18_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig___fields___closed__19_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__18_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__18_value)
                as *mut LeanObject,
            1 as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig___fields___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__19_value) as *mut LeanObject;
static mut l_Lake_CacheServiceConfig___fields___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_CacheServiceConfig___fields___closed__20: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_CacheServiceConfig___fields___closed__21_value: LeanStringObject<17> =
    LeanStringObject {
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
            114, 101, 118, 105, 115, 105, 111, 110, 69, 110, 100, 112, 111, 105, 110, 116, 0,
        ],
    };
static mut l_Lake_CacheServiceConfig___fields___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__21_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig___fields___closed__22_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__21_value)
                as *mut LeanObject,
            8770602121871834863 as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig___fields___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__22_value) as *mut LeanObject;
pub static l_Lake_CacheServiceConfig___fields___closed__23_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__22_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__22_value)
                as *mut LeanObject,
            1 as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig___fields___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig___fields___closed__23_value) as *mut LeanObject;
static mut l_Lake_CacheServiceConfig___fields___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_CacheServiceConfig___fields___closed__24: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_CacheServiceConfig___fields: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_CacheServiceConfig_instConfigFields: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_CacheServiceConfig_instConfigInfo___closed__1_value: LeanClosureObject<0> =
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
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_instConfigInfo___closed__2_value: LeanClosureObject<0> =
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
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_instConfigInfo___closed__3_value: LeanClosureObject<0> =
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
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_instConfigInfo___closed__4_value: LeanClosureObject<0> =
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
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_instConfigInfo___closed__5_value: LeanClosureObject<0> =
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
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__5_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_instConfigInfo___closed__6_value: LeanClosureObject<0> =
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
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__6_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_instConfigInfo___closed__7_value: LeanClosureObject<0> =
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
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__7_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_instConfigInfo___closed__8_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__8_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_instConfigInfo___closed__9_value: LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__9_value)
        as *mut LeanObject;
pub static l_Lake_CacheServiceConfig_instConfigInfo___closed__10_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__10_value)
        as *mut LeanObject;
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__11: u8 = 0;
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_CacheServiceConfig_instConfigInfo___closed__13_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheServiceConfig_instConfigInfo___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheServiceConfig_instConfigInfo___closed__13_value)
        as *mut LeanObject;
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__14: u8 = 0;
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__15: usize = 0;
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_CacheServiceConfig_instConfigInfo___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_CacheServiceConfig_instConfigInfo: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_CacheServiceConfig_instEmptyCollection: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedCacheServiceConfig_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedCacheConfig_default___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lake_instInhabitedCacheConfig_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedCacheConfig_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedCacheConfig_default___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instInhabitedCacheServiceConfig_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedCacheServiceConfig_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedCacheConfig_default___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instInhabitedCacheConfig_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedCacheConfig_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_instInhabitedCacheConfig_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedCacheConfig_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_instInhabitedCacheConfig: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedCacheConfig_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_CacheConfig_defaultService___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheConfig_defaultService___proj___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheConfig_defaultService___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_defaultService___proj___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_CacheConfig_defaultService___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheConfig_defaultService___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheConfig_defaultService___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_defaultService___proj___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_CacheConfig_defaultService___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheConfig_defaultService___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheConfig_defaultService___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_defaultService___proj___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_CacheConfig_defaultService___proj___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheConfig_defaultService___proj___lam__3___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheConfig_defaultService___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_defaultService___proj___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_CacheConfig_defaultService___proj___closed__4_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_CacheConfig_defaultService___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheConfig_defaultService___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheConfig_defaultService___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheConfig_defaultService___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheConfig_defaultService___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_defaultService___proj___closed__4_value)
        as *mut LeanObject;
pub static mut l_Lake_CacheConfig_defaultService___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_defaultService___proj___closed__4_value)
        as *mut LeanObject;
pub static mut l_Lake_CacheConfig_defaultService_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_defaultService___proj___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_CacheConfig_defaultUploadService___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheConfig_defaultUploadService___proj___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheConfig_defaultUploadService___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_defaultUploadService___proj___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_CacheConfig_defaultUploadService___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheConfig_defaultUploadService___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheConfig_defaultUploadService___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_defaultUploadService___proj___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_CacheConfig_defaultUploadService___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheConfig_defaultUploadService___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheConfig_defaultUploadService___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_defaultUploadService___proj___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_CacheConfig_defaultUploadService___proj___closed__3_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_CacheConfig_defaultUploadService___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheConfig_defaultUploadService___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheConfig_defaultUploadService___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheConfig_defaultService___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheConfig_defaultUploadService___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_defaultUploadService___proj___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lake_CacheConfig_defaultUploadService___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_defaultUploadService___proj___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lake_CacheConfig_defaultUploadService_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_defaultUploadService___proj___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_CacheConfig_services___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheConfig_services___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheConfig_services___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_services___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_CacheConfig_services___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheConfig_services___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheConfig_services___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_services___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_CacheConfig_services___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheConfig_services___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheConfig_services___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_services___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_CacheConfig_services___proj___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CacheConfig_services___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CacheConfig_services___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_services___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_CacheConfig_services___proj___closed__4_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_CacheConfig_services___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheConfig_services___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheConfig_services___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_CacheConfig_services___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_CacheConfig_services___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_services___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_CacheConfig_services___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_services___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_CacheConfig_service_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig_services___proj___closed__4_value) as *mut LeanObject;
pub static l_Lake_CacheConfig___fields___closed__0_value: LeanStringObject<15> = LeanStringObject {
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
        100, 101, 102, 97, 117, 108, 116, 83, 101, 114, 118, 105, 99, 101, 0,
    ],
};
static mut l_Lake_CacheConfig___fields___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__0_value) as *mut LeanObject;
pub static l_Lake_CacheConfig___fields___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__0_value) as *mut LeanObject,
        7671415556498737588 as *mut LeanObject,
    ],
};
static mut l_Lake_CacheConfig___fields___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__1_value) as *mut LeanObject;
pub static l_Lake_CacheConfig___fields___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__1_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_CacheConfig___fields___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__2_value) as *mut LeanObject;
static mut l_Lake_CacheConfig___fields___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_CacheConfig___fields___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_CacheConfig___fields___closed__4_value: LeanStringObject<21> = LeanStringObject {
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
        100, 101, 102, 97, 117, 108, 116, 85, 112, 108, 111, 97, 100, 83, 101, 114, 118, 105, 99,
        101, 0,
    ],
};
static mut l_Lake_CacheConfig___fields___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__4_value) as *mut LeanObject;
pub static l_Lake_CacheConfig___fields___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__4_value) as *mut LeanObject,
        11829887590799302480 as *mut LeanObject,
    ],
};
static mut l_Lake_CacheConfig___fields___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__5_value) as *mut LeanObject;
pub static l_Lake_CacheConfig___fields___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__5_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_CacheConfig___fields___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__6_value) as *mut LeanObject;
static mut l_Lake_CacheConfig___fields___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_CacheConfig___fields___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_CacheConfig___fields___closed__8_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 101, 114, 118, 105, 99, 101, 0],
};
static mut l_Lake_CacheConfig___fields___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__8_value) as *mut LeanObject;
pub static l_Lake_CacheConfig___fields___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__8_value) as *mut LeanObject,
        15757077380799170046 as *mut LeanObject,
    ],
};
static mut l_Lake_CacheConfig___fields___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__9_value) as *mut LeanObject;
pub static l_Lake_CacheConfig___fields___closed__10_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [115, 101, 114, 118, 105, 99, 101, 115, 0],
};
static mut l_Lake_CacheConfig___fields___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__10_value) as *mut LeanObject;
pub static l_Lake_CacheConfig___fields___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__10_value) as *mut LeanObject,
        10502571181597865326 as *mut LeanObject,
    ],
};
static mut l_Lake_CacheConfig___fields___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__11_value) as *mut LeanObject;
pub static l_Lake_CacheConfig___fields___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__11_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_CacheConfig___fields___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CacheConfig___fields___closed__12_value) as *mut LeanObject;
static mut l_Lake_CacheConfig___fields___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_CacheConfig___fields___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_CacheConfig___fields: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_CacheConfig_instConfigFields: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_CacheConfig_instConfigInfo___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_CacheConfig_instConfigInfo___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_CacheConfig_instConfigInfo___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_CacheConfig_instConfigInfo___closed__1: u8 = 0;
static mut l_Lake_CacheConfig_instConfigInfo___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_CacheConfig_instConfigInfo___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_CacheConfig_instConfigInfo___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_CacheConfig_instConfigInfo___closed__3: u8 = 0;
static mut l_Lake_CacheConfig_instConfigInfo___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_CacheConfig_instConfigInfo___closed__4: usize = 0;
static mut l_Lake_CacheConfig_instConfigInfo___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_CacheConfig_instConfigInfo___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_CacheConfig_instConfigInfo___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_CacheConfig_instConfigInfo___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_CacheConfig_instConfigInfo: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_CacheConfig_instEmptyCollection: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedCacheConfig_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_instInhabitedLakeConfig_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedCacheConfig_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_instInhabitedLakeConfig: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedCacheConfig_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_LakeConfig_cache___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LakeConfig_cache___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LakeConfig_cache___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LakeConfig_cache___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_LakeConfig_cache___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LakeConfig_cache___proj___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LakeConfig_cache___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LakeConfig_cache___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_LakeConfig_cache___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LakeConfig_cache___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LakeConfig_cache___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LakeConfig_cache___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_LakeConfig_cache___proj___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LakeConfig_cache___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LakeConfig_cache___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LakeConfig_cache___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_LakeConfig_cache___proj___closed__4_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LakeConfig_cache___proj___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LakeConfig_cache___proj___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LakeConfig_cache___proj___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LakeConfig_cache___proj___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_LakeConfig_cache___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LakeConfig_cache___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_LakeConfig_cache___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LakeConfig_cache___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_LakeConfig_cache_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LakeConfig_cache___proj___closed__4_value) as *mut LeanObject;
pub static l_Lake_LakeConfig___fields___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 97, 99, 104, 101, 0],
};
static mut l_Lake_LakeConfig___fields___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LakeConfig___fields___closed__0_value) as *mut LeanObject;
pub static l_Lake_LakeConfig___fields___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_LakeConfig___fields___closed__0_value) as *mut LeanObject,
        6317631098742144178 as *mut LeanObject,
    ],
};
static mut l_Lake_LakeConfig___fields___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LakeConfig___fields___closed__1_value) as *mut LeanObject;
pub static l_Lake_LakeConfig___fields___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LakeConfig___fields___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LakeConfig___fields___closed__1_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LakeConfig___fields___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LakeConfig___fields___closed__2_value) as *mut LeanObject;
static mut l_Lake_LakeConfig___fields___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LakeConfig___fields___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_LakeConfig___fields: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_LakeConfig_instConfigFields: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_LakeConfig_instConfigInfo___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LakeConfig_instConfigInfo___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_LakeConfig_instConfigInfo___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LakeConfig_instConfigInfo___closed__1: u8 = 0;
static mut l_Lake_LakeConfig_instConfigInfo___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LakeConfig_instConfigInfo___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_LakeConfig_instConfigInfo___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LakeConfig_instConfigInfo___closed__3: u8 = 0;
static mut l_Lake_LakeConfig_instConfigInfo___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LakeConfig_instConfigInfo___closed__4: usize = 0;
static mut l_Lake_LakeConfig_instConfigInfo___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LakeConfig_instConfigInfo___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_LakeConfig_instConfigInfo___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LakeConfig_instConfigInfo___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_LakeConfig_instConfigInfo: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_LakeConfig_instEmptyCollection: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedCacheConfig_default___closed__1_value)
        as *mut LeanObject;
pub unsafe fn l_Lake_CacheServiceKind_ctorIdx(mut v_x_717_: u8) -> *mut LeanObject {
    match v_x_717_ {
        0 => {
            let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
            v___x_718_ = lean_unsigned_to_nat(0);
            return v___x_718_;
        }
        1 => {
            let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
            v___x_719_ = lean_unsigned_to_nat(1);
            return v___x_719_;
        }
        _ => {
            let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
            v___x_720_ = lean_unsigned_to_nat(2);
            return v___x_720_;
        }
    }
}
pub unsafe fn l_Lake_CacheServiceKind_ctorIdx___boxed(
    mut v_x_721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_722_: u8 = 0;
    let mut v_res_723_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_722_ = (lean_unbox(v_x_721_) as u8);
    v_res_723_ = l_Lake_CacheServiceKind_ctorIdx(v_x_boxed_722_);
    return v_res_723_;
}
pub unsafe fn l_Lake_CacheServiceKind_toCtorIdx(mut v_x_724_: u8) -> *mut LeanObject {
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    v___x_725_ = l_Lake_CacheServiceKind_ctorIdx(v_x_724_);
    return v___x_725_;
}
pub unsafe fn l_Lake_CacheServiceKind_toCtorIdx___boxed(
    mut v_x_726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_727_: u8 = 0;
    let mut v_res_728_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_727_ = (lean_unbox(v_x_726_) as u8);
    v_res_728_ = l_Lake_CacheServiceKind_toCtorIdx(v_x_4__boxed_727_);
    return v_res_728_;
}
pub unsafe fn l_Lake_CacheServiceKind_ctorElim___redArg(
    mut v_k_729_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_729_);
    return v_k_729_;
}
pub unsafe fn l_Lake_CacheServiceKind_ctorElim___redArg___boxed(
    mut v_k_730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_731_: *mut LeanObject = core::ptr::null_mut();
    v_res_731_ = l_Lake_CacheServiceKind_ctorElim___redArg(v_k_730_);
    lean_dec(v_k_730_);
    return v_res_731_;
}
pub unsafe fn l_Lake_CacheServiceKind_ctorElim(
    mut v_motive_732_: *mut LeanObject,
    mut v_ctorIdx_733_: *mut LeanObject,
    mut v_t_734_: u8,
    mut v_h_735_: *mut LeanObject,
    mut v_k_736_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_736_);
    return v_k_736_;
}
pub unsafe fn l_Lake_CacheServiceKind_ctorElim___boxed(
    mut v_motive_737_: *mut LeanObject,
    mut v_ctorIdx_738_: *mut LeanObject,
    mut v_t_739_: *mut LeanObject,
    mut v_h_740_: *mut LeanObject,
    mut v_k_741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_742_: u8 = 0;
    let mut v_res_743_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_742_ = (lean_unbox(v_t_739_) as u8);
    v_res_743_ = l_Lake_CacheServiceKind_ctorElim(
        v_motive_737_,
        v_ctorIdx_738_,
        v_t_boxed_742_,
        v_h_740_,
        v_k_741_,
    );
    lean_dec(v_k_741_);
    lean_dec(v_ctorIdx_738_);
    return v_res_743_;
}
pub unsafe fn l_Lake_CacheServiceKind_undef_elim___redArg(
    mut v_undef_744_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_undef_744_);
    return v_undef_744_;
}
pub unsafe fn l_Lake_CacheServiceKind_undef_elim___redArg___boxed(
    mut v_undef_745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_746_: *mut LeanObject = core::ptr::null_mut();
    v_res_746_ = l_Lake_CacheServiceKind_undef_elim___redArg(v_undef_745_);
    lean_dec(v_undef_745_);
    return v_res_746_;
}
pub unsafe fn l_Lake_CacheServiceKind_undef_elim(
    mut v_motive_747_: *mut LeanObject,
    mut v_t_748_: u8,
    mut v_h_749_: *mut LeanObject,
    mut v_undef_750_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_undef_750_);
    return v_undef_750_;
}
pub unsafe fn l_Lake_CacheServiceKind_undef_elim___boxed(
    mut v_motive_751_: *mut LeanObject,
    mut v_t_752_: *mut LeanObject,
    mut v_h_753_: *mut LeanObject,
    mut v_undef_754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_755_: u8 = 0;
    let mut v_res_756_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_755_ = (lean_unbox(v_t_752_) as u8);
    v_res_756_ =
        l_Lake_CacheServiceKind_undef_elim(v_motive_751_, v_t_boxed_755_, v_h_753_, v_undef_754_);
    lean_dec(v_undef_754_);
    return v_res_756_;
}
pub unsafe fn l_Lake_CacheServiceKind_reservoir_elim___redArg(
    mut v_reservoir_757_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_reservoir_757_);
    return v_reservoir_757_;
}
pub unsafe fn l_Lake_CacheServiceKind_reservoir_elim___redArg___boxed(
    mut v_reservoir_758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_759_: *mut LeanObject = core::ptr::null_mut();
    v_res_759_ = l_Lake_CacheServiceKind_reservoir_elim___redArg(v_reservoir_758_);
    lean_dec(v_reservoir_758_);
    return v_res_759_;
}
pub unsafe fn l_Lake_CacheServiceKind_reservoir_elim(
    mut v_motive_760_: *mut LeanObject,
    mut v_t_761_: u8,
    mut v_h_762_: *mut LeanObject,
    mut v_reservoir_763_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_reservoir_763_);
    return v_reservoir_763_;
}
pub unsafe fn l_Lake_CacheServiceKind_reservoir_elim___boxed(
    mut v_motive_764_: *mut LeanObject,
    mut v_t_765_: *mut LeanObject,
    mut v_h_766_: *mut LeanObject,
    mut v_reservoir_767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_768_: u8 = 0;
    let mut v_res_769_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_768_ = (lean_unbox(v_t_765_) as u8);
    v_res_769_ = l_Lake_CacheServiceKind_reservoir_elim(
        v_motive_764_,
        v_t_boxed_768_,
        v_h_766_,
        v_reservoir_767_,
    );
    lean_dec(v_reservoir_767_);
    return v_res_769_;
}
pub unsafe fn l_Lake_CacheServiceKind_s3_elim___redArg(
    mut v_s3_770_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_s3_770_);
    return v_s3_770_;
}
pub unsafe fn l_Lake_CacheServiceKind_s3_elim___redArg___boxed(
    mut v_s3_771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_772_: *mut LeanObject = core::ptr::null_mut();
    v_res_772_ = l_Lake_CacheServiceKind_s3_elim___redArg(v_s3_771_);
    lean_dec(v_s3_771_);
    return v_res_772_;
}
pub unsafe fn l_Lake_CacheServiceKind_s3_elim(
    mut v_motive_773_: *mut LeanObject,
    mut v_t_774_: u8,
    mut v_h_775_: *mut LeanObject,
    mut v_s3_776_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_s3_776_);
    return v_s3_776_;
}
pub unsafe fn l_Lake_CacheServiceKind_s3_elim___boxed(
    mut v_motive_777_: *mut LeanObject,
    mut v_t_778_: *mut LeanObject,
    mut v_h_779_: *mut LeanObject,
    mut v_s3_780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_781_: u8 = 0;
    let mut v_res_782_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_781_ = (lean_unbox(v_t_778_) as u8);
    v_res_782_ =
        l_Lake_CacheServiceKind_s3_elim(v_motive_777_, v_t_boxed_781_, v_h_779_, v_s3_780_);
    lean_dec(v_s3_780_);
    return v_res_782_;
}
pub unsafe fn _init_l_Lake_instInhabitedCacheServiceKind_default() -> u8 {
    let mut v___x_783_: u8 = 0;
    v___x_783_ = 0;
    return v___x_783_;
}
pub unsafe fn _init_l_Lake_instInhabitedCacheServiceKind() -> u8 {
    let mut v___x_784_: u8 = 0;
    v___x_784_ = 0;
    return v___x_784_;
}
pub unsafe fn l_Lake_CacheServiceKind_ofString_x3f(
    mut v_s_793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: u8 = 0;
    v___x_794_ = l_Lake_CacheServiceKind_ofString_x3f___closed__0;
    v___x_795_ = lean_string_dec_eq(v_s_793_, v___x_794_);
    if v___x_795_ == 0 {
        let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_797_: u8 = 0;
        v___x_796_ = l_Lake_CacheServiceKind_ofString_x3f___closed__1;
        v___x_797_ = lean_string_dec_eq(v_s_793_, v___x_796_);
        if v___x_797_ == 0 {
            let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
            v___x_798_ = lean_box(0);
            return v___x_798_;
        } else {
            let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
            v___x_799_ = l_Lake_CacheServiceKind_ofString_x3f___closed__2;
            return v___x_799_;
        }
    } else {
        let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
        v___x_800_ = l_Lake_CacheServiceKind_ofString_x3f___closed__3;
        return v___x_800_;
    }
}
pub unsafe fn l_Lake_CacheServiceKind_ofString_x3f___boxed(
    mut v_s_801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_802_: *mut LeanObject = core::ptr::null_mut();
    v_res_802_ = l_Lake_CacheServiceKind_ofString_x3f(v_s_801_);
    lean_dec_ref(v_s_801_);
    return v_res_802_;
}
pub unsafe fn l_Lake_CacheServiceConfig_name___proj___lam__0(
    mut v_cfg_809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_810_: *mut LeanObject = core::ptr::null_mut();
    v_name_810_ = lean_ctor_get(v_cfg_809_, 0);
    lean_inc_ref(v_name_810_);
    return v_name_810_;
}
pub unsafe fn l_Lake_CacheServiceConfig_name___proj___lam__0___boxed(
    mut v_cfg_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_812_: *mut LeanObject = core::ptr::null_mut();
    v_res_812_ = l_Lake_CacheServiceConfig_name___proj___lam__0(v_cfg_811_);
    lean_dec_ref(v_cfg_811_);
    return v_res_812_;
}
pub unsafe fn l_Lake_CacheServiceConfig_name___proj___lam__1(
    mut v_val_813_: *mut LeanObject,
    mut v_cfg_814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_815_: u8 = 0;
    let mut v_apiEndpoint_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_artifactEndpoint_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_revisionEndpoint_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_821_: u8 = 0;
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_825_: u8 = 0;
    let mut v_unused_826_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kind_815_ = lean_ctor_get_uint8(
                    v_cfg_814_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_apiEndpoint_816_ = lean_ctor_get(v_cfg_814_, 1);
                v_artifactEndpoint_817_ = lean_ctor_get(v_cfg_814_, 2);
                v_revisionEndpoint_818_ = lean_ctor_get(v_cfg_814_, 3);
                v_isSharedCheck_825_ = (!lean_is_exclusive(v_cfg_814_)) as u8;
                if v_isSharedCheck_825_ == 0 {
                    v_unused_826_ = lean_ctor_get(v_cfg_814_, 0);
                    lean_dec(v_unused_826_);
                    v___x_820_ = v_cfg_814_;
                    v_isShared_821_ = v_isSharedCheck_825_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_revisionEndpoint_818_);
                    lean_inc(v_artifactEndpoint_817_);
                    lean_inc(v_apiEndpoint_816_);
                    lean_dec(v_cfg_814_);
                    v___x_820_ = lean_box(0);
                    v_isShared_821_ = v_isSharedCheck_825_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_821_ == 0 {
                    lean_ctor_set(v___x_820_, 0, v_val_813_);
                    v___x_823_ = v___x_820_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_824_, 0, v_val_813_);
                    lean_ctor_set(v_reuseFailAlloc_824_, 1, v_apiEndpoint_816_);
                    lean_ctor_set(v_reuseFailAlloc_824_, 2, v_artifactEndpoint_817_);
                    lean_ctor_set(v_reuseFailAlloc_824_, 3, v_revisionEndpoint_818_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_824_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_kind_815_,
                    );
                    v___x_823_ = v_reuseFailAlloc_824_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_823_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_CacheServiceConfig_name___proj___lam__2(
    mut v_f_827_: *mut LeanObject,
    mut v_cfg_828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_830_: u8 = 0;
    let mut v_apiEndpoint_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_artifactEndpoint_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_revisionEndpoint_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_836_: u8 = 0;
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_841_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_829_ = lean_ctor_get(v_cfg_828_, 0);
                v_kind_830_ = lean_ctor_get_uint8(
                    v_cfg_828_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_apiEndpoint_831_ = lean_ctor_get(v_cfg_828_, 1);
                v_artifactEndpoint_832_ = lean_ctor_get(v_cfg_828_, 2);
                v_revisionEndpoint_833_ = lean_ctor_get(v_cfg_828_, 3);
                v_isSharedCheck_841_ = (!lean_is_exclusive(v_cfg_828_)) as u8;
                if v_isSharedCheck_841_ == 0 {
                    v___x_835_ = v_cfg_828_;
                    v_isShared_836_ = v_isSharedCheck_841_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_revisionEndpoint_833_);
                    lean_inc(v_artifactEndpoint_832_);
                    lean_inc(v_apiEndpoint_831_);
                    lean_inc(v_name_829_);
                    lean_dec(v_cfg_828_);
                    v___x_835_ = lean_box(0);
                    v_isShared_836_ = v_isSharedCheck_841_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_837_ = lean_apply_1(v_f_827_, v_name_829_);
                if v_isShared_836_ == 0 {
                    lean_ctor_set(v___x_835_, 0, v___x_837_);
                    v___x_839_ = v___x_835_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
                    lean_ctor_set(v_reuseFailAlloc_840_, 1, v_apiEndpoint_831_);
                    lean_ctor_set(v_reuseFailAlloc_840_, 2, v_artifactEndpoint_832_);
                    lean_ctor_set(v_reuseFailAlloc_840_, 3, v_revisionEndpoint_833_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_840_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_kind_830_,
                    );
                    v___x_839_ = v_reuseFailAlloc_840_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_839_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_CacheServiceConfig_name___proj___lam__3(
    mut v_x_842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    v___x_843_ = l_Lake_instInhabitedCacheServiceConfig_default___closed__0;
    return v___x_843_;
}
pub unsafe fn l_Lake_CacheServiceConfig_name___proj___lam__3___boxed(
    mut v_x_844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_845_: *mut LeanObject = core::ptr::null_mut();
    v_res_845_ = l_Lake_CacheServiceConfig_name___proj___lam__3(v_x_844_);
    lean_dec_ref(v_x_844_);
    return v_res_845_;
}
pub unsafe fn l_Lake_CacheServiceConfig_kind___proj___lam__0(
    mut v_cfg_857_: *mut LeanObject,
) -> u8 {
    let mut v_kind_858_: u8 = 0;
    v_kind_858_ = lean_ctor_get_uint8(
        v_cfg_857_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
    );
    return v_kind_858_;
}
pub unsafe fn l_Lake_CacheServiceConfig_kind___proj___lam__0___boxed(
    mut v_cfg_859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_860_: u8 = 0;
    let mut v_r_861_: *mut LeanObject = core::ptr::null_mut();
    v_res_860_ = l_Lake_CacheServiceConfig_kind___proj___lam__0(v_cfg_859_);
    lean_dec_ref(v_cfg_859_);
    v_r_861_ = lean_box((v_res_860_) as usize);
    return v_r_861_;
}
pub unsafe fn l_Lake_CacheServiceConfig_kind___proj___lam__1(
    mut v_val_862_: u8,
    mut v_cfg_863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_apiEndpoint_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_artifactEndpoint_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_revisionEndpoint_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_870_: u8 = 0;
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_864_ = lean_ctor_get(v_cfg_863_, 0);
                v_apiEndpoint_865_ = lean_ctor_get(v_cfg_863_, 1);
                v_artifactEndpoint_866_ = lean_ctor_get(v_cfg_863_, 2);
                v_revisionEndpoint_867_ = lean_ctor_get(v_cfg_863_, 3);
                v_isSharedCheck_874_ = (!lean_is_exclusive(v_cfg_863_)) as u8;
                if v_isSharedCheck_874_ == 0 {
                    v___x_869_ = v_cfg_863_;
                    v_isShared_870_ = v_isSharedCheck_874_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_revisionEndpoint_867_);
                    lean_inc(v_artifactEndpoint_866_);
                    lean_inc(v_apiEndpoint_865_);
                    lean_inc(v_name_864_);
                    lean_dec(v_cfg_863_);
                    v___x_869_ = lean_box(0);
                    v_isShared_870_ = v_isSharedCheck_874_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_870_ == 0 {
                    v___x_872_ = v___x_869_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_873_, 0, v_name_864_);
                    lean_ctor_set(v_reuseFailAlloc_873_, 1, v_apiEndpoint_865_);
                    lean_ctor_set(v_reuseFailAlloc_873_, 2, v_artifactEndpoint_866_);
                    lean_ctor_set(v_reuseFailAlloc_873_, 3, v_revisionEndpoint_867_);
                    v___x_872_ = v_reuseFailAlloc_873_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_872_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v_val_862_,
                );
                return v___x_872_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_CacheServiceConfig_kind___proj___lam__1___boxed(
    mut v_val_875_: *mut LeanObject,
    mut v_cfg_876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_49__boxed_877_: u8 = 0;
    let mut v_res_878_: *mut LeanObject = core::ptr::null_mut();
    v_val_49__boxed_877_ = (lean_unbox(v_val_875_) as u8);
    v_res_878_ = l_Lake_CacheServiceConfig_kind___proj___lam__1(v_val_49__boxed_877_, v_cfg_876_);
    return v_res_878_;
}
pub unsafe fn l_Lake_CacheServiceConfig_kind___proj___lam__2(
    mut v_f_879_: *mut LeanObject,
    mut v_cfg_880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_882_: u8 = 0;
    let mut v_apiEndpoint_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_artifactEndpoint_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_revisionEndpoint_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_888_: u8 = 0;
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: u8 = 0;
    let mut v_reuseFailAlloc_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_881_ = lean_ctor_get(v_cfg_880_, 0);
                v_kind_882_ = lean_ctor_get_uint8(
                    v_cfg_880_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_apiEndpoint_883_ = lean_ctor_get(v_cfg_880_, 1);
                v_artifactEndpoint_884_ = lean_ctor_get(v_cfg_880_, 2);
                v_revisionEndpoint_885_ = lean_ctor_get(v_cfg_880_, 3);
                v_isSharedCheck_895_ = (!lean_is_exclusive(v_cfg_880_)) as u8;
                if v_isSharedCheck_895_ == 0 {
                    v___x_887_ = v_cfg_880_;
                    v_isShared_888_ = v_isSharedCheck_895_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_revisionEndpoint_885_);
                    lean_inc(v_artifactEndpoint_884_);
                    lean_inc(v_apiEndpoint_883_);
                    lean_inc(v_name_881_);
                    lean_dec(v_cfg_880_);
                    v___x_887_ = lean_box(0);
                    v_isShared_888_ = v_isSharedCheck_895_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_889_ = lean_box((v_kind_882_) as usize);
                v___x_890_ = lean_apply_1(v_f_879_, v___x_889_);
                if v_isShared_888_ == 0 {
                    v___x_892_ = v___x_887_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_894_, 0, v_name_881_);
                    lean_ctor_set(v_reuseFailAlloc_894_, 1, v_apiEndpoint_883_);
                    lean_ctor_set(v_reuseFailAlloc_894_, 2, v_artifactEndpoint_884_);
                    lean_ctor_set(v_reuseFailAlloc_894_, 3, v_revisionEndpoint_885_);
                    v___x_892_ = v_reuseFailAlloc_894_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_893_ = (lean_unbox(v___x_890_) as u8);
                lean_ctor_set_uint8(
                    v___x_892_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v___x_893_,
                );
                return v___x_892_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_CacheServiceConfig_kind___proj___lam__3(mut v_x_896_: *mut LeanObject) -> u8 {
    let mut v___x_897_: u8 = 0;
    v___x_897_ = 0;
    return v___x_897_;
}
pub unsafe fn l_Lake_CacheServiceConfig_kind___proj___lam__3___boxed(
    mut v_x_898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_899_: u8 = 0;
    let mut v_r_900_: *mut LeanObject = core::ptr::null_mut();
    v_res_899_ = l_Lake_CacheServiceConfig_kind___proj___lam__3(v_x_898_);
    lean_dec_ref(v_x_898_);
    v_r_900_ = lean_box((v_res_899_) as usize);
    return v_r_900_;
}
pub unsafe fn l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0(
    mut v_cfg_913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_apiEndpoint_914_: *mut LeanObject = core::ptr::null_mut();
    v_apiEndpoint_914_ = lean_ctor_get(v_cfg_913_, 1);
    lean_inc_ref(v_apiEndpoint_914_);
    return v_apiEndpoint_914_;
}
pub unsafe fn l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0___boxed(
    mut v_cfg_915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_916_: *mut LeanObject = core::ptr::null_mut();
    v_res_916_ = l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0(v_cfg_915_);
    lean_dec_ref(v_cfg_915_);
    return v_res_916_;
}
pub unsafe fn l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__1(
    mut v_val_917_: *mut LeanObject,
    mut v_cfg_918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_920_: u8 = 0;
    let mut v_artifactEndpoint_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_revisionEndpoint_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_925_: u8 = 0;
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_929_: u8 = 0;
    let mut v_unused_930_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_919_ = lean_ctor_get(v_cfg_918_, 0);
                v_kind_920_ = lean_ctor_get_uint8(
                    v_cfg_918_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_artifactEndpoint_921_ = lean_ctor_get(v_cfg_918_, 2);
                v_revisionEndpoint_922_ = lean_ctor_get(v_cfg_918_, 3);
                v_isSharedCheck_929_ = (!lean_is_exclusive(v_cfg_918_)) as u8;
                if v_isSharedCheck_929_ == 0 {
                    v_unused_930_ = lean_ctor_get(v_cfg_918_, 1);
                    lean_dec(v_unused_930_);
                    v___x_924_ = v_cfg_918_;
                    v_isShared_925_ = v_isSharedCheck_929_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_revisionEndpoint_922_);
                    lean_inc(v_artifactEndpoint_921_);
                    lean_inc(v_name_919_);
                    lean_dec(v_cfg_918_);
                    v___x_924_ = lean_box(0);
                    v_isShared_925_ = v_isSharedCheck_929_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_925_ == 0 {
                    lean_ctor_set(v___x_924_, 1, v_val_917_);
                    v___x_927_ = v___x_924_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_928_, 0, v_name_919_);
                    lean_ctor_set(v_reuseFailAlloc_928_, 1, v_val_917_);
                    lean_ctor_set(v_reuseFailAlloc_928_, 2, v_artifactEndpoint_921_);
                    lean_ctor_set(v_reuseFailAlloc_928_, 3, v_revisionEndpoint_922_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_928_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_kind_920_,
                    );
                    v___x_927_ = v_reuseFailAlloc_928_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_927_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__2(
    mut v_f_931_: *mut LeanObject,
    mut v_cfg_932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_934_: u8 = 0;
    let mut v_apiEndpoint_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_artifactEndpoint_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_revisionEndpoint_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_940_: u8 = 0;
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_945_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_933_ = lean_ctor_get(v_cfg_932_, 0);
                v_kind_934_ = lean_ctor_get_uint8(
                    v_cfg_932_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_apiEndpoint_935_ = lean_ctor_get(v_cfg_932_, 1);
                v_artifactEndpoint_936_ = lean_ctor_get(v_cfg_932_, 2);
                v_revisionEndpoint_937_ = lean_ctor_get(v_cfg_932_, 3);
                v_isSharedCheck_945_ = (!lean_is_exclusive(v_cfg_932_)) as u8;
                if v_isSharedCheck_945_ == 0 {
                    v___x_939_ = v_cfg_932_;
                    v_isShared_940_ = v_isSharedCheck_945_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_revisionEndpoint_937_);
                    lean_inc(v_artifactEndpoint_936_);
                    lean_inc(v_apiEndpoint_935_);
                    lean_inc(v_name_933_);
                    lean_dec(v_cfg_932_);
                    v___x_939_ = lean_box(0);
                    v_isShared_940_ = v_isSharedCheck_945_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_941_ = lean_apply_1(v_f_931_, v_apiEndpoint_935_);
                if v_isShared_940_ == 0 {
                    lean_ctor_set(v___x_939_, 1, v___x_941_);
                    v___x_943_ = v___x_939_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_944_, 0, v_name_933_);
                    lean_ctor_set(v_reuseFailAlloc_944_, 1, v___x_941_);
                    lean_ctor_set(v_reuseFailAlloc_944_, 2, v_artifactEndpoint_936_);
                    lean_ctor_set(v_reuseFailAlloc_944_, 3, v_revisionEndpoint_937_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_944_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_kind_934_,
                    );
                    v___x_943_ = v_reuseFailAlloc_944_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_943_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0(
    mut v_cfg_956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_artifactEndpoint_957_: *mut LeanObject = core::ptr::null_mut();
    v_artifactEndpoint_957_ = lean_ctor_get(v_cfg_956_, 2);
    lean_inc_ref(v_artifactEndpoint_957_);
    return v_artifactEndpoint_957_;
}
pub unsafe fn l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0___boxed(
    mut v_cfg_958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_959_: *mut LeanObject = core::ptr::null_mut();
    v_res_959_ = l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0(v_cfg_958_);
    lean_dec_ref(v_cfg_958_);
    return v_res_959_;
}
pub unsafe fn l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__1(
    mut v_val_960_: *mut LeanObject,
    mut v_cfg_961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_963_: u8 = 0;
    let mut v_apiEndpoint_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_revisionEndpoint_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_968_: u8 = 0;
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_972_: u8 = 0;
    let mut v_unused_973_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_962_ = lean_ctor_get(v_cfg_961_, 0);
                v_kind_963_ = lean_ctor_get_uint8(
                    v_cfg_961_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_apiEndpoint_964_ = lean_ctor_get(v_cfg_961_, 1);
                v_revisionEndpoint_965_ = lean_ctor_get(v_cfg_961_, 3);
                v_isSharedCheck_972_ = (!lean_is_exclusive(v_cfg_961_)) as u8;
                if v_isSharedCheck_972_ == 0 {
                    v_unused_973_ = lean_ctor_get(v_cfg_961_, 2);
                    lean_dec(v_unused_973_);
                    v___x_967_ = v_cfg_961_;
                    v_isShared_968_ = v_isSharedCheck_972_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_revisionEndpoint_965_);
                    lean_inc(v_apiEndpoint_964_);
                    lean_inc(v_name_962_);
                    lean_dec(v_cfg_961_);
                    v___x_967_ = lean_box(0);
                    v_isShared_968_ = v_isSharedCheck_972_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_968_ == 0 {
                    lean_ctor_set(v___x_967_, 2, v_val_960_);
                    v___x_970_ = v___x_967_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_971_, 0, v_name_962_);
                    lean_ctor_set(v_reuseFailAlloc_971_, 1, v_apiEndpoint_964_);
                    lean_ctor_set(v_reuseFailAlloc_971_, 2, v_val_960_);
                    lean_ctor_set(v_reuseFailAlloc_971_, 3, v_revisionEndpoint_965_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_971_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_kind_963_,
                    );
                    v___x_970_ = v_reuseFailAlloc_971_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_970_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__2(
    mut v_f_974_: *mut LeanObject,
    mut v_cfg_975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_977_: u8 = 0;
    let mut v_apiEndpoint_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_artifactEndpoint_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_revisionEndpoint_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_983_: u8 = 0;
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_988_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_976_ = lean_ctor_get(v_cfg_975_, 0);
                v_kind_977_ = lean_ctor_get_uint8(
                    v_cfg_975_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_apiEndpoint_978_ = lean_ctor_get(v_cfg_975_, 1);
                v_artifactEndpoint_979_ = lean_ctor_get(v_cfg_975_, 2);
                v_revisionEndpoint_980_ = lean_ctor_get(v_cfg_975_, 3);
                v_isSharedCheck_988_ = (!lean_is_exclusive(v_cfg_975_)) as u8;
                if v_isSharedCheck_988_ == 0 {
                    v___x_982_ = v_cfg_975_;
                    v_isShared_983_ = v_isSharedCheck_988_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_revisionEndpoint_980_);
                    lean_inc(v_artifactEndpoint_979_);
                    lean_inc(v_apiEndpoint_978_);
                    lean_inc(v_name_976_);
                    lean_dec(v_cfg_975_);
                    v___x_982_ = lean_box(0);
                    v_isShared_983_ = v_isSharedCheck_988_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_984_ = lean_apply_1(v_f_974_, v_artifactEndpoint_979_);
                if v_isShared_983_ == 0 {
                    lean_ctor_set(v___x_982_, 2, v___x_984_);
                    v___x_986_ = v___x_982_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_987_, 0, v_name_976_);
                    lean_ctor_set(v_reuseFailAlloc_987_, 1, v_apiEndpoint_978_);
                    lean_ctor_set(v_reuseFailAlloc_987_, 2, v___x_984_);
                    lean_ctor_set(v_reuseFailAlloc_987_, 3, v_revisionEndpoint_980_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_987_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_kind_977_,
                    );
                    v___x_986_ = v_reuseFailAlloc_987_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_986_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0(
    mut v_cfg_999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_revisionEndpoint_1000_: *mut LeanObject = core::ptr::null_mut();
    v_revisionEndpoint_1000_ = lean_ctor_get(v_cfg_999_, 3);
    lean_inc_ref(v_revisionEndpoint_1000_);
    return v_revisionEndpoint_1000_;
}
pub unsafe fn l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0___boxed(
    mut v_cfg_1001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1002_: *mut LeanObject = core::ptr::null_mut();
    v_res_1002_ = l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0(v_cfg_1001_);
    lean_dec_ref(v_cfg_1001_);
    return v_res_1002_;
}
pub unsafe fn l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__1(
    mut v_val_1003_: *mut LeanObject,
    mut v_cfg_1004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1006_: u8 = 0;
    let mut v_apiEndpoint_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_artifactEndpoint_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1011_: u8 = 0;
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1015_: u8 = 0;
    let mut v_unused_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_1005_ = lean_ctor_get(v_cfg_1004_, 0);
                v_kind_1006_ = lean_ctor_get_uint8(
                    v_cfg_1004_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_apiEndpoint_1007_ = lean_ctor_get(v_cfg_1004_, 1);
                v_artifactEndpoint_1008_ = lean_ctor_get(v_cfg_1004_, 2);
                v_isSharedCheck_1015_ = (!lean_is_exclusive(v_cfg_1004_)) as u8;
                if v_isSharedCheck_1015_ == 0 {
                    v_unused_1016_ = lean_ctor_get(v_cfg_1004_, 3);
                    lean_dec(v_unused_1016_);
                    v___x_1010_ = v_cfg_1004_;
                    v_isShared_1011_ = v_isSharedCheck_1015_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_artifactEndpoint_1008_);
                    lean_inc(v_apiEndpoint_1007_);
                    lean_inc(v_name_1005_);
                    lean_dec(v_cfg_1004_);
                    v___x_1010_ = lean_box(0);
                    v_isShared_1011_ = v_isSharedCheck_1015_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1011_ == 0 {
                    lean_ctor_set(v___x_1010_, 3, v_val_1003_);
                    v___x_1013_ = v___x_1010_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_name_1005_);
                    lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_apiEndpoint_1007_);
                    lean_ctor_set(v_reuseFailAlloc_1014_, 2, v_artifactEndpoint_1008_);
                    lean_ctor_set(v_reuseFailAlloc_1014_, 3, v_val_1003_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1014_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_kind_1006_,
                    );
                    v___x_1013_ = v_reuseFailAlloc_1014_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__2(
    mut v_f_1017_: *mut LeanObject,
    mut v_cfg_1018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1020_: u8 = 0;
    let mut v_apiEndpoint_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_artifactEndpoint_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_revisionEndpoint_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1026_: u8 = 0;
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1031_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_1019_ = lean_ctor_get(v_cfg_1018_, 0);
                v_kind_1020_ = lean_ctor_get_uint8(
                    v_cfg_1018_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_apiEndpoint_1021_ = lean_ctor_get(v_cfg_1018_, 1);
                v_artifactEndpoint_1022_ = lean_ctor_get(v_cfg_1018_, 2);
                v_revisionEndpoint_1023_ = lean_ctor_get(v_cfg_1018_, 3);
                v_isSharedCheck_1031_ = (!lean_is_exclusive(v_cfg_1018_)) as u8;
                if v_isSharedCheck_1031_ == 0 {
                    v___x_1025_ = v_cfg_1018_;
                    v_isShared_1026_ = v_isSharedCheck_1031_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_revisionEndpoint_1023_);
                    lean_inc(v_artifactEndpoint_1022_);
                    lean_inc(v_apiEndpoint_1021_);
                    lean_inc(v_name_1019_);
                    lean_dec(v_cfg_1018_);
                    v___x_1025_ = lean_box(0);
                    v_isShared_1026_ = v_isSharedCheck_1031_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1027_ = lean_apply_1(v_f_1017_, v_revisionEndpoint_1023_);
                if v_isShared_1026_ == 0 {
                    lean_ctor_set(v___x_1025_, 3, v___x_1027_);
                    v___x_1029_ = v___x_1025_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_name_1019_);
                    lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_apiEndpoint_1021_);
                    lean_ctor_set(v_reuseFailAlloc_1030_, 2, v_artifactEndpoint_1022_);
                    lean_ctor_set(v_reuseFailAlloc_1030_, 3, v___x_1027_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1030_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_kind_1020_,
                    );
                    v___x_1029_ = v_reuseFailAlloc_1030_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1029_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lake_CacheServiceConfig___fields___closed__4() -> *mut LeanObject {
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    v___x_1051_ = l_Lake_CacheServiceConfig___fields___closed__3;
    v___x_1052_ = l_Lake_CacheServiceConfig___fields___closed__0;
    v___x_1053_ = lean_array_push(v___x_1052_, v___x_1051_);
    return v___x_1053_;
}
pub unsafe fn _init_l_Lake_CacheServiceConfig___fields___closed__8() -> *mut LeanObject {
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    v___x_1061_ = l_Lake_CacheServiceConfig___fields___closed__7;
    v___x_1062_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig___fields___closed__4),
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig___fields___closed__4_once),
        _init_l_Lake_CacheServiceConfig___fields___closed__4,
    );
    v___x_1063_ = lean_array_push(v___x_1062_, v___x_1061_);
    return v___x_1063_;
}
pub unsafe fn _init_l_Lake_CacheServiceConfig___fields___closed__12() -> *mut LeanObject {
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    v___x_1071_ = l_Lake_CacheServiceConfig___fields___closed__11;
    v___x_1072_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig___fields___closed__8),
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig___fields___closed__8_once),
        _init_l_Lake_CacheServiceConfig___fields___closed__8,
    );
    v___x_1073_ = lean_array_push(v___x_1072_, v___x_1071_);
    return v___x_1073_;
}
pub unsafe fn _init_l_Lake_CacheServiceConfig___fields___closed__16() -> *mut LeanObject {
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    v___x_1081_ = l_Lake_CacheServiceConfig___fields___closed__15;
    v___x_1082_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig___fields___closed__12),
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig___fields___closed__12_once),
        _init_l_Lake_CacheServiceConfig___fields___closed__12,
    );
    v___x_1083_ = lean_array_push(v___x_1082_, v___x_1081_);
    return v___x_1083_;
}
pub unsafe fn _init_l_Lake_CacheServiceConfig___fields___closed__20() -> *mut LeanObject {
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    v___x_1091_ = l_Lake_CacheServiceConfig___fields___closed__19;
    v___x_1092_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig___fields___closed__16),
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig___fields___closed__16_once),
        _init_l_Lake_CacheServiceConfig___fields___closed__16,
    );
    v___x_1093_ = lean_array_push(v___x_1092_, v___x_1091_);
    return v___x_1093_;
}
pub unsafe fn _init_l_Lake_CacheServiceConfig___fields___closed__24() -> *mut LeanObject {
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    v___x_1101_ = l_Lake_CacheServiceConfig___fields___closed__23;
    v___x_1102_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig___fields___closed__20),
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig___fields___closed__20_once),
        _init_l_Lake_CacheServiceConfig___fields___closed__20,
    );
    v___x_1103_ = lean_array_push(v___x_1102_, v___x_1101_);
    return v___x_1103_;
}
pub unsafe fn _init_l_Lake_CacheServiceConfig___fields() -> *mut LeanObject {
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    v___x_1104_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig___fields___closed__24),
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig___fields___closed__24_once),
        _init_l_Lake_CacheServiceConfig___fields___closed__24,
    );
    return v___x_1104_;
}
pub unsafe fn _init_l_Lake_CacheServiceConfig_instConfigFields() -> *mut LeanObject {
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    v___x_1105_ = l_Lake_CacheServiceConfig___fields;
    return v___x_1105_;
}
pub unsafe fn l_Lake_CacheServiceConfig_instConfigInfo___lam__0(
    mut v_x1_1106_: *mut LeanObject,
    mut v_x2_1107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    v_name_1108_ = lean_ctor_get(v_x2_1107_, 0);
    lean_inc(v_name_1108_);
    v___x_1109_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_name_1108_,
        v_x2_1107_,
        v_x1_1106_,
    );
    return v___x_1109_;
}
pub unsafe fn _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0() -> *mut LeanObject {
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    v___x_1110_ = l_Lake_CacheServiceConfig___fields;
    v___x_1111_ = lean_array_get_size(v___x_1110_);
    return v___x_1111_;
}
pub unsafe fn _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__11() -> u8 {
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: u8 = 0;
    v___x_1131_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0,
    );
    v___x_1132_ = lean_unsigned_to_nat(0);
    v___x_1133_ = lean_nat_dec_lt(v___x_1132_, v___x_1131_);
    return v___x_1133_;
}
pub unsafe fn _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__12() -> *mut LeanObject {
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    v___x_1134_ = lean_unsigned_to_nat(0);
    v___x_1135_ = lean_box(1);
    v___x_1136_ = l_Lake_CacheServiceConfig___fields;
    v___x_1137_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1137_, 0, v___x_1136_);
    lean_ctor_set(v___x_1137_, 1, v___x_1135_);
    lean_ctor_set(v___x_1137_, 2, v___x_1134_);
    return v___x_1137_;
}
pub unsafe fn _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__14() -> u8 {
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: u8 = 0;
    v___x_1139_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0,
    );
    v___x_1140_ = lean_nat_dec_le(v___x_1139_, v___x_1139_);
    return v___x_1140_;
}
pub unsafe fn _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__15() -> usize {
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: usize = 0;
    v___x_1141_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0,
    );
    v___x_1142_ = lean_usize_of_nat(v___x_1141_);
    return v___x_1142_;
}
pub unsafe fn _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__16() -> *mut LeanObject {
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: usize = 0;
    let mut v___x_1145_: usize = 0;
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    v___x_1143_ = lean_box(1);
    v___x_1144_ = lean_usize_once(
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__15),
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__15_once),
        _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__15,
    );
    v___x_1145_ = 0usize;
    v___x_1146_ = l_Lake_CacheServiceConfig___fields;
    v___f_1147_ = l_Lake_CacheServiceConfig_instConfigInfo___closed__13;
    v___x_1148_ = l_Lake_CacheServiceConfig_instConfigInfo___closed__10;
    v___x_1149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_1148_,
        v___f_1147_,
        v___x_1146_,
        v___x_1145_,
        v___x_1144_,
        v___x_1143_,
    );
    return v___x_1149_;
}
pub unsafe fn _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__17() -> *mut LeanObject {
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    v___x_1150_ = lean_unsigned_to_nat(0);
    v___x_1151_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__16),
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__16_once),
        _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__16,
    );
    v___x_1152_ = l_Lake_CacheServiceConfig___fields;
    v___x_1153_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1153_, 0, v___x_1152_);
    lean_ctor_set(v___x_1153_, 1, v___x_1151_);
    lean_ctor_set(v___x_1153_, 2, v___x_1150_);
    return v___x_1153_;
}
pub unsafe fn _init_l_Lake_CacheServiceConfig_instConfigInfo() -> *mut LeanObject {
    let mut v___x_1154_: u8 = 0;
    v___x_1154_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__11),
        core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__11_once),
        _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__11,
    );
    if v___x_1154_ == 0 {
        let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
        v___x_1155_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__12),
            core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__12_once),
            _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__12,
        );
        return v___x_1155_;
    } else {
        let mut v___x_1156_: u8 = 0;
        v___x_1156_ = lean_uint8_once(
            core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__14),
            core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__14_once),
            _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__14,
        );
        if v___x_1156_ == 0 {
            if v___x_1154_ == 0 {
                let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
                v___x_1157_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__12),
                    core::ptr::addr_of_mut!(
                        l_Lake_CacheServiceConfig_instConfigInfo___closed__12_once
                    ),
                    _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__12,
                );
                return v___x_1157_;
            } else {
                let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
                v___x_1158_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__17),
                    core::ptr::addr_of_mut!(
                        l_Lake_CacheServiceConfig_instConfigInfo___closed__17_once
                    ),
                    _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__17,
                );
                return v___x_1158_;
            }
        } else {
            let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
            v___x_1159_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__17),
                core::ptr::addr_of_mut!(l_Lake_CacheServiceConfig_instConfigInfo___closed__17_once),
                _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__17,
            );
            return v___x_1159_;
        }
    }
}
pub unsafe fn l_Lake_CacheConfig_defaultService___proj___lam__0(
    mut v_cfg_1168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defaultService_1169_: *mut LeanObject = core::ptr::null_mut();
    v_defaultService_1169_ = lean_ctor_get(v_cfg_1168_, 0);
    lean_inc_ref(v_defaultService_1169_);
    return v_defaultService_1169_;
}
pub unsafe fn l_Lake_CacheConfig_defaultService___proj___lam__0___boxed(
    mut v_cfg_1170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1171_: *mut LeanObject = core::ptr::null_mut();
    v_res_1171_ = l_Lake_CacheConfig_defaultService___proj___lam__0(v_cfg_1170_);
    lean_dec_ref(v_cfg_1170_);
    return v_res_1171_;
}
pub unsafe fn l_Lake_CacheConfig_defaultService___proj___lam__1(
    mut v_val_1172_: *mut LeanObject,
    mut v_cfg_1173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defaultUploadService_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_services_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1178_: u8 = 0;
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1182_: u8 = 0;
    let mut v_unused_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defaultUploadService_1174_ = lean_ctor_get(v_cfg_1173_, 1);
                v_services_1175_ = lean_ctor_get(v_cfg_1173_, 2);
                v_isSharedCheck_1182_ = (!lean_is_exclusive(v_cfg_1173_)) as u8;
                if v_isSharedCheck_1182_ == 0 {
                    v_unused_1183_ = lean_ctor_get(v_cfg_1173_, 0);
                    lean_dec(v_unused_1183_);
                    v___x_1177_ = v_cfg_1173_;
                    v_isShared_1178_ = v_isSharedCheck_1182_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_services_1175_);
                    lean_inc(v_defaultUploadService_1174_);
                    lean_dec(v_cfg_1173_);
                    v___x_1177_ = lean_box(0);
                    v_isShared_1178_ = v_isSharedCheck_1182_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1178_ == 0 {
                    lean_ctor_set(v___x_1177_, 0, v_val_1172_);
                    v___x_1180_ = v___x_1177_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_val_1172_);
                    lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_defaultUploadService_1174_);
                    lean_ctor_set(v_reuseFailAlloc_1181_, 2, v_services_1175_);
                    v___x_1180_ = v_reuseFailAlloc_1181_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1180_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_CacheConfig_defaultService___proj___lam__2(
    mut v_f_1184_: *mut LeanObject,
    mut v_cfg_1185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defaultService_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defaultUploadService_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_services_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1191_: u8 = 0;
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1196_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defaultService_1186_ = lean_ctor_get(v_cfg_1185_, 0);
                v_defaultUploadService_1187_ = lean_ctor_get(v_cfg_1185_, 1);
                v_services_1188_ = lean_ctor_get(v_cfg_1185_, 2);
                v_isSharedCheck_1196_ = (!lean_is_exclusive(v_cfg_1185_)) as u8;
                if v_isSharedCheck_1196_ == 0 {
                    v___x_1190_ = v_cfg_1185_;
                    v_isShared_1191_ = v_isSharedCheck_1196_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_services_1188_);
                    lean_inc(v_defaultUploadService_1187_);
                    lean_inc(v_defaultService_1186_);
                    lean_dec(v_cfg_1185_);
                    v___x_1190_ = lean_box(0);
                    v_isShared_1191_ = v_isSharedCheck_1196_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1192_ = lean_apply_1(v_f_1184_, v_defaultService_1186_);
                if v_isShared_1191_ == 0 {
                    lean_ctor_set(v___x_1190_, 0, v___x_1192_);
                    v___x_1194_ = v___x_1190_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
                    lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_defaultUploadService_1187_);
                    lean_ctor_set(v_reuseFailAlloc_1195_, 2, v_services_1188_);
                    v___x_1194_ = v_reuseFailAlloc_1195_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1194_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_CacheConfig_defaultService___proj___lam__3(
    mut v_x_1197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    v___x_1198_ = l_Lake_instInhabitedCacheServiceConfig_default___closed__0;
    return v___x_1198_;
}
pub unsafe fn l_Lake_CacheConfig_defaultService___proj___lam__3___boxed(
    mut v_x_1199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1200_: *mut LeanObject = core::ptr::null_mut();
    v_res_1200_ = l_Lake_CacheConfig_defaultService___proj___lam__3(v_x_1199_);
    lean_dec_ref(v_x_1199_);
    return v_res_1200_;
}
pub unsafe fn l_Lake_CacheConfig_defaultUploadService___proj___lam__0(
    mut v_cfg_1212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defaultUploadService_1213_: *mut LeanObject = core::ptr::null_mut();
    v_defaultUploadService_1213_ = lean_ctor_get(v_cfg_1212_, 1);
    lean_inc_ref(v_defaultUploadService_1213_);
    return v_defaultUploadService_1213_;
}
pub unsafe fn l_Lake_CacheConfig_defaultUploadService___proj___lam__0___boxed(
    mut v_cfg_1214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1215_: *mut LeanObject = core::ptr::null_mut();
    v_res_1215_ = l_Lake_CacheConfig_defaultUploadService___proj___lam__0(v_cfg_1214_);
    lean_dec_ref(v_cfg_1214_);
    return v_res_1215_;
}
pub unsafe fn l_Lake_CacheConfig_defaultUploadService___proj___lam__1(
    mut v_val_1216_: *mut LeanObject,
    mut v_cfg_1217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defaultService_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_services_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1222_: u8 = 0;
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1226_: u8 = 0;
    let mut v_unused_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defaultService_1218_ = lean_ctor_get(v_cfg_1217_, 0);
                v_services_1219_ = lean_ctor_get(v_cfg_1217_, 2);
                v_isSharedCheck_1226_ = (!lean_is_exclusive(v_cfg_1217_)) as u8;
                if v_isSharedCheck_1226_ == 0 {
                    v_unused_1227_ = lean_ctor_get(v_cfg_1217_, 1);
                    lean_dec(v_unused_1227_);
                    v___x_1221_ = v_cfg_1217_;
                    v_isShared_1222_ = v_isSharedCheck_1226_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_services_1219_);
                    lean_inc(v_defaultService_1218_);
                    lean_dec(v_cfg_1217_);
                    v___x_1221_ = lean_box(0);
                    v_isShared_1222_ = v_isSharedCheck_1226_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1222_ == 0 {
                    lean_ctor_set(v___x_1221_, 1, v_val_1216_);
                    v___x_1224_ = v___x_1221_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_defaultService_1218_);
                    lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_val_1216_);
                    lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_services_1219_);
                    v___x_1224_ = v_reuseFailAlloc_1225_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1224_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_CacheConfig_defaultUploadService___proj___lam__2(
    mut v_f_1228_: *mut LeanObject,
    mut v_cfg_1229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defaultService_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defaultUploadService_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_services_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1235_: u8 = 0;
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defaultService_1230_ = lean_ctor_get(v_cfg_1229_, 0);
                v_defaultUploadService_1231_ = lean_ctor_get(v_cfg_1229_, 1);
                v_services_1232_ = lean_ctor_get(v_cfg_1229_, 2);
                v_isSharedCheck_1240_ = (!lean_is_exclusive(v_cfg_1229_)) as u8;
                if v_isSharedCheck_1240_ == 0 {
                    v___x_1234_ = v_cfg_1229_;
                    v_isShared_1235_ = v_isSharedCheck_1240_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_services_1232_);
                    lean_inc(v_defaultUploadService_1231_);
                    lean_inc(v_defaultService_1230_);
                    lean_dec(v_cfg_1229_);
                    v___x_1234_ = lean_box(0);
                    v_isShared_1235_ = v_isSharedCheck_1240_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1236_ = lean_apply_1(v_f_1228_, v_defaultUploadService_1231_);
                if v_isShared_1235_ == 0 {
                    lean_ctor_set(v___x_1234_, 1, v___x_1236_);
                    v___x_1238_ = v___x_1234_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_defaultService_1230_);
                    lean_ctor_set(v_reuseFailAlloc_1239_, 1, v___x_1236_);
                    lean_ctor_set(v_reuseFailAlloc_1239_, 2, v_services_1232_);
                    v___x_1238_ = v_reuseFailAlloc_1239_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1238_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_CacheConfig_services___proj___lam__0(
    mut v_cfg_1251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_services_1252_: *mut LeanObject = core::ptr::null_mut();
    v_services_1252_ = lean_ctor_get(v_cfg_1251_, 2);
    lean_inc_ref(v_services_1252_);
    return v_services_1252_;
}
pub unsafe fn l_Lake_CacheConfig_services___proj___lam__0___boxed(
    mut v_cfg_1253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1254_: *mut LeanObject = core::ptr::null_mut();
    v_res_1254_ = l_Lake_CacheConfig_services___proj___lam__0(v_cfg_1253_);
    lean_dec_ref(v_cfg_1253_);
    return v_res_1254_;
}
pub unsafe fn l_Lake_CacheConfig_services___proj___lam__1(
    mut v_val_1255_: *mut LeanObject,
    mut v_cfg_1256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defaultService_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defaultUploadService_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1261_: u8 = 0;
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1265_: u8 = 0;
    let mut v_unused_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defaultService_1257_ = lean_ctor_get(v_cfg_1256_, 0);
                v_defaultUploadService_1258_ = lean_ctor_get(v_cfg_1256_, 1);
                v_isSharedCheck_1265_ = (!lean_is_exclusive(v_cfg_1256_)) as u8;
                if v_isSharedCheck_1265_ == 0 {
                    v_unused_1266_ = lean_ctor_get(v_cfg_1256_, 2);
                    lean_dec(v_unused_1266_);
                    v___x_1260_ = v_cfg_1256_;
                    v_isShared_1261_ = v_isSharedCheck_1265_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_defaultUploadService_1258_);
                    lean_inc(v_defaultService_1257_);
                    lean_dec(v_cfg_1256_);
                    v___x_1260_ = lean_box(0);
                    v_isShared_1261_ = v_isSharedCheck_1265_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1261_ == 0 {
                    lean_ctor_set(v___x_1260_, 2, v_val_1255_);
                    v___x_1263_ = v___x_1260_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_defaultService_1257_);
                    lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_defaultUploadService_1258_);
                    lean_ctor_set(v_reuseFailAlloc_1264_, 2, v_val_1255_);
                    v___x_1263_ = v_reuseFailAlloc_1264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1263_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_CacheConfig_services___proj___lam__2(
    mut v_f_1267_: *mut LeanObject,
    mut v_cfg_1268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defaultService_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defaultUploadService_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_services_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1274_: u8 = 0;
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1279_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defaultService_1269_ = lean_ctor_get(v_cfg_1268_, 0);
                v_defaultUploadService_1270_ = lean_ctor_get(v_cfg_1268_, 1);
                v_services_1271_ = lean_ctor_get(v_cfg_1268_, 2);
                v_isSharedCheck_1279_ = (!lean_is_exclusive(v_cfg_1268_)) as u8;
                if v_isSharedCheck_1279_ == 0 {
                    v___x_1273_ = v_cfg_1268_;
                    v_isShared_1274_ = v_isSharedCheck_1279_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_services_1271_);
                    lean_inc(v_defaultUploadService_1270_);
                    lean_inc(v_defaultService_1269_);
                    lean_dec(v_cfg_1268_);
                    v___x_1273_ = lean_box(0);
                    v_isShared_1274_ = v_isSharedCheck_1279_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1275_ = lean_apply_1(v_f_1267_, v_services_1271_);
                if v_isShared_1274_ == 0 {
                    lean_ctor_set(v___x_1273_, 2, v___x_1275_);
                    v___x_1277_ = v___x_1273_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_defaultService_1269_);
                    lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_defaultUploadService_1270_);
                    lean_ctor_set(v_reuseFailAlloc_1278_, 2, v___x_1275_);
                    v___x_1277_ = v_reuseFailAlloc_1278_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1277_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_CacheConfig_services___proj___lam__3(
    mut v_x_1280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    v___x_1281_ = l_Lake_instInhabitedCacheConfig_default___closed__0;
    return v___x_1281_;
}
pub unsafe fn l_Lake_CacheConfig_services___proj___lam__3___boxed(
    mut v_x_1282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1283_: *mut LeanObject = core::ptr::null_mut();
    v_res_1283_ = l_Lake_CacheConfig_services___proj___lam__3(v_x_1282_);
    lean_dec_ref(v_x_1282_);
    return v_res_1283_;
}
pub unsafe fn _init_l_Lake_CacheConfig___fields___closed__3() -> *mut LeanObject {
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    v___x_1302_ = l_Lake_CacheConfig___fields___closed__2;
    v___x_1303_ = l_Lake_CacheServiceConfig___fields___closed__0;
    v___x_1304_ = lean_array_push(v___x_1303_, v___x_1302_);
    return v___x_1304_;
}
pub unsafe fn _init_l_Lake_CacheConfig___fields___closed__7() -> *mut LeanObject {
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    v___x_1312_ = l_Lake_CacheConfig___fields___closed__6;
    v___x_1313_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_CacheConfig___fields___closed__3),
        core::ptr::addr_of_mut!(l_Lake_CacheConfig___fields___closed__3_once),
        _init_l_Lake_CacheConfig___fields___closed__3,
    );
    v___x_1314_ = lean_array_push(v___x_1313_, v___x_1312_);
    return v___x_1314_;
}
pub unsafe fn _init_l_Lake_CacheConfig___fields___closed__13() -> *mut LeanObject {
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    v___x_1326_ = l_Lake_CacheConfig___fields___closed__12;
    v___x_1327_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_CacheConfig___fields___closed__7),
        core::ptr::addr_of_mut!(l_Lake_CacheConfig___fields___closed__7_once),
        _init_l_Lake_CacheConfig___fields___closed__7,
    );
    v___x_1328_ = lean_array_push(v___x_1327_, v___x_1326_);
    return v___x_1328_;
}
pub unsafe fn _init_l_Lake_CacheConfig___fields() -> *mut LeanObject {
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    v___x_1329_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_CacheConfig___fields___closed__13),
        core::ptr::addr_of_mut!(l_Lake_CacheConfig___fields___closed__13_once),
        _init_l_Lake_CacheConfig___fields___closed__13,
    );
    return v___x_1329_;
}
pub unsafe fn _init_l_Lake_CacheConfig_instConfigFields() -> *mut LeanObject {
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    v___x_1330_ = l_Lake_CacheConfig___fields;
    return v___x_1330_;
}
pub unsafe fn _init_l_Lake_CacheConfig_instConfigInfo___closed__0() -> *mut LeanObject {
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    v___x_1331_ = l_Lake_CacheConfig___fields;
    v___x_1332_ = lean_array_get_size(v___x_1331_);
    return v___x_1332_;
}
pub unsafe fn _init_l_Lake_CacheConfig_instConfigInfo___closed__1() -> u8 {
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: u8 = 0;
    v___x_1333_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_CacheConfig_instConfigInfo___closed__0,
    );
    v___x_1334_ = lean_unsigned_to_nat(0);
    v___x_1335_ = lean_nat_dec_lt(v___x_1334_, v___x_1333_);
    return v___x_1335_;
}
pub unsafe fn _init_l_Lake_CacheConfig_instConfigInfo___closed__2() -> *mut LeanObject {
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    v___x_1336_ = lean_unsigned_to_nat(0);
    v___x_1337_ = lean_box(1);
    v___x_1338_ = l_Lake_CacheConfig___fields;
    v___x_1339_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1339_, 0, v___x_1338_);
    lean_ctor_set(v___x_1339_, 1, v___x_1337_);
    lean_ctor_set(v___x_1339_, 2, v___x_1336_);
    return v___x_1339_;
}
pub unsafe fn _init_l_Lake_CacheConfig_instConfigInfo___closed__3() -> u8 {
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: u8 = 0;
    v___x_1340_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_CacheConfig_instConfigInfo___closed__0,
    );
    v___x_1341_ = lean_nat_dec_le(v___x_1340_, v___x_1340_);
    return v___x_1341_;
}
pub unsafe fn _init_l_Lake_CacheConfig_instConfigInfo___closed__4() -> usize {
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: usize = 0;
    v___x_1342_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_CacheConfig_instConfigInfo___closed__0,
    );
    v___x_1343_ = lean_usize_of_nat(v___x_1342_);
    return v___x_1343_;
}
pub unsafe fn _init_l_Lake_CacheConfig_instConfigInfo___closed__5() -> *mut LeanObject {
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: usize = 0;
    let mut v___x_1346_: usize = 0;
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    v___x_1344_ = lean_box(1);
    v___x_1345_ = lean_usize_once(
        core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__4),
        core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__4_once),
        _init_l_Lake_CacheConfig_instConfigInfo___closed__4,
    );
    v___x_1346_ = 0usize;
    v___x_1347_ = l_Lake_CacheConfig___fields;
    v___f_1348_ = l_Lake_CacheServiceConfig_instConfigInfo___closed__13;
    v___x_1349_ = l_Lake_CacheServiceConfig_instConfigInfo___closed__10;
    v___x_1350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_1349_,
        v___f_1348_,
        v___x_1347_,
        v___x_1346_,
        v___x_1345_,
        v___x_1344_,
    );
    return v___x_1350_;
}
pub unsafe fn _init_l_Lake_CacheConfig_instConfigInfo___closed__6() -> *mut LeanObject {
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    v___x_1351_ = lean_unsigned_to_nat(0);
    v___x_1352_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__5),
        core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__5_once),
        _init_l_Lake_CacheConfig_instConfigInfo___closed__5,
    );
    v___x_1353_ = l_Lake_CacheConfig___fields;
    v___x_1354_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1354_, 0, v___x_1353_);
    lean_ctor_set(v___x_1354_, 1, v___x_1352_);
    lean_ctor_set(v___x_1354_, 2, v___x_1351_);
    return v___x_1354_;
}
pub unsafe fn _init_l_Lake_CacheConfig_instConfigInfo() -> *mut LeanObject {
    let mut v___x_1355_: u8 = 0;
    v___x_1355_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__1),
        core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__1_once),
        _init_l_Lake_CacheConfig_instConfigInfo___closed__1,
    );
    if v___x_1355_ == 0 {
        let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
        v___x_1356_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__2),
            core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__2_once),
            _init_l_Lake_CacheConfig_instConfigInfo___closed__2,
        );
        return v___x_1356_;
    } else {
        let mut v___x_1357_: u8 = 0;
        v___x_1357_ = lean_uint8_once(
            core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__3),
            core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__3_once),
            _init_l_Lake_CacheConfig_instConfigInfo___closed__3,
        );
        if v___x_1357_ == 0 {
            if v___x_1355_ == 0 {
                let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
                v___x_1358_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__2),
                    core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__2_once),
                    _init_l_Lake_CacheConfig_instConfigInfo___closed__2,
                );
                return v___x_1358_;
            } else {
                let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
                v___x_1359_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__6),
                    core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__6_once),
                    _init_l_Lake_CacheConfig_instConfigInfo___closed__6,
                );
                return v___x_1359_;
            }
        } else {
            let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
            v___x_1360_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__6),
                core::ptr::addr_of_mut!(l_Lake_CacheConfig_instConfigInfo___closed__6_once),
                _init_l_Lake_CacheConfig_instConfigInfo___closed__6,
            );
            return v___x_1360_;
        }
    }
}
pub unsafe fn l_Lake_LakeConfig_cache___proj___lam__0(
    mut v_cfg_1364_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_cfg_1364_);
    return v_cfg_1364_;
}
pub unsafe fn l_Lake_LakeConfig_cache___proj___lam__0___boxed(
    mut v_cfg_1365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1366_: *mut LeanObject = core::ptr::null_mut();
    v_res_1366_ = l_Lake_LakeConfig_cache___proj___lam__0(v_cfg_1365_);
    lean_dec_ref(v_cfg_1365_);
    return v_res_1366_;
}
pub unsafe fn l_Lake_LakeConfig_cache___proj___lam__1(
    mut v_val_1367_: *mut LeanObject,
    mut v_cfg_1368_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_val_1367_);
    return v_val_1367_;
}
pub unsafe fn l_Lake_LakeConfig_cache___proj___lam__1___boxed(
    mut v_val_1369_: *mut LeanObject,
    mut v_cfg_1370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1371_: *mut LeanObject = core::ptr::null_mut();
    v_res_1371_ = l_Lake_LakeConfig_cache___proj___lam__1(v_val_1369_, v_cfg_1370_);
    lean_dec_ref(v_cfg_1370_);
    lean_dec_ref(v_val_1369_);
    return v_res_1371_;
}
pub unsafe fn l_Lake_LakeConfig_cache___proj___lam__2(
    mut v_f_1372_: *mut LeanObject,
    mut v_cfg_1373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    v___x_1374_ = lean_apply_1(v_f_1372_, v_cfg_1373_);
    return v___x_1374_;
}
pub unsafe fn l_Lake_LakeConfig_cache___proj___lam__3(
    mut v_x_1375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    v___x_1376_ = l_Lake_instInhabitedCacheConfig_default___closed__1;
    return v___x_1376_;
}
pub unsafe fn l_Lake_LakeConfig_cache___proj___lam__3___boxed(
    mut v_x_1377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1378_: *mut LeanObject = core::ptr::null_mut();
    v_res_1378_ = l_Lake_LakeConfig_cache___proj___lam__3(v_x_1377_);
    lean_dec_ref(v_x_1377_);
    return v_res_1378_;
}
pub unsafe fn _init_l_Lake_LakeConfig___fields___closed__3() -> *mut LeanObject {
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    v___x_1397_ = l_Lake_LakeConfig___fields___closed__2;
    v___x_1398_ = l_Lake_CacheServiceConfig___fields___closed__0;
    v___x_1399_ = lean_array_push(v___x_1398_, v___x_1397_);
    return v___x_1399_;
}
pub unsafe fn _init_l_Lake_LakeConfig___fields() -> *mut LeanObject {
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    v___x_1400_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LakeConfig___fields___closed__3),
        core::ptr::addr_of_mut!(l_Lake_LakeConfig___fields___closed__3_once),
        _init_l_Lake_LakeConfig___fields___closed__3,
    );
    return v___x_1400_;
}
pub unsafe fn _init_l_Lake_LakeConfig_instConfigFields() -> *mut LeanObject {
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    v___x_1401_ = l_Lake_LakeConfig___fields;
    return v___x_1401_;
}
pub unsafe fn _init_l_Lake_LakeConfig_instConfigInfo___closed__0() -> *mut LeanObject {
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    v___x_1402_ = l_Lake_LakeConfig___fields;
    v___x_1403_ = lean_array_get_size(v___x_1402_);
    return v___x_1403_;
}
pub unsafe fn _init_l_Lake_LakeConfig_instConfigInfo___closed__1() -> u8 {
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: u8 = 0;
    v___x_1404_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LakeConfig_instConfigInfo___closed__0,
    );
    v___x_1405_ = lean_unsigned_to_nat(0);
    v___x_1406_ = lean_nat_dec_lt(v___x_1405_, v___x_1404_);
    return v___x_1406_;
}
pub unsafe fn _init_l_Lake_LakeConfig_instConfigInfo___closed__2() -> *mut LeanObject {
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    v___x_1407_ = lean_unsigned_to_nat(0);
    v___x_1408_ = lean_box(1);
    v___x_1409_ = l_Lake_LakeConfig___fields;
    v___x_1410_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1410_, 0, v___x_1409_);
    lean_ctor_set(v___x_1410_, 1, v___x_1408_);
    lean_ctor_set(v___x_1410_, 2, v___x_1407_);
    return v___x_1410_;
}
pub unsafe fn _init_l_Lake_LakeConfig_instConfigInfo___closed__3() -> u8 {
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: u8 = 0;
    v___x_1411_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LakeConfig_instConfigInfo___closed__0,
    );
    v___x_1412_ = lean_nat_dec_le(v___x_1411_, v___x_1411_);
    return v___x_1412_;
}
pub unsafe fn _init_l_Lake_LakeConfig_instConfigInfo___closed__4() -> usize {
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: usize = 0;
    v___x_1413_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LakeConfig_instConfigInfo___closed__0,
    );
    v___x_1414_ = lean_usize_of_nat(v___x_1413_);
    return v___x_1414_;
}
pub unsafe fn _init_l_Lake_LakeConfig_instConfigInfo___closed__5() -> *mut LeanObject {
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: usize = 0;
    let mut v___x_1417_: usize = 0;
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    v___x_1415_ = lean_box(1);
    v___x_1416_ = lean_usize_once(
        core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__4),
        core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__4_once),
        _init_l_Lake_LakeConfig_instConfigInfo___closed__4,
    );
    v___x_1417_ = 0usize;
    v___x_1418_ = l_Lake_LakeConfig___fields;
    v___f_1419_ = l_Lake_CacheServiceConfig_instConfigInfo___closed__13;
    v___x_1420_ = l_Lake_CacheServiceConfig_instConfigInfo___closed__10;
    v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_1420_,
        v___f_1419_,
        v___x_1418_,
        v___x_1417_,
        v___x_1416_,
        v___x_1415_,
    );
    return v___x_1421_;
}
pub unsafe fn _init_l_Lake_LakeConfig_instConfigInfo___closed__6() -> *mut LeanObject {
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    v___x_1422_ = lean_unsigned_to_nat(0);
    v___x_1423_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__5),
        core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__5_once),
        _init_l_Lake_LakeConfig_instConfigInfo___closed__5,
    );
    v___x_1424_ = l_Lake_LakeConfig___fields;
    v___x_1425_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1425_, 0, v___x_1424_);
    lean_ctor_set(v___x_1425_, 1, v___x_1423_);
    lean_ctor_set(v___x_1425_, 2, v___x_1422_);
    return v___x_1425_;
}
pub unsafe fn _init_l_Lake_LakeConfig_instConfigInfo() -> *mut LeanObject {
    let mut v___x_1426_: u8 = 0;
    v___x_1426_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__1),
        core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__1_once),
        _init_l_Lake_LakeConfig_instConfigInfo___closed__1,
    );
    if v___x_1426_ == 0 {
        let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
        v___x_1427_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__2),
            core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__2_once),
            _init_l_Lake_LakeConfig_instConfigInfo___closed__2,
        );
        return v___x_1427_;
    } else {
        let mut v___x_1428_: u8 = 0;
        v___x_1428_ = lean_uint8_once(
            core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__3),
            core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__3_once),
            _init_l_Lake_LakeConfig_instConfigInfo___closed__3,
        );
        if v___x_1428_ == 0 {
            if v___x_1426_ == 0 {
                let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
                v___x_1429_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__2),
                    core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__2_once),
                    _init_l_Lake_LakeConfig_instConfigInfo___closed__2,
                );
                return v___x_1429_;
            } else {
                let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
                v___x_1430_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__6),
                    core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__6_once),
                    _init_l_Lake_LakeConfig_instConfigInfo___closed__6,
                );
                return v___x_1430_;
            }
        } else {
            let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
            v___x_1431_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__6),
                core::ptr::addr_of_mut!(l_Lake_LakeConfig_instConfigInfo___closed__6_once),
                _init_l_Lake_LakeConfig_instConfigInfo___closed__6,
            );
            return v___x_1431_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_LakeConfig(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Cache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_MetaClasses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_instInhabitedCacheServiceKind_default =
        _init_l_Lake_instInhabitedCacheServiceKind_default();
    l_Lake_instInhabitedCacheServiceKind = _init_l_Lake_instInhabitedCacheServiceKind();
    l_Lake_CacheServiceConfig___fields = _init_l_Lake_CacheServiceConfig___fields();
    lean_mark_persistent(l_Lake_CacheServiceConfig___fields);
    l_Lake_CacheServiceConfig_instConfigFields = _init_l_Lake_CacheServiceConfig_instConfigFields();
    lean_mark_persistent(l_Lake_CacheServiceConfig_instConfigFields);
    l_Lake_CacheServiceConfig_instConfigInfo = _init_l_Lake_CacheServiceConfig_instConfigInfo();
    lean_mark_persistent(l_Lake_CacheServiceConfig_instConfigInfo);
    l_Lake_CacheConfig___fields = _init_l_Lake_CacheConfig___fields();
    lean_mark_persistent(l_Lake_CacheConfig___fields);
    l_Lake_CacheConfig_instConfigFields = _init_l_Lake_CacheConfig_instConfigFields();
    lean_mark_persistent(l_Lake_CacheConfig_instConfigFields);
    l_Lake_CacheConfig_instConfigInfo = _init_l_Lake_CacheConfig_instConfigInfo();
    lean_mark_persistent(l_Lake_CacheConfig_instConfigInfo);
    l_Lake_LakeConfig___fields = _init_l_Lake_LakeConfig___fields();
    lean_mark_persistent(l_Lake_LakeConfig___fields);
    l_Lake_LakeConfig_instConfigFields = _init_l_Lake_LakeConfig_instConfigFields();
    lean_mark_persistent(l_Lake_LakeConfig_instConfigFields);
    l_Lake_LakeConfig_instConfigInfo = _init_l_Lake_LakeConfig_instConfigInfo();
    lean_mark_persistent(l_Lake_LakeConfig_instConfigInfo);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_LakeConfig(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Config_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_LakeConfig(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Cache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_MetaClasses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LakeConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_LakeConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_LakeConfig(builtin);
}
