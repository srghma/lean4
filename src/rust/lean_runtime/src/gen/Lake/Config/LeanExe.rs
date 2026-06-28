// Lean compiler output
// Module: Lake.Config.LeanExe
// Imports: Lake.Config.Module
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold, l_Array_append___redArg,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Init::System::FilePath::{
    l_System_FilePath_addExtension, l_System_FilePath_exeExtension, l_System_FilePath_normalize,
    l_System_FilePath_withExtension,
};
use crate::r#gen::Init::System::Platform::l_System_Platform_isWindows;
use crate::r#gen::Lake::Build::Facets::l_Lake_LeanLib_leanArtsFacet;
use crate::r#gen::Lake::Config::Kinds::l_Lake_LeanExe_keyword;
use crate::r#gen::Lake::Config::Module::{
    initialize_Lake_Config_Module, l_Lake_LeanLib_findModuleBySrc_x3f,
    l_Lake_Package_findModule_x3f, runtime_initialize_Lake_Config_Module,
};
use crate::r#gen::Lake::Config::Package::l_Lake_Package_findTargetDecl_x3f;
use crate::r#gen::Lake::Util::FilePath::l_Lake_joinRelative;
use crate::r#gen::Lean::Util::Path::l_Lean_modToFilePath;
use crate::lean_imports_rs::Init::Core::lean_strict_and;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lake_Package_leanExes___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lake_Package_leanExes___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanExes___closed__0_value) as *mut LeanObject;
pub static l_Lake_Package_leanExes___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Package_leanExes___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanExes___closed__1_value) as *mut LeanObject;
pub static l_Lake_Package_leanExes___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Package_leanExes___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanExes___closed__2_value) as *mut LeanObject;
pub static l_Lake_Package_leanExes___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Package_leanExes___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanExes___closed__3_value) as *mut LeanObject;
pub static l_Lake_Package_leanExes___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Package_leanExes___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanExes___closed__4_value) as *mut LeanObject;
pub static l_Lake_Package_leanExes___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Package_leanExes___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanExes___closed__5_value) as *mut LeanObject;
pub static l_Lake_Package_leanExes___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Package_leanExes___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanExes___closed__6_value) as *mut LeanObject;
pub static l_Lake_Package_leanExes___closed__7_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Package_leanExes___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanExes___closed__7_value) as *mut LeanObject;
pub static l_Lake_Package_leanExes___closed__8_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Package_leanExes___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_leanExes___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Package_leanExes___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanExes___closed__8_value) as *mut LeanObject;
pub static l_Lake_Package_leanExes___closed__9_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Package_leanExes___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_leanExes___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_leanExes___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_leanExes___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_leanExes___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Package_leanExes___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanExes___closed__9_value) as *mut LeanObject;
pub static l_Lake_Package_leanExes___closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Package_leanExes___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_leanExes___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Package_leanExes___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanExes___closed__10_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1: usize = 0;
static mut l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExe_isRootSrc_x3f___closed__0_value: LeanStringObject<1> = LeanStringObject {
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
static mut l_Lake_LeanExe_isRootSrc_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_isRootSrc_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanExe_linkArgs___closed__0_value: LeanStringObject<20> = LeanStringObject {
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
        45, 87, 108, 44, 45, 45, 119, 104, 111, 108, 101, 45, 97, 114, 99, 104, 105, 118, 101, 0,
    ],
};
static mut l_Lake_LeanExe_linkArgs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_linkArgs___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanExe_linkArgs___closed__1_value: LeanStringObject<15> = LeanStringObject {
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
        45, 108, 108, 101, 97, 110, 109, 97, 110, 105, 102, 101, 115, 116, 0,
    ],
};
static mut l_Lake_LeanExe_linkArgs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_linkArgs___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanExe_linkArgs___closed__2_value: LeanStringObject<23> = LeanStringObject {
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
        45, 87, 108, 44, 45, 45, 110, 111, 45, 119, 104, 111, 108, 101, 45, 97, 114, 99, 104, 105,
        118, 101, 0,
    ],
};
static mut l_Lake_LeanExe_linkArgs___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_linkArgs___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanExe_linkArgs___closed__3_value: LeanArrayObject<3> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 3,
    m_capacity: 3,
    m_data: [
        core::ptr::addr_of!(l_Lake_LeanExe_linkArgs___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExe_linkArgs___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExe_linkArgs___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lake_LeanExe_linkArgs___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_linkArgs___closed__3_value) as *mut LeanObject;
pub static l_Lake_LeanExe_linkArgs___closed__4_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [45, 114, 100, 121, 110, 97, 109, 105, 99, 0],
};
static mut l_Lake_LeanExe_linkArgs___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_linkArgs___closed__4_value) as *mut LeanObject;
pub static l_Lake_LeanExe_linkArgs___closed__5_value: LeanArrayObject<1> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 1,
    m_capacity: 1,
    m_data: [core::ptr::addr_of!(l_Lake_LeanExe_linkArgs___closed__4_value) as *mut LeanObject],
};
static mut l_Lake_LeanExe_linkArgs___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_linkArgs___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 97, 110, 95, 108, 105, 98, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___closed__0_value) as *mut LeanObject,12295998048739818339 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lake_Package_leanExes___lam__0(
    mut v___x_480_: *mut LeanObject,
    mut v_self_481_: *mut LeanObject,
    mut v_x1_482_: *mut LeanObject,
    mut v_x2_483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: u8 = 0;
    v_name_484_ = lean_ctor_get(v_x2_483_, 1);
    v_kind_485_ = lean_ctor_get(v_x2_483_, 2);
    v_config_486_ = lean_ctor_get(v_x2_483_, 3);
    v___x_487_ = lean_name_eq(v_kind_485_, v___x_480_);
    if v___x_487_ == 0 {
        lean_dec_ref(v_self_481_);
        return v_x1_482_;
    } else {
        let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_486_);
        lean_inc(v_name_484_);
        v___x_488_ = lean_alloc_ctor(0, 3, (0) as u32);
        lean_ctor_set(v___x_488_, 0, v_self_481_);
        lean_ctor_set(v___x_488_, 1, v_name_484_);
        lean_ctor_set(v___x_488_, 2, v_config_486_);
        v___x_489_ = lean_array_push(v_x1_482_, v___x_488_);
        return v___x_489_;
    }
}
pub unsafe fn l_Lake_Package_leanExes___lam__0___boxed(
    mut v___x_490_: *mut LeanObject,
    mut v_self_491_: *mut LeanObject,
    mut v_x1_492_: *mut LeanObject,
    mut v_x2_493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_494_: *mut LeanObject = core::ptr::null_mut();
    v_res_494_ = l_Lake_Package_leanExes___lam__0(v___x_490_, v_self_491_, v_x1_492_, v_x2_493_);
    lean_dec_ref(v_x2_493_);
    lean_dec(v___x_490_);
    return v_res_494_;
}
pub unsafe fn l_Lake_Package_leanExes(mut v_self_516_: *mut LeanObject) -> *mut LeanObject {
    let mut v_targetDecls_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_522_: u8 = 0;
    v_targetDecls_517_ = lean_ctor_get(v_self_516_, 14);
    lean_inc_ref(v_targetDecls_517_);
    v___x_518_ = lean_unsigned_to_nat(0);
    v___x_519_ = l_Lake_Package_leanExes___closed__0;
    v___x_520_ = lean_array_get_size(v_targetDecls_517_);
    v___x_521_ = l_Lake_Package_leanExes___closed__10;
    v___x_522_ = lean_nat_dec_lt(v___x_518_, v___x_520_);
    if v___x_522_ == 0 {
        lean_dec_ref(v_targetDecls_517_);
        lean_dec_ref(v_self_516_);
        return v___x_519_;
    } else {
        let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_525_: u8 = 0;
        v___x_523_ = l_Lake_LeanExe_keyword;
        v___f_524_ = lean_alloc_closure(
            l_Lake_Package_leanExes___lam__0___boxed as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_524_, 0, v___x_523_);
        lean_closure_set(v___f_524_, 1, v_self_516_);
        v___x_525_ = lean_nat_dec_le(v___x_520_, v___x_520_);
        if v___x_525_ == 0 {
            if v___x_522_ == 0 {
                lean_dec_ref(v___f_524_);
                lean_dec_ref(v_targetDecls_517_);
                return v___x_519_;
            } else {
                let mut v___x_526_: usize = 0;
                let mut v___x_527_: usize = 0;
                let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
                v___x_526_ = 0usize;
                v___x_527_ = lean_usize_of_nat(v___x_520_);
                v___x_528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_521_,
                    v___f_524_,
                    v_targetDecls_517_,
                    v___x_526_,
                    v___x_527_,
                    v___x_519_,
                );
                return v___x_528_;
            }
        } else {
            let mut v___x_529_: usize = 0;
            let mut v___x_530_: usize = 0;
            let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
            v___x_529_ = 0usize;
            v___x_530_ = lean_usize_of_nat(v___x_520_);
            v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v___x_521_,
                v___f_524_,
                v_targetDecls_517_,
                v___x_529_,
                v___x_530_,
                v___x_519_,
            );
            return v___x_531_;
        }
    }
}
pub unsafe fn l_Lake_Package_findLeanExe_x3f(
    mut v_name_532_: *mut LeanObject,
    mut v_self_533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_539_: u8 = 0;
    let mut v_name_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: u8 = 0;
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_550_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_534_ = l_Lake_Package_findTargetDecl_x3f(v_name_532_, v_self_533_);
                if lean_obj_tag(v___x_534_) == 0 {
                    lean_dec_ref(v_self_533_);
                    v___x_535_ = lean_box(0);
                    return v___x_535_;
                } else {
                    v_val_536_ = lean_ctor_get(v___x_534_, 0);
                    v_isSharedCheck_550_ = (!lean_is_exclusive(v___x_534_)) as u8;
                    if v_isSharedCheck_550_ == 0 {
                        v___x_538_ = v___x_534_;
                        v_isShared_539_ = v_isSharedCheck_550_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_536_);
                        lean_dec(v___x_534_);
                        v___x_538_ = lean_box(0);
                        v_isShared_539_ = v_isSharedCheck_550_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_name_540_ = lean_ctor_get(v_val_536_, 1);
                lean_inc(v_name_540_);
                v_kind_541_ = lean_ctor_get(v_val_536_, 2);
                lean_inc(v_kind_541_);
                v_config_542_ = lean_ctor_get(v_val_536_, 3);
                lean_inc(v_config_542_);
                lean_dec(v_val_536_);
                v___x_543_ = l_Lake_LeanExe_keyword;
                v___x_544_ = lean_name_eq(v_kind_541_, v___x_543_);
                lean_dec(v_kind_541_);
                if v___x_544_ == 0 {
                    lean_dec(v_config_542_);
                    lean_dec(v_name_540_);
                    lean_del_object(v___x_538_);
                    lean_dec_ref(v_self_533_);
                    v___x_545_ = lean_box(0);
                    return v___x_545_;
                } else {
                    v___x_546_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_546_, 0, v_self_533_);
                    lean_ctor_set(v___x_546_, 1, v_name_540_);
                    lean_ctor_set(v___x_546_, 2, v_config_542_);
                    if v_isShared_539_ == 0 {
                        lean_ctor_set(v___x_538_, 0, v___x_546_);
                        v___x_548_ = v___x_538_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_546_);
                        v___x_548_ = v_reuseFailAlloc_549_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_548_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_findLeanExe_x3f___boxed(
    mut v_name_551_: *mut LeanObject,
    mut v_self_552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_553_: *mut LeanObject = core::ptr::null_mut();
    v_res_553_ = l_Lake_Package_findLeanExe_x3f(v_name_551_, v_self_552_);
    lean_dec(v_name_551_);
    return v_res_553_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0(
    mut v_sz_554_: usize,
    mut v_i_555_: usize,
    mut v_bs_556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_557_: u8 = 0;
    let mut v_v_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: usize = 0;
    let mut v___x_563_: usize = 0;
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_557_ = lean_usize_dec_lt(v_i_555_, v_sz_554_);
                if v___x_557_ == 0 {
                    return v_bs_556_;
                } else {
                    v_v_558_ = lean_array_uget(v_bs_556_, v_i_555_);
                    v___x_559_ = lean_unsigned_to_nat(0);
                    v_bs_x27_560_ = lean_array_uset(v_bs_556_, v_i_555_, v___x_559_);
                    v___x_561_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_561_, 0, v_v_558_);
                    v___x_562_ = 1usize;
                    v___x_563_ = lean_usize_add(v_i_555_, v___x_562_);
                    v___x_564_ = lean_array_uset(v_bs_x27_560_, v_i_555_, v___x_561_);
                    v_i_555_ = v___x_563_;
                    v_bs_556_ = v___x_564_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0___boxed(
    mut v_sz_566_: *mut LeanObject,
    mut v_i_567_: *mut LeanObject,
    mut v_bs_568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_569_: usize = 0;
    let mut v_i_boxed_570_: usize = 0;
    let mut v_res_571_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_569_ = lean_unbox_usize(v_sz_566_);
    lean_dec(v_sz_566_);
    v_i_boxed_570_ = lean_unbox_usize(v_i_567_);
    lean_dec(v_i_567_);
    v_res_571_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0(v_sz_boxed_569_, v_i_boxed_570_, v_bs_568_);
    return v_res_571_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1() -> usize {
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_575_: usize = 0;
    v___x_574_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__0;
    v_sz_575_ = lean_array_size(v___x_574_);
    return v_sz_575_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: usize = 0;
    let mut v_sz_578_: usize = 0;
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    v___x_576_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__0;
    v___x_577_ = 0usize;
    v_sz_578_ = lean_usize_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1_once),
        _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1,
    );
    v___x_579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0(v_sz_578_, v___x_577_, v___x_576_);
    return v___x_579_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    v___x_580_ = l_Lake_LeanLib_leanArtsFacet;
    v___x_581_ = lean_unsigned_to_nat(1);
    v___x_582_ = lean_mk_empty_array_with_capacity(v___x_581_);
    v___x_583_ = lean_array_push(v___x_582_, v___x_580_);
    return v___x_583_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanLibConfig___redArg(
    mut v_self_584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toLeanConfig_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exeName_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needs_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: u8 = 0;
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    v_toLeanConfig_585_ = lean_ctor_get(v_self_584_, 0);
    v_srcDir_586_ = lean_ctor_get(v_self_584_, 1);
    v_exeName_587_ = lean_ctor_get(v_self_584_, 3);
    v_needs_588_ = lean_ctor_get(v_self_584_, 4);
    v_extraDepTargets_589_ = lean_ctor_get(v_self_584_, 5);
    v_nativeFacets_590_ = lean_ctor_get(v_self_584_, 6);
    v___x_591_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__0;
    v___x_592_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2_once),
        _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2,
    );
    v___x_593_ = 0;
    v___x_594_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3_once),
        _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3,
    );
    lean_inc_ref(v_nativeFacets_590_);
    lean_inc_ref(v_extraDepTargets_589_);
    lean_inc_ref(v_needs_588_);
    lean_inc_ref(v_exeName_587_);
    lean_inc_ref(v_srcDir_586_);
    lean_inc_ref(v_toLeanConfig_585_);
    v___x_595_ = lean_alloc_ctor(0, 9, (3) as u32);
    lean_ctor_set(v___x_595_, 0, v_toLeanConfig_585_);
    lean_ctor_set(v___x_595_, 1, v_srcDir_586_);
    lean_ctor_set(v___x_595_, 2, v___x_591_);
    lean_ctor_set(v___x_595_, 3, v___x_592_);
    lean_ctor_set(v___x_595_, 4, v_exeName_587_);
    lean_ctor_set(v___x_595_, 5, v_needs_588_);
    lean_ctor_set(v___x_595_, 6, v_extraDepTargets_589_);
    lean_ctor_set(v___x_595_, 7, v___x_594_);
    lean_ctor_set(v___x_595_, 8, v_nativeFacets_590_);
    lean_ctor_set_uint8(
        v___x_595_,
        (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
        v___x_593_,
    );
    lean_ctor_set_uint8(
        v___x_595_,
        (core::mem::size_of::<*mut LeanObject>() * 9 + 1) as u32,
        v___x_593_,
    );
    lean_ctor_set_uint8(
        v___x_595_,
        (core::mem::size_of::<*mut LeanObject>() * 9 + 2) as u32,
        v___x_593_,
    );
    return v___x_595_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanLibConfig___redArg___boxed(
    mut v_self_596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_597_: *mut LeanObject = core::ptr::null_mut();
    v_res_597_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_self_596_);
    lean_dec_ref(v_self_596_);
    return v_res_597_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanLibConfig(
    mut v_n_598_: *mut LeanObject,
    mut v_self_599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    v___x_600_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_self_599_);
    return v___x_600_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanLibConfig___boxed(
    mut v_n_601_: *mut LeanObject,
    mut v_self_602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_603_: *mut LeanObject = core::ptr::null_mut();
    v_res_603_ = l_Lake_LeanExeConfig_toLeanLibConfig(v_n_601_, v_self_602_);
    lean_dec_ref(v_self_602_);
    lean_dec(v_n_601_);
    return v_res_603_;
}
pub unsafe fn l_Lake_LeanExe_config(mut v_self_604_: *mut LeanObject) -> *mut LeanObject {
    let mut v_config_605_: *mut LeanObject = core::ptr::null_mut();
    v_config_605_ = lean_ctor_get(v_self_604_, 2);
    lean_inc(v_config_605_);
    return v_config_605_;
}
pub unsafe fn l_Lake_LeanExe_config___boxed(mut v_self_606_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_607_: *mut LeanObject = core::ptr::null_mut();
    v_res_607_ = l_Lake_LeanExe_config(v_self_606_);
    lean_dec_ref(v_self_606_);
    return v_res_607_;
}
pub unsafe fn l_Lake_LeanExe_toLeanLib(mut v_self_608_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_614_: u8 = 0;
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_619_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_609_ = lean_ctor_get(v_self_608_, 0);
                v_name_610_ = lean_ctor_get(v_self_608_, 1);
                v_config_611_ = lean_ctor_get(v_self_608_, 2);
                v_isSharedCheck_619_ = (!lean_is_exclusive(v_self_608_)) as u8;
                if v_isSharedCheck_619_ == 0 {
                    v___x_613_ = v_self_608_;
                    v_isShared_614_ = v_isSharedCheck_619_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_config_611_);
                    lean_inc(v_name_610_);
                    lean_inc(v_pkg_609_);
                    lean_dec(v_self_608_);
                    v___x_613_ = lean_box(0);
                    v_isShared_614_ = v_isSharedCheck_619_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_615_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_611_);
                lean_dec(v_config_611_);
                if v_isShared_614_ == 0 {
                    lean_ctor_set(v___x_613_, 2, v___x_615_);
                    v___x_617_ = v___x_613_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_618_, 0, v_pkg_609_);
                    lean_ctor_set(v_reuseFailAlloc_618_, 1, v_name_610_);
                    lean_ctor_set(v_reuseFailAlloc_618_, 2, v___x_615_);
                    v___x_617_ = v_reuseFailAlloc_618_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_617_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExe_root(mut v_self_620_: *mut LeanObject) -> *mut LeanObject {
    let mut v_config_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_626_: u8 = 0;
    let mut v_root_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_633_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_621_ = lean_ctor_get(v_self_620_, 2);
                v_pkg_622_ = lean_ctor_get(v_self_620_, 0);
                v_name_623_ = lean_ctor_get(v_self_620_, 1);
                v_isSharedCheck_633_ = (!lean_is_exclusive(v_self_620_)) as u8;
                if v_isSharedCheck_633_ == 0 {
                    v___x_625_ = v_self_620_;
                    v_isShared_626_ = v_isSharedCheck_633_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_config_621_);
                    lean_inc(v_name_623_);
                    lean_inc(v_pkg_622_);
                    lean_dec(v_self_620_);
                    v___x_625_ = lean_box(0);
                    v_isShared_626_ = v_isSharedCheck_633_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_root_627_ = lean_ctor_get(v_config_621_, 2);
                lean_inc(v_root_627_);
                v___x_628_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_621_);
                lean_dec(v_config_621_);
                if v_isShared_626_ == 0 {
                    lean_ctor_set(v___x_625_, 2, v___x_628_);
                    v___x_630_ = v___x_625_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_632_, 0, v_pkg_622_);
                    lean_ctor_set(v_reuseFailAlloc_632_, 1, v_name_623_);
                    lean_ctor_set(v_reuseFailAlloc_632_, 2, v___x_628_);
                    v___x_630_ = v_reuseFailAlloc_632_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_631_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_631_, 0, v___x_630_);
                lean_ctor_set(v___x_631_, 1, v_root_627_);
                return v___x_631_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExe_isRoot_x3f(
    mut v_name_634_: *mut LeanObject,
    mut v_self_635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_641_: u8 = 0;
    let mut v_root_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: u8 = 0;
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_651_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_636_ = lean_ctor_get(v_self_635_, 2);
                v_pkg_637_ = lean_ctor_get(v_self_635_, 0);
                v_name_638_ = lean_ctor_get(v_self_635_, 1);
                v_isSharedCheck_651_ = (!lean_is_exclusive(v_self_635_)) as u8;
                if v_isSharedCheck_651_ == 0 {
                    v___x_640_ = v_self_635_;
                    v_isShared_641_ = v_isSharedCheck_651_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_config_636_);
                    lean_inc(v_name_638_);
                    lean_inc(v_pkg_637_);
                    lean_dec(v_self_635_);
                    v___x_640_ = lean_box(0);
                    v_isShared_641_ = v_isSharedCheck_651_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_root_642_ = lean_ctor_get(v_config_636_, 2);
                lean_inc(v_root_642_);
                v___x_643_ = lean_name_eq(v_name_634_, v_root_642_);
                if v___x_643_ == 0 {
                    lean_dec(v_root_642_);
                    lean_del_object(v___x_640_);
                    lean_dec(v_name_638_);
                    lean_dec_ref(v_pkg_637_);
                    lean_dec(v_config_636_);
                    v___x_644_ = lean_box(0);
                    return v___x_644_;
                } else {
                    v___x_645_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_636_);
                    lean_dec(v_config_636_);
                    if v_isShared_641_ == 0 {
                        lean_ctor_set(v___x_640_, 2, v___x_645_);
                        v___x_647_ = v___x_640_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_650_, 0, v_pkg_637_);
                        lean_ctor_set(v_reuseFailAlloc_650_, 1, v_name_638_);
                        lean_ctor_set(v_reuseFailAlloc_650_, 2, v___x_645_);
                        v___x_647_ = v_reuseFailAlloc_650_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_648_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_648_, 0, v___x_647_);
                lean_ctor_set(v___x_648_, 1, v_root_642_);
                v___x_649_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_649_, 0, v___x_648_);
                return v___x_649_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExe_isRoot_x3f___boxed(
    mut v_name_652_: *mut LeanObject,
    mut v_self_653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_654_: *mut LeanObject = core::ptr::null_mut();
    v_res_654_ = l_Lake_LeanExe_isRoot_x3f(v_name_652_, v_self_653_);
    lean_dec(v_name_652_);
    return v_res_654_;
}
pub unsafe fn l_Lake_LeanExe_isRootSrc_x3f(
    mut v_path_656_: *mut LeanObject,
    mut v_self_657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_664_: u8 = 0;
    let mut v_root_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: u8 = 0;
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_684_: u8 = 0;
    let mut v_unused_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_686_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_658_ = lean_ctor_get(v_self_657_, 2);
                lean_inc(v_config_658_);
                v_pkg_659_ = lean_ctor_get(v_self_657_, 0);
                lean_inc_ref(v_pkg_659_);
                v_config_660_ = lean_ctor_get(v_pkg_659_, 6);
                v_name_661_ = lean_ctor_get(v_self_657_, 1);
                v_isSharedCheck_684_ = (!lean_is_exclusive(v_self_657_)) as u8;
                if v_isSharedCheck_684_ == 0 {
                    v_unused_685_ = lean_ctor_get(v_self_657_, 2);
                    lean_dec(v_unused_685_);
                    v_unused_686_ = lean_ctor_get(v_self_657_, 0);
                    lean_dec(v_unused_686_);
                    v___x_663_ = v_self_657_;
                    v_isShared_664_ = v_isSharedCheck_684_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_661_);
                    lean_dec(v_self_657_);
                    v___x_663_ = lean_box(0);
                    v_isShared_664_ = v_isSharedCheck_684_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_root_665_ = lean_ctor_get(v_config_658_, 2);
                lean_inc(v_root_665_);
                v_dir_666_ = lean_ctor_get(v_pkg_659_, 4);
                lean_inc_ref(v_dir_666_);
                v_srcDir_667_ = lean_ctor_get(v_config_660_, 4);
                lean_inc_ref(v_srcDir_667_);
                v___x_668_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_658_);
                lean_dec(v_config_658_);
                v_srcDir_669_ = lean_ctor_get(v___x_668_, 1);
                lean_inc_ref(v_srcDir_669_);
                v___x_670_ = l_Lake_LeanExe_isRootSrc_x3f___closed__0;
                v___x_671_ = l_System_FilePath_withExtension(v_path_656_, v___x_670_);
                if v_isShared_664_ == 0 {
                    lean_ctor_set(v___x_663_, 2, v___x_668_);
                    v___x_673_ = v___x_663_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_683_, 0, v_pkg_659_);
                    lean_ctor_set(v_reuseFailAlloc_683_, 1, v_name_661_);
                    lean_ctor_set(v_reuseFailAlloc_683_, 2, v___x_668_);
                    v___x_673_ = v_reuseFailAlloc_683_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_root_665_);
                v___x_674_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_674_, 0, v___x_673_);
                lean_ctor_set(v___x_674_, 1, v_root_665_);
                v___x_675_ = l_System_FilePath_normalize(v_srcDir_667_);
                v___x_676_ = l_Lake_joinRelative(v_dir_666_, v___x_675_);
                v___x_677_ = l_System_FilePath_normalize(v_srcDir_669_);
                v___x_678_ = l_Lake_joinRelative(v___x_676_, v___x_677_);
                v___x_679_ = l_Lean_modToFilePath(v___x_678_, v_root_665_, v___x_670_);
                lean_dec_ref(v___x_678_);
                v___x_680_ = lean_string_dec_eq(v___x_671_, v___x_679_);
                lean_dec_ref(v___x_679_);
                lean_dec_ref(v___x_671_);
                if v___x_680_ == 0 {
                    lean_dec_ref_known(v___x_674_, 2);
                    v___x_681_ = lean_box(0);
                    return v___x_681_;
                } else {
                    v___x_682_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_682_, 0, v___x_674_);
                    return v___x_682_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExe_fileName(mut v_self_687_: *mut LeanObject) -> *mut LeanObject {
    let mut v_config_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exeName_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    v_config_688_ = lean_ctor_get(v_self_687_, 2);
    lean_inc(v_config_688_);
    lean_dec_ref(v_self_687_);
    v_exeName_689_ = lean_ctor_get(v_config_688_, 3);
    lean_inc_ref(v_exeName_689_);
    lean_dec(v_config_688_);
    v___x_690_ = l_System_FilePath_exeExtension;
    v___x_691_ = l_System_FilePath_addExtension(v_exeName_689_, v___x_690_);
    return v___x_691_;
}
pub unsafe fn l_Lake_LeanExe_file(mut v_self_692_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildDir_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binDir_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exeName_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_693_ = lean_ctor_get(v_self_692_, 0);
    lean_inc_ref(v_pkg_693_);
    v_config_694_ = lean_ctor_get(v_pkg_693_, 6);
    lean_inc_ref(v_config_694_);
    v_config_695_ = lean_ctor_get(v_self_692_, 2);
    lean_inc(v_config_695_);
    lean_dec_ref(v_self_692_);
    v_dir_696_ = lean_ctor_get(v_pkg_693_, 4);
    lean_inc_ref(v_dir_696_);
    lean_dec_ref(v_pkg_693_);
    v_buildDir_697_ = lean_ctor_get(v_config_694_, 5);
    lean_inc_ref(v_buildDir_697_);
    v_binDir_698_ = lean_ctor_get(v_config_694_, 8);
    lean_inc_ref(v_binDir_698_);
    lean_dec_ref(v_config_694_);
    v_exeName_699_ = lean_ctor_get(v_config_695_, 3);
    lean_inc_ref(v_exeName_699_);
    lean_dec(v_config_695_);
    v___x_700_ = l_System_FilePath_normalize(v_buildDir_697_);
    v___x_701_ = l_Lake_joinRelative(v_dir_696_, v___x_700_);
    v___x_702_ = l_System_FilePath_normalize(v_binDir_698_);
    v___x_703_ = l_Lake_joinRelative(v___x_701_, v___x_702_);
    v___x_704_ = l_System_FilePath_exeExtension;
    v___x_705_ = l_System_FilePath_addExtension(v_exeName_699_, v___x_704_);
    v___x_706_ = l_Lake_joinRelative(v___x_703_, v___x_705_);
    return v___x_706_;
}
pub unsafe fn l_Lake_LeanExe_supportInterpreter(mut v_self_707_: *mut LeanObject) -> u8 {
    let mut v_config_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_709_: u8 = 0;
    v_config_708_ = lean_ctor_get(v_self_707_, 2);
    v_supportInterpreter_709_ = lean_ctor_get_uint8(
        v_config_708_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
    );
    return v_supportInterpreter_709_;
}
pub unsafe fn l_Lake_LeanExe_supportInterpreter___boxed(
    mut v_self_710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_711_: u8 = 0;
    let mut v_r_712_: *mut LeanObject = core::ptr::null_mut();
    v_res_711_ = l_Lake_LeanExe_supportInterpreter(v_self_710_);
    lean_dec_ref(v_self_710_);
    v_r_712_ = lean_box((v_res_711_) as usize);
    return v_r_712_;
}
pub unsafe fn l_Lake_LeanExe_linkArgs(mut v_self_729_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_736_: u8 = 0;
    let mut v_moreLinkArgs_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linkArgs_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: u8 = 0;
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linkArgs_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: u8 = 0;
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linkArgs_745_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_730_ = lean_ctor_get(v_self_729_, 0);
                v_config_731_ = lean_ctor_get(v_pkg_730_, 6);
                v_toLeanConfig_732_ = lean_ctor_get(v_config_731_, 1);
                lean_inc_ref(v_toLeanConfig_732_);
                v_config_733_ = lean_ctor_get(v_self_729_, 2);
                lean_inc(v_config_733_);
                lean_dec_ref(v_self_729_);
                v_toLeanConfig_734_ = lean_ctor_get(v_config_733_, 0);
                lean_inc_ref(v_toLeanConfig_734_);
                v_moreLinkArgs_735_ = lean_ctor_get(v_toLeanConfig_732_, 8);
                lean_inc_ref(v_moreLinkArgs_735_);
                lean_dec_ref(v_toLeanConfig_732_);
                v_supportInterpreter_736_ = lean_ctor_get_uint8(
                    v_config_733_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                lean_dec(v_config_733_);
                v_moreLinkArgs_737_ = lean_ctor_get(v_toLeanConfig_734_, 8);
                lean_inc_ref(v_moreLinkArgs_737_);
                lean_dec_ref(v_toLeanConfig_734_);
                v_linkArgs_738_ = l_Array_append___redArg(v_moreLinkArgs_735_, v_moreLinkArgs_737_);
                lean_dec_ref(v_moreLinkArgs_737_);
                if v_supportInterpreter_736_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_743_ = l_System_Platform_isWindows;
                    if v___x_743_ == 0 {
                        v___x_744_ = l_Lake_LeanExe_linkArgs___closed__5;
                        v_linkArgs_745_ = l_Array_append___redArg(v___x_744_, v_linkArgs_738_);
                        lean_dec_ref(v_linkArgs_738_);
                        return v_linkArgs_745_;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_740_ = l_System_Platform_isWindows;
                if v___x_740_ == 0 {
                    return v_linkArgs_738_;
                } else {
                    v___x_741_ = l_Lake_LeanExe_linkArgs___closed__3;
                    v_linkArgs_742_ = l_Array_append___redArg(v_linkArgs_738_, v___x_741_);
                    return v_linkArgs_742_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExe_sharedLean(mut v_self_746_: *mut LeanObject) -> u8 {
    let mut v_config_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_748_: u8 = 0;
    let mut v___x_749_: u8 = 0;
    let mut v___x_750_: u8 = 0;
    v_config_747_ = lean_ctor_get(v_self_746_, 2);
    v_supportInterpreter_748_ = lean_ctor_get_uint8(
        v_config_747_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
    );
    v___x_749_ = l_System_Platform_isWindows;
    v___x_750_ = lean_strict_and(v___x_749_, v_supportInterpreter_748_);
    return v___x_750_;
}
pub unsafe fn l_Lake_LeanExe_sharedLean___boxed(
    mut v_self_751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_752_: u8 = 0;
    let mut v_r_753_: *mut LeanObject = core::ptr::null_mut();
    v_res_752_ = l_Lake_LeanExe_sharedLean(v_self_751_);
    lean_dec_ref(v_self_751_);
    v_r_753_ = lean_box((v_res_752_) as usize);
    return v_r_753_;
}
pub unsafe fn l_Lake_LeanExe_weakLinkArgs(mut v_self_754_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_755_ = lean_ctor_get(v_self_754_, 0);
    v_config_756_ = lean_ctor_get(v_pkg_755_, 6);
    v_toLeanConfig_757_ = lean_ctor_get(v_config_756_, 1);
    lean_inc_ref(v_toLeanConfig_757_);
    v_config_758_ = lean_ctor_get(v_self_754_, 2);
    lean_inc(v_config_758_);
    lean_dec_ref(v_self_754_);
    v_toLeanConfig_759_ = lean_ctor_get(v_config_758_, 0);
    lean_inc_ref(v_toLeanConfig_759_);
    lean_dec(v_config_758_);
    v_weakLinkArgs_760_ = lean_ctor_get(v_toLeanConfig_757_, 9);
    lean_inc_ref(v_weakLinkArgs_760_);
    lean_dec_ref(v_toLeanConfig_757_);
    v_weakLinkArgs_761_ = lean_ctor_get(v_toLeanConfig_759_, 9);
    lean_inc_ref(v_weakLinkArgs_761_);
    lean_dec_ref(v_toLeanConfig_759_);
    v___x_762_ = l_Array_append___redArg(v_weakLinkArgs_760_, v_weakLinkArgs_761_);
    lean_dec_ref(v_weakLinkArgs_761_);
    return v___x_762_;
}
pub unsafe fn l_Lake_LeanExe_moreLinkObjs(mut v_self_763_: *mut LeanObject) -> *mut LeanObject {
    let mut v_config_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_766_: *mut LeanObject = core::ptr::null_mut();
    v_config_764_ = lean_ctor_get(v_self_763_, 2);
    v_toLeanConfig_765_ = lean_ctor_get(v_config_764_, 0);
    v_moreLinkObjs_766_ = lean_ctor_get(v_toLeanConfig_765_, 6);
    lean_inc_ref(v_moreLinkObjs_766_);
    return v_moreLinkObjs_766_;
}
pub unsafe fn l_Lake_LeanExe_moreLinkObjs___boxed(
    mut v_self_767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_768_: *mut LeanObject = core::ptr::null_mut();
    v_res_768_ = l_Lake_LeanExe_moreLinkObjs(v_self_767_);
    lean_dec_ref(v_self_767_);
    return v_res_768_;
}
pub unsafe fn l_Lake_LeanExe_moreLinkLibs(mut v_self_769_: *mut LeanObject) -> *mut LeanObject {
    let mut v_config_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_772_: *mut LeanObject = core::ptr::null_mut();
    v_config_770_ = lean_ctor_get(v_self_769_, 2);
    v_toLeanConfig_771_ = lean_ctor_get(v_config_770_, 0);
    v_moreLinkLibs_772_ = lean_ctor_get(v_toLeanConfig_771_, 7);
    lean_inc_ref(v_moreLinkLibs_772_);
    return v_moreLinkLibs_772_;
}
pub unsafe fn l_Lake_LeanExe_moreLinkLibs___boxed(
    mut v_self_773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_774_: *mut LeanObject = core::ptr::null_mut();
    v_res_774_ = l_Lake_LeanExe_moreLinkLibs(v_self_773_);
    lean_dec_ref(v_self_773_);
    return v_res_774_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg(
    mut v_mod_775_: *mut LeanObject,
    mut v_as_776_: *mut LeanObject,
    mut v_i_777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_779_: u8 = 0;
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_778_ = lean_unsigned_to_nat(0);
                v_isZero_779_ = lean_nat_dec_eq(v_i_777_, v_zero_778_);
                if v_isZero_779_ == 1 {
                    lean_dec(v_i_777_);
                    v___x_780_ = lean_box(0);
                    return v___x_780_;
                } else {
                    v_one_781_ = lean_unsigned_to_nat(1);
                    v_n_782_ = lean_nat_sub(v_i_777_, v_one_781_);
                    lean_dec(v_i_777_);
                    v___x_783_ = lean_array_fget_borrowed(v_as_776_, v_n_782_);
                    lean_inc(v___x_783_);
                    v___x_784_ = l_Lake_LeanExe_isRoot_x3f(v_mod_775_, v___x_783_);
                    if lean_obj_tag(v___x_784_) == 0 {
                        v_i_777_ = v_n_782_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_n_782_);
                        return v___x_784_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg___boxed(
    mut v_mod_786_: *mut LeanObject,
    mut v_as_787_: *mut LeanObject,
    mut v_i_788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_789_: *mut LeanObject = core::ptr::null_mut();
    v_res_789_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg(v_mod_786_, v_as_787_, v_i_788_);
    lean_dec_ref(v_as_787_);
    lean_dec(v_mod_786_);
    return v_res_789_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(
    mut v_self_790_: *mut LeanObject,
    mut v_as_791_: *mut LeanObject,
    mut v_i_792_: usize,
    mut v_stop_793_: usize,
    mut v_b_794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: usize = 0;
    let mut v___x_798_: usize = 0;
    let mut v___x_800_: u8 = 0;
    let mut v_toConfigDecl_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: u8 = 0;
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_800_ = lean_usize_dec_eq(v_i_792_, v_stop_793_);
                if v___x_800_ == 0 {
                    v_toConfigDecl_801_ = lean_array_uget_borrowed(v_as_791_, v_i_792_);
                    v_name_802_ = lean_ctor_get(v_toConfigDecl_801_, 1);
                    v_kind_803_ = lean_ctor_get(v_toConfigDecl_801_, 2);
                    v_config_804_ = lean_ctor_get(v_toConfigDecl_801_, 3);
                    v___x_805_ = l_Lake_LeanExe_keyword;
                    v___x_806_ = lean_name_eq(v_kind_803_, v___x_805_);
                    if v___x_806_ == 0 {
                        v___y_796_ = v_b_794_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_config_804_);
                        lean_inc(v_name_802_);
                        lean_inc_ref(v_self_790_);
                        v___x_807_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_807_, 0, v_self_790_);
                        lean_ctor_set(v___x_807_, 1, v_name_802_);
                        lean_ctor_set(v___x_807_, 2, v_config_804_);
                        v___x_808_ = lean_array_push(v_b_794_, v___x_807_);
                        v___y_796_ = v___x_808_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_self_790_);
                    return v_b_794_;
                }
            }
            1 => {
                v___x_797_ = 1usize;
                v___x_798_ = lean_usize_add(v_i_792_, v___x_797_);
                v_i_792_ = v___x_798_;
                v_b_794_ = v___y_796_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1___boxed(
    mut v_self_809_: *mut LeanObject,
    mut v_as_810_: *mut LeanObject,
    mut v_i_811_: *mut LeanObject,
    mut v_stop_812_: *mut LeanObject,
    mut v_b_813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_814_: usize = 0;
    let mut v_stop_boxed_815_: usize = 0;
    let mut v_res_816_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_814_ = lean_unbox_usize(v_i_811_);
    lean_dec(v_i_811_);
    v_stop_boxed_815_ = lean_unbox_usize(v_stop_812_);
    lean_dec(v_stop_812_);
    v_res_816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(v_self_809_, v_as_810_, v_i_boxed_814_, v_stop_boxed_815_, v_b_813_);
    lean_dec_ref(v_as_810_);
    return v_res_816_;
}
pub unsafe fn l_Lake_Package_findTargetModule_x3f(
    mut v_mod_817_: *mut LeanObject,
    mut v_self_818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_targetDecls_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: u8 = 0;
    let mut v___x_829_: u8 = 0;
    let mut v___x_830_: usize = 0;
    let mut v___x_831_: usize = 0;
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: usize = 0;
    let mut v___x_834_: usize = 0;
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_targetDecls_824_ = lean_ctor_get(v_self_818_, 14);
                v___x_825_ = lean_unsigned_to_nat(0);
                v___x_826_ = l_Lake_Package_leanExes___closed__0;
                v___x_827_ = lean_array_get_size(v_targetDecls_824_);
                v___x_828_ = lean_nat_dec_lt(v___x_825_, v___x_827_);
                if v___x_828_ == 0 {
                    v___y_820_ = v___x_826_;
                    state = 1;
                    continue;
                } else {
                    v___x_829_ = lean_nat_dec_le(v___x_827_, v___x_827_);
                    if v___x_829_ == 0 {
                        if v___x_828_ == 0 {
                            v___y_820_ = v___x_826_;
                            state = 1;
                            continue;
                        } else {
                            v___x_830_ = 0usize;
                            v___x_831_ = lean_usize_of_nat(v___x_827_);
                            lean_inc_ref(v_self_818_);
                            v___x_832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(v_self_818_, v_targetDecls_824_, v___x_830_, v___x_831_, v___x_826_);
                            v___y_820_ = v___x_832_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_833_ = 0usize;
                        v___x_834_ = lean_usize_of_nat(v___x_827_);
                        lean_inc_ref(v_self_818_);
                        v___x_835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(v_self_818_, v_targetDecls_824_, v___x_833_, v___x_834_, v___x_826_);
                        v___y_820_ = v___x_835_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_821_ = lean_array_get_size(v___y_820_);
                v___x_822_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg(v_mod_817_, v___y_820_, v___x_821_);
                lean_dec_ref(v___y_820_);
                if lean_obj_tag(v___x_822_) == 0 {
                    v___x_823_ = l_Lake_Package_findModule_x3f(v_mod_817_, v_self_818_);
                    return v___x_823_;
                } else {
                    lean_dec_ref(v_self_818_);
                    lean_dec(v_mod_817_);
                    return v___x_822_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0(
    mut v_mod_836_: *mut LeanObject,
    mut v_as_837_: *mut LeanObject,
    mut v_i_838_: *mut LeanObject,
    mut v_a_839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    v___x_840_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg(v_mod_836_, v_as_837_, v_i_838_);
    return v___x_840_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___boxed(
    mut v_mod_841_: *mut LeanObject,
    mut v_as_842_: *mut LeanObject,
    mut v_i_843_: *mut LeanObject,
    mut v_a_844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_845_: *mut LeanObject = core::ptr::null_mut();
    v_res_845_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0(v_mod_841_, v_as_842_, v_i_843_, v_a_844_);
    lean_dec_ref(v_as_842_);
    lean_dec(v_mod_841_);
    return v_res_845_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg(
    mut v_path_846_: *mut LeanObject,
    mut v_as_847_: *mut LeanObject,
    mut v_i_848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_850_: u8 = 0;
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_849_ = lean_unsigned_to_nat(0);
                v_isZero_850_ = lean_nat_dec_eq(v_i_848_, v_zero_849_);
                if v_isZero_850_ == 1 {
                    lean_dec(v_i_848_);
                    lean_dec_ref(v_path_846_);
                    v___x_851_ = lean_box(0);
                    return v___x_851_;
                } else {
                    v_one_852_ = lean_unsigned_to_nat(1);
                    v_n_853_ = lean_nat_sub(v_i_848_, v_one_852_);
                    lean_dec(v_i_848_);
                    v___x_854_ = lean_array_fget_borrowed(v_as_847_, v_n_853_);
                    lean_inc(v___x_854_);
                    lean_inc_ref(v_path_846_);
                    v___x_855_ = l_Lake_LeanExe_isRootSrc_x3f(v_path_846_, v___x_854_);
                    if lean_obj_tag(v___x_855_) == 0 {
                        v_i_848_ = v_n_853_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_n_853_);
                        lean_dec_ref(v_path_846_);
                        return v___x_855_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg___boxed(
    mut v_path_857_: *mut LeanObject,
    mut v_as_858_: *mut LeanObject,
    mut v_i_859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_860_: *mut LeanObject = core::ptr::null_mut();
    v_res_860_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg(v_path_857_, v_as_858_, v_i_859_);
    lean_dec_ref(v_as_858_);
    return v_res_860_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2(
    mut v_self_864_: *mut LeanObject,
    mut v_as_865_: *mut LeanObject,
    mut v_i_866_: usize,
    mut v_stop_867_: usize,
    mut v_b_868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: usize = 0;
    let mut v___x_872_: usize = 0;
    let mut v___x_874_: u8 = 0;
    let mut v_toConfigDecl_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: u8 = 0;
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_874_ = lean_usize_dec_eq(v_i_866_, v_stop_867_);
                if v___x_874_ == 0 {
                    v_toConfigDecl_875_ = lean_array_uget_borrowed(v_as_865_, v_i_866_);
                    v_name_876_ = lean_ctor_get(v_toConfigDecl_875_, 1);
                    v_kind_877_ = lean_ctor_get(v_toConfigDecl_875_, 2);
                    v_config_878_ = lean_ctor_get(v_toConfigDecl_875_, 3);
                    v___x_879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___closed__1;
                    v___x_880_ = lean_name_eq(v_kind_877_, v___x_879_);
                    if v___x_880_ == 0 {
                        v___y_870_ = v_b_868_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_config_878_);
                        lean_inc(v_name_876_);
                        lean_inc_ref(v_self_864_);
                        v___x_881_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_881_, 0, v_self_864_);
                        lean_ctor_set(v___x_881_, 1, v_name_876_);
                        lean_ctor_set(v___x_881_, 2, v_config_878_);
                        v___x_882_ = lean_array_push(v_b_868_, v___x_881_);
                        v___y_870_ = v___x_882_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_self_864_);
                    return v_b_868_;
                }
            }
            1 => {
                v___x_871_ = 1usize;
                v___x_872_ = lean_usize_add(v_i_866_, v___x_871_);
                v_i_866_ = v___x_872_;
                v_b_868_ = v___y_870_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___boxed(
    mut v_self_883_: *mut LeanObject,
    mut v_as_884_: *mut LeanObject,
    mut v_i_885_: *mut LeanObject,
    mut v_stop_886_: *mut LeanObject,
    mut v_b_887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_888_: usize = 0;
    let mut v_stop_boxed_889_: usize = 0;
    let mut v_res_890_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_888_ = lean_unbox_usize(v_i_885_);
    lean_dec(v_i_885_);
    v_stop_boxed_889_ = lean_unbox_usize(v_stop_886_);
    lean_dec(v_stop_886_);
    v_res_890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2(v_self_883_, v_as_884_, v_i_boxed_888_, v_stop_boxed_889_, v_b_887_);
    lean_dec_ref(v_as_884_);
    return v_res_890_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg(
    mut v_path_891_: *mut LeanObject,
    mut v_as_892_: *mut LeanObject,
    mut v_i_893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_895_: u8 = 0;
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_894_ = lean_unsigned_to_nat(0);
                v_isZero_895_ = lean_nat_dec_eq(v_i_893_, v_zero_894_);
                if v_isZero_895_ == 1 {
                    lean_dec(v_i_893_);
                    lean_dec_ref(v_path_891_);
                    v___x_896_ = lean_box(0);
                    return v___x_896_;
                } else {
                    v_one_897_ = lean_unsigned_to_nat(1);
                    v_n_898_ = lean_nat_sub(v_i_893_, v_one_897_);
                    lean_dec(v_i_893_);
                    v___x_899_ = lean_array_fget_borrowed(v_as_892_, v_n_898_);
                    lean_inc(v___x_899_);
                    lean_inc_ref(v_path_891_);
                    v___x_900_ = l_Lake_LeanLib_findModuleBySrc_x3f(v_path_891_, v___x_899_);
                    if lean_obj_tag(v___x_900_) == 0 {
                        v_i_893_ = v_n_898_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_n_898_);
                        lean_dec_ref(v_path_891_);
                        return v___x_900_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg___boxed(
    mut v_path_902_: *mut LeanObject,
    mut v_as_903_: *mut LeanObject,
    mut v_i_904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_905_: *mut LeanObject = core::ptr::null_mut();
    v_res_905_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg(v_path_902_, v_as_903_, v_i_904_);
    lean_dec_ref(v_as_903_);
    return v_res_905_;
}
pub unsafe fn l_Lake_Package_findModuleBySrc_x3f(
    mut v_path_906_: *mut LeanObject,
    mut v_self_907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_targetDecls_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: u8 = 0;
    let mut v___x_921_: u8 = 0;
    let mut v___x_922_: usize = 0;
    let mut v___x_923_: usize = 0;
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: usize = 0;
    let mut v___x_926_: usize = 0;
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: u8 = 0;
    let mut v___x_932_: u8 = 0;
    let mut v___x_933_: usize = 0;
    let mut v___x_934_: usize = 0;
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: usize = 0;
    let mut v___x_937_: usize = 0;
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_targetDecls_912_ = lean_ctor_get(v_self_907_, 14);
                lean_inc_ref(v_targetDecls_912_);
                v___x_928_ = lean_unsigned_to_nat(0);
                v___x_929_ = l_Lake_Package_leanExes___closed__0;
                v___x_930_ = lean_array_get_size(v_targetDecls_912_);
                v___x_931_ = lean_nat_dec_lt(v___x_928_, v___x_930_);
                if v___x_931_ == 0 {
                    v___y_914_ = v___x_929_;
                    state = 2;
                    continue;
                } else {
                    v___x_932_ = lean_nat_dec_le(v___x_930_, v___x_930_);
                    if v___x_932_ == 0 {
                        if v___x_931_ == 0 {
                            v___y_914_ = v___x_929_;
                            state = 2;
                            continue;
                        } else {
                            v___x_933_ = 0usize;
                            v___x_934_ = lean_usize_of_nat(v___x_930_);
                            lean_inc_ref(v_self_907_);
                            v___x_935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2(v_self_907_, v_targetDecls_912_, v___x_933_, v___x_934_, v___x_929_);
                            v___y_914_ = v___x_935_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_936_ = 0usize;
                        v___x_937_ = lean_usize_of_nat(v___x_930_);
                        lean_inc_ref(v_self_907_);
                        v___x_938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2(v_self_907_, v_targetDecls_912_, v___x_936_, v___x_937_, v___x_929_);
                        v___y_914_ = v___x_938_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_910_ = lean_array_get_size(v___y_909_);
                v___x_911_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg(v_path_906_, v___y_909_, v___x_910_);
                lean_dec_ref(v___y_909_);
                return v___x_911_;
            }
            2 => {
                v___x_915_ = lean_array_get_size(v___y_914_);
                lean_inc_ref(v_path_906_);
                v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg(v_path_906_, v___y_914_, v___x_915_);
                lean_dec_ref(v___y_914_);
                if lean_obj_tag(v___x_916_) == 0 {
                    v___x_917_ = lean_unsigned_to_nat(0);
                    v___x_918_ = l_Lake_Package_leanExes___closed__0;
                    v___x_919_ = lean_array_get_size(v_targetDecls_912_);
                    v___x_920_ = lean_nat_dec_lt(v___x_917_, v___x_919_);
                    if v___x_920_ == 0 {
                        lean_dec_ref(v_targetDecls_912_);
                        lean_dec_ref(v_self_907_);
                        v___y_909_ = v___x_918_;
                        state = 1;
                        continue;
                    } else {
                        v___x_921_ = lean_nat_dec_le(v___x_919_, v___x_919_);
                        if v___x_921_ == 0 {
                            if v___x_920_ == 0 {
                                lean_dec_ref(v_targetDecls_912_);
                                lean_dec_ref(v_self_907_);
                                v___y_909_ = v___x_918_;
                                state = 1;
                                continue;
                            } else {
                                v___x_922_ = 0usize;
                                v___x_923_ = lean_usize_of_nat(v___x_919_);
                                v___x_924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(v_self_907_, v_targetDecls_912_, v___x_922_, v___x_923_, v___x_918_);
                                lean_dec_ref(v_targetDecls_912_);
                                v___y_909_ = v___x_924_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_925_ = 0usize;
                            v___x_926_ = lean_usize_of_nat(v___x_919_);
                            v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(v_self_907_, v_targetDecls_912_, v___x_925_, v___x_926_, v___x_918_);
                            lean_dec_ref(v_targetDecls_912_);
                            v___y_909_ = v___x_927_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_targetDecls_912_);
                    lean_dec_ref(v_self_907_);
                    lean_dec_ref(v_path_906_);
                    return v___x_916_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0(
    mut v_path_939_: *mut LeanObject,
    mut v_as_940_: *mut LeanObject,
    mut v_i_941_: *mut LeanObject,
    mut v_a_942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    v___x_943_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg(v_path_939_, v_as_940_, v_i_941_);
    return v___x_943_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___boxed(
    mut v_path_944_: *mut LeanObject,
    mut v_as_945_: *mut LeanObject,
    mut v_i_946_: *mut LeanObject,
    mut v_a_947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_948_: *mut LeanObject = core::ptr::null_mut();
    v_res_948_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0(v_path_944_, v_as_945_, v_i_946_, v_a_947_);
    lean_dec_ref(v_as_945_);
    return v_res_948_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1(
    mut v_path_949_: *mut LeanObject,
    mut v_as_950_: *mut LeanObject,
    mut v_i_951_: *mut LeanObject,
    mut v_a_952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    v___x_953_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg(v_path_949_, v_as_950_, v_i_951_);
    return v___x_953_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___boxed(
    mut v_path_954_: *mut LeanObject,
    mut v_as_955_: *mut LeanObject,
    mut v_i_956_: *mut LeanObject,
    mut v_a_957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_958_: *mut LeanObject = core::ptr::null_mut();
    v_res_958_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1(v_path_954_, v_as_955_, v_i_956_, v_a_957_);
    lean_dec_ref(v_as_955_);
    return v_res_958_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_LeanExe(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Module(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_LeanExe(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_LeanExe(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Module(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanExe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_LeanExe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_LeanExe(builtin);
}
