// Lean compiler output
// Module: Lake.Util.NativeLib
// Imports: Init.System.IO Init.Data.ToString.Macro Init.System.Platform
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::System::FilePath::l_System_SearchPath_parse;
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, runtime_initialize_Init_System_IO,
};
use crate::r#gen::Init::System::Platform::{
    initialize_Init_System_Platform, l_System_Platform_isOSX, l_System_Platform_isWindows,
    runtime_initialize_Init_System_Platform,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::System::IO::lean_io_getenv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_ctor_get, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
    lean_obj_tag, lean_unbox,
};
pub static l_Lake_sharedLibExt___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [115, 111, 0],
};
static mut l_Lake_sharedLibExt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_sharedLibExt___closed__0_value) as *mut LeanObject;
pub static l_Lake_sharedLibExt___closed__1_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [100, 121, 108, 105, 98, 0],
};
static mut l_Lake_sharedLibExt___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_sharedLibExt___closed__1_value) as *mut LeanObject;
pub static l_Lake_sharedLibExt___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [100, 108, 108, 0],
};
static mut l_Lake_sharedLibExt___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_sharedLibExt___closed__2_value) as *mut LeanObject;
pub static mut l_Lake_sharedLibExt: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_nameToStaticLib___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [108, 105, 98, 0],
};
static mut l_Lake_nameToStaticLib___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_nameToStaticLib___closed__0_value) as *mut LeanObject;
pub static l_Lake_nameToStaticLib___closed__1_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [46, 97, 0],
};
static mut l_Lake_nameToStaticLib___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_nameToStaticLib___closed__1_value) as *mut LeanObject;
pub static l_Lake_nameToSharedLib___closed__0_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Lake_nameToSharedLib___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_nameToSharedLib___closed__0_value) as *mut LeanObject;
pub static l_Lake_nameToSharedLib___closed__1_value: LeanStringObject<1> = LeanStringObject {
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
static mut l_Lake_nameToSharedLib___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_nameToSharedLib___closed__1_value) as *mut LeanObject;
pub static l_Lake_sharedLibPathEnvVar___closed__0_value: LeanStringObject<16> = LeanStringObject {
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
        76, 68, 95, 76, 73, 66, 82, 65, 82, 89, 95, 80, 65, 84, 72, 0,
    ],
};
static mut l_Lake_sharedLibPathEnvVar___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_sharedLibPathEnvVar___closed__0_value) as *mut LeanObject;
pub static l_Lake_sharedLibPathEnvVar___closed__1_value: LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        68, 89, 76, 68, 95, 76, 73, 66, 82, 65, 82, 89, 95, 80, 65, 84, 72, 0,
    ],
};
static mut l_Lake_sharedLibPathEnvVar___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_sharedLibPathEnvVar___closed__1_value) as *mut LeanObject;
pub static l_Lake_sharedLibPathEnvVar___closed__2_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [80, 65, 84, 72, 0],
};
static mut l_Lake_sharedLibPathEnvVar___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_sharedLibPathEnvVar___closed__2_value) as *mut LeanObject;
pub static mut l_Lake_sharedLibPathEnvVar: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lake_sharedLibExt() -> *mut LeanObject {
    let mut v___x_64_: u8 = 0;
    v___x_64_ = l_System_Platform_isWindows;
    if v___x_64_ == 0 {
        let mut v___x_65_: u8 = 0;
        v___x_65_ = l_System_Platform_isOSX;
        if v___x_65_ == 0 {
            let mut v___x_66_: *mut LeanObject = core::ptr::null_mut();
            v___x_66_ = l_Lake_sharedLibExt___closed__0;
            return v___x_66_;
        } else {
            let mut v___x_67_: *mut LeanObject = core::ptr::null_mut();
            v___x_67_ = l_Lake_sharedLibExt___closed__1;
            return v___x_67_;
        }
    } else {
        let mut v___x_68_: *mut LeanObject = core::ptr::null_mut();
        v___x_68_ = l_Lake_sharedLibExt___closed__2;
        return v___x_68_;
    }
}
pub unsafe fn l_Lake_nameToStaticLib(
    mut v_name_71_: *mut LeanObject,
    mut v_libPrefixOnWindows_72_: u8,
) -> *mut LeanObject {
    let mut v___x_74_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_75_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_76_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_77_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_78_: u8 = 0;
    let mut v___x_79_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_80_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_libPrefixOnWindows_72_ == 0 {
                    v___x_78_ = l_System_Platform_isWindows;
                    if v___x_78_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_79_ = l_Lake_nameToStaticLib___closed__1;
                        v___x_80_ = lean_string_append(v_name_71_, v___x_79_);
                        return v___x_80_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_74_ = l_Lake_nameToStaticLib___closed__0;
                v___x_75_ = lean_string_append(v___x_74_, v_name_71_);
                lean_dec_ref(v_name_71_);
                v___x_76_ = l_Lake_nameToStaticLib___closed__1;
                v___x_77_ = lean_string_append(v___x_75_, v___x_76_);
                return v___x_77_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_nameToStaticLib___boxed(
    mut v_name_81_: *mut LeanObject,
    mut v_libPrefixOnWindows_82_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_libPrefixOnWindows_boxed_83_: u8 = 0;
    let mut v_res_84_: *mut LeanObject = core::ptr::null_mut();
    v_libPrefixOnWindows_boxed_83_ = (lean_unbox(v_libPrefixOnWindows_82_) as u8);
    v_res_84_ = l_Lake_nameToStaticLib(v_name_81_, v_libPrefixOnWindows_boxed_83_);
    return v_res_84_;
}
pub unsafe fn l_Lake_nameToSharedLib(
    mut v_name_87_: *mut LeanObject,
    mut v_libPrefixOnWindows_88_: u8,
) -> *mut LeanObject {
    let mut v___y_90_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_91_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_92_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_93_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_94_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_95_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_97_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_98_: u8 = 0;
    let mut v___x_99_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_libPrefixOnWindows_88_ == 0 {
                    v___x_98_ = l_System_Platform_isWindows;
                    if v___x_98_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_99_ = l_Lake_nameToSharedLib___closed__1;
                        v___y_90_ = v___x_99_;
                        state = 1;
                        continue;
                    }
                } else {
                    state = 2;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v___y_90_);
                v___x_91_ = lean_string_append(v___y_90_, v_name_87_);
                v___x_92_ = l_Lake_nameToSharedLib___closed__0;
                v___x_93_ = lean_string_append(v___x_91_, v___x_92_);
                v___x_94_ = l_Lake_sharedLibExt;
                v___x_95_ = lean_string_append(v___x_93_, v___x_94_);
                return v___x_95_;
            }
            2 => {
                v___x_97_ = l_Lake_nameToStaticLib___closed__0;
                v___y_90_ = v___x_97_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_nameToSharedLib___boxed(
    mut v_name_100_: *mut LeanObject,
    mut v_libPrefixOnWindows_101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_libPrefixOnWindows_boxed_102_: u8 = 0;
    let mut v_res_103_: *mut LeanObject = core::ptr::null_mut();
    v_libPrefixOnWindows_boxed_102_ = (lean_unbox(v_libPrefixOnWindows_101_) as u8);
    v_res_103_ = l_Lake_nameToSharedLib(v_name_100_, v_libPrefixOnWindows_boxed_102_);
    lean_dec_ref(v_name_100_);
    return v_res_103_;
}
pub unsafe fn _init_l_Lake_sharedLibPathEnvVar() -> *mut LeanObject {
    let mut v___x_107_: u8 = 0;
    v___x_107_ = l_System_Platform_isWindows;
    if v___x_107_ == 0 {
        let mut v___x_108_: u8 = 0;
        v___x_108_ = l_System_Platform_isOSX;
        if v___x_108_ == 0 {
            let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
            v___x_109_ = l_Lake_sharedLibPathEnvVar___closed__0;
            return v___x_109_;
        } else {
            let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
            v___x_110_ = l_Lake_sharedLibPathEnvVar___closed__1;
            return v___x_110_;
        }
    } else {
        let mut v___x_111_: *mut LeanObject = core::ptr::null_mut();
        v___x_111_ = l_Lake_sharedLibPathEnvVar___closed__2;
        return v___x_111_;
    }
}
pub unsafe fn l_Lake_getSearchPath(mut v_envVar_112_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
    v___x_114_ = lean_io_getenv(v_envVar_112_);
    if lean_obj_tag(v___x_114_) == 0 {
        let mut v___x_115_: *mut LeanObject = core::ptr::null_mut();
        v___x_115_ = lean_box(0);
        return v___x_115_;
    } else {
        let mut v_val_116_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_117_: *mut LeanObject = core::ptr::null_mut();
        v_val_116_ = lean_ctor_get(v___x_114_, 0);
        lean_inc(v_val_116_);
        lean_dec_ref_known(v___x_114_, 1);
        v___x_117_ = l_System_SearchPath_parse(v_val_116_);
        return v___x_117_;
    }
}
pub unsafe fn l_Lake_getSearchPath___boxed(
    mut v_envVar_118_: *mut LeanObject,
    mut v_a_119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_120_: *mut LeanObject = core::ptr::null_mut();
    v_res_120_ = l_Lake_getSearchPath(v_envVar_118_);
    lean_dec_ref(v_envVar_118_);
    return v_res_120_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_NativeLib(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_sharedLibExt = _init_l_Lake_sharedLibExt();
    lean_mark_persistent(l_Lake_sharedLibExt);
    l_Lake_sharedLibPathEnvVar = _init_l_Lake_sharedLibPathEnvVar();
    lean_mark_persistent(l_Lake_sharedLibPathEnvVar);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_NativeLib(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_NativeLib(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_System_Platform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_NativeLib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Util_NativeLib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Util_NativeLib(builtin);
}
