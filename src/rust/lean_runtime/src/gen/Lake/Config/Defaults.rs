// Lean compiler output
// Module: Lake.Config.Defaults
// Imports: Init.System.FilePath
use crate::r#gen::Init::System::FilePath::{
    initialize_Init_System_FilePath, l_System_FilePath_addExtension, l_System_FilePath_join,
    runtime_initialize_Init_System_FilePath,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
};
pub static l_Lake_defaultLakeDir___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [46, 108, 97, 107, 101, 0],
};
static mut l_Lake_defaultLakeDir___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_defaultLakeDir___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_defaultLakeDir: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_defaultLakeDir___closed__0_value) as *mut LeanObject;
pub static l_Lake_defaultPackagesDir___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [112, 97, 99, 107, 97, 103, 101, 115, 0],
};
static mut l_Lake_defaultPackagesDir___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_defaultPackagesDir___closed__0_value) as *mut LeanObject;
static mut l_Lake_defaultPackagesDir___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_defaultPackagesDir___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_defaultPackagesDir: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_defaultConfigFile___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [108, 97, 107, 101, 102, 105, 108, 101, 0],
};
static mut l_Lake_defaultConfigFile___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_defaultConfigFile___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_defaultConfigFile: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_defaultConfigFile___closed__0_value) as *mut LeanObject;
pub static l_Lake_defaultLeanConfigFile___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [108, 101, 97, 110, 0],
};
static mut l_Lake_defaultLeanConfigFile___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_defaultLeanConfigFile___closed__0_value) as *mut LeanObject;
static mut l_Lake_defaultLeanConfigFile___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_defaultLeanConfigFile___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_defaultLeanConfigFile: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_defaultTomlConfigFile___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 111, 109, 108, 0],
};
static mut l_Lake_defaultTomlConfigFile___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_defaultTomlConfigFile___closed__0_value) as *mut LeanObject;
static mut l_Lake_defaultTomlConfigFile___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_defaultTomlConfigFile___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_defaultTomlConfigFile: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_defaultManifestFile___closed__0_value: LeanStringObject<19> = LeanStringObject {
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
        108, 97, 107, 101, 45, 109, 97, 110, 105, 102, 101, 115, 116, 46, 106, 115, 111, 110, 0,
    ],
};
static mut l_Lake_defaultManifestFile___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_defaultManifestFile___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_defaultManifestFile: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_defaultManifestFile___closed__0_value) as *mut LeanObject;
pub static l_Lake_defaultBuildDir___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [98, 117, 105, 108, 100, 0],
};
static mut l_Lake_defaultBuildDir___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_defaultBuildDir___closed__0_value) as *mut LeanObject;
static mut l_Lake_defaultBuildDir___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_defaultBuildDir___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_defaultBuildDir: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_defaultLeanLibDir___closed__0_value: LeanStringObject<4> = LeanStringObject {
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
static mut l_Lake_defaultLeanLibDir___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_defaultLeanLibDir___closed__0_value) as *mut LeanObject;
static mut l_Lake_defaultLeanLibDir___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_defaultLeanLibDir___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_defaultLeanLibDir: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_defaultNativeLibDir: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_defaultLeanLibDir___closed__0_value) as *mut LeanObject;
pub static l_Lake_defaultBinDir___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [98, 105, 110, 0],
};
static mut l_Lake_defaultBinDir___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_defaultBinDir___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_defaultBinDir: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_defaultBinDir___closed__0_value) as *mut LeanObject;
pub static l_Lake_defaultIrDir___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [105, 114, 0],
};
static mut l_Lake_defaultIrDir___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_defaultIrDir___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_defaultIrDir: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_defaultIrDir___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l_Lake_defaultPackagesDir___closed__1() -> *mut LeanObject {
    let mut v___x_40_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_41_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_42_: *mut LeanObject = core::ptr::null_mut();
    v___x_40_ = l_Lake_defaultPackagesDir___closed__0;
    v___x_41_ = l_Lake_defaultLakeDir___closed__0;
    v___x_42_ = l_System_FilePath_join(v___x_41_, v___x_40_);
    return v___x_42_;
}
pub unsafe fn _init_l_Lake_defaultPackagesDir() -> *mut LeanObject {
    let mut v___x_43_: *mut LeanObject = core::ptr::null_mut();
    v___x_43_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_defaultPackagesDir___closed__1),
        core::ptr::addr_of_mut!(l_Lake_defaultPackagesDir___closed__1_once),
        _init_l_Lake_defaultPackagesDir___closed__1,
    );
    return v___x_43_;
}
pub unsafe fn _init_l_Lake_defaultLeanConfigFile___closed__1() -> *mut LeanObject {
    let mut v___x_47_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_48_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_49_: *mut LeanObject = core::ptr::null_mut();
    v___x_47_ = l_Lake_defaultLeanConfigFile___closed__0;
    v___x_48_ = l_Lake_defaultConfigFile___closed__0;
    v___x_49_ = l_System_FilePath_addExtension(v___x_48_, v___x_47_);
    return v___x_49_;
}
pub unsafe fn _init_l_Lake_defaultLeanConfigFile() -> *mut LeanObject {
    let mut v___x_50_: *mut LeanObject = core::ptr::null_mut();
    v___x_50_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_defaultLeanConfigFile___closed__1),
        core::ptr::addr_of_mut!(l_Lake_defaultLeanConfigFile___closed__1_once),
        _init_l_Lake_defaultLeanConfigFile___closed__1,
    );
    return v___x_50_;
}
pub unsafe fn _init_l_Lake_defaultTomlConfigFile___closed__1() -> *mut LeanObject {
    let mut v___x_52_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_53_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_54_: *mut LeanObject = core::ptr::null_mut();
    v___x_52_ = l_Lake_defaultTomlConfigFile___closed__0;
    v___x_53_ = l_Lake_defaultConfigFile___closed__0;
    v___x_54_ = l_System_FilePath_addExtension(v___x_53_, v___x_52_);
    return v___x_54_;
}
pub unsafe fn _init_l_Lake_defaultTomlConfigFile() -> *mut LeanObject {
    let mut v___x_55_: *mut LeanObject = core::ptr::null_mut();
    v___x_55_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_defaultTomlConfigFile___closed__1),
        core::ptr::addr_of_mut!(l_Lake_defaultTomlConfigFile___closed__1_once),
        _init_l_Lake_defaultTomlConfigFile___closed__1,
    );
    return v___x_55_;
}
pub unsafe fn _init_l_Lake_defaultBuildDir___closed__1() -> *mut LeanObject {
    let mut v___x_59_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_60_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_61_: *mut LeanObject = core::ptr::null_mut();
    v___x_59_ = l_Lake_defaultBuildDir___closed__0;
    v___x_60_ = l_Lake_defaultLakeDir___closed__0;
    v___x_61_ = l_System_FilePath_join(v___x_60_, v___x_59_);
    return v___x_61_;
}
pub unsafe fn _init_l_Lake_defaultBuildDir() -> *mut LeanObject {
    let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
    v___x_62_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_defaultBuildDir___closed__1),
        core::ptr::addr_of_mut!(l_Lake_defaultBuildDir___closed__1_once),
        _init_l_Lake_defaultBuildDir___closed__1,
    );
    return v___x_62_;
}
pub unsafe fn _init_l_Lake_defaultLeanLibDir___closed__1() -> *mut LeanObject {
    let mut v___x_64_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_65_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_66_: *mut LeanObject = core::ptr::null_mut();
    v___x_64_ = l_Lake_defaultLeanConfigFile___closed__0;
    v___x_65_ = l_Lake_defaultLeanLibDir___closed__0;
    v___x_66_ = l_System_FilePath_join(v___x_65_, v___x_64_);
    return v___x_66_;
}
pub unsafe fn _init_l_Lake_defaultLeanLibDir() -> *mut LeanObject {
    let mut v___x_67_: *mut LeanObject = core::ptr::null_mut();
    v___x_67_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_defaultLeanLibDir___closed__1),
        core::ptr::addr_of_mut!(l_Lake_defaultLeanLibDir___closed__1_once),
        _init_l_Lake_defaultLeanLibDir___closed__1,
    );
    return v___x_67_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Defaults(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_FilePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_defaultPackagesDir = _init_l_Lake_defaultPackagesDir();
    lean_mark_persistent(l_Lake_defaultPackagesDir);
    l_Lake_defaultLeanConfigFile = _init_l_Lake_defaultLeanConfigFile();
    lean_mark_persistent(l_Lake_defaultLeanConfigFile);
    l_Lake_defaultTomlConfigFile = _init_l_Lake_defaultTomlConfigFile();
    lean_mark_persistent(l_Lake_defaultTomlConfigFile);
    l_Lake_defaultBuildDir = _init_l_Lake_defaultBuildDir();
    lean_mark_persistent(l_Lake_defaultBuildDir);
    l_Lake_defaultLeanLibDir = _init_l_Lake_defaultLeanLibDir();
    lean_mark_persistent(l_Lake_defaultLeanLibDir);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Defaults(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Defaults(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_FilePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Defaults(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Defaults(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_Defaults(builtin);
}
