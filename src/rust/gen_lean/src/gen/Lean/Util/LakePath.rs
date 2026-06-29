// Lean compiler output
// Module: Lean.Util.LakePath
// Imports: Init.System.IO
use crate::r#gen::Init::System::FilePath::l_System_FilePath_join;
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, l_IO_appDir, runtime_initialize_Init_System_IO,
};
use crate::ffi::lean_io_getenv;
pub static l_Lean_determineLakePath___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [76, 65, 75, 69, 0],
    };
static mut l_Lean_determineLakePath___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_determineLakePath___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_determineLakePath___closed__1_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [76, 69, 65, 78, 95, 83, 89, 83, 82, 79, 79, 84, 0],
    };
static mut l_Lean_determineLakePath___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_determineLakePath___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_determineLakePath___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [108, 97, 107, 101, 0],
    };
static mut l_Lean_determineLakePath___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_determineLakePath___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_determineLakePath___closed__3_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_determineLakePath___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_determineLakePath___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_determineLakePath() -> *mut crate::leanh::LeanObject {
    let mut v___x_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_53_: u8 = 0;
    let mut v___x_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_57_: u8 = 0;
    let mut v___x_58_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_59_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_64_: u8 = 0;
    let mut v___x_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_68_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_69_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_70_: u8 = 0;
    let mut v_val_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_74_: u8 = 0;
    let mut v___x_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_81_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_82_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_48_ = l_Lean_determineLakePath___closed__0;
                v___x_49_ = lean_io_getenv(v___x_48_);
                if crate::leanh::lean_obj_tag(v___x_49_) == 1 {
                    v_val_50_ = crate::leanh::lean_ctor_get(v___x_49_, 0);
                    v_isSharedCheck_57_ = (!crate::leanh::lean_is_exclusive(v___x_49_)) as u8;
                    if v_isSharedCheck_57_ == 0 {
                        v___x_52_ = v___x_49_;
                        v_isShared_53_ = v_isSharedCheck_57_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_50_);
                        crate::leanh::lean_dec(v___x_49_);
                        v___x_52_ = crate::leanh::lean_box(0);
                        v_isShared_53_ = v_isSharedCheck_57_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_49_);
                    v___x_58_ = l_Lean_determineLakePath___closed__1;
                    v___x_59_ = lean_io_getenv(v___x_58_);
                    if crate::leanh::lean_obj_tag(v___x_59_) == 0 {
                        v___x_60_ = l_IO_appDir();
                        if crate::leanh::lean_obj_tag(v___x_60_) == 0 {
                            v_a_61_ = crate::leanh::lean_ctor_get(v___x_60_, 0);
                            v_isSharedCheck_70_ =
                                (!crate::leanh::lean_is_exclusive(v___x_60_)) as u8;
                            if v_isSharedCheck_70_ == 0 {
                                v___x_63_ = v___x_60_;
                                v_isShared_64_ = v_isSharedCheck_70_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_61_);
                                crate::leanh::lean_dec(v___x_60_);
                                v___x_63_ = crate::leanh::lean_box(0);
                                v_isShared_64_ = v_isSharedCheck_70_;
                                state = 3;
                                continue;
                            }
                        } else {
                            return v___x_60_;
                        }
                    } else {
                        v_val_71_ = crate::leanh::lean_ctor_get(v___x_59_, 0);
                        v_isSharedCheck_82_ = (!crate::leanh::lean_is_exclusive(v___x_59_)) as u8;
                        if v_isSharedCheck_82_ == 0 {
                            v___x_73_ = v___x_59_;
                            v_isShared_74_ = v_isSharedCheck_82_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_71_);
                            crate::leanh::lean_dec(v___x_59_);
                            v___x_73_ = crate::leanh::lean_box(0);
                            v_isShared_74_ = v_isSharedCheck_82_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_53_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_52_, 0);
                    v___x_55_ = v___x_52_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_56_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_56_, 0, v_val_50_);
                    v___x_55_ = v_reuseFailAlloc_56_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_55_;
            }
            3 => {
                v___x_65_ = l_Lean_determineLakePath___closed__2;
                v___x_66_ = l_System_FilePath_join(v_a_61_, v___x_65_);
                if v_isShared_64_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_63_, 0, v___x_66_);
                    v___x_68_ = v___x_63_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_69_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_66_);
                    v___x_68_ = v_reuseFailAlloc_69_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_68_;
            }
            5 => {
                v___x_75_ = l_Lean_determineLakePath___closed__3;
                v___x_76_ = l_System_FilePath_join(v_val_71_, v___x_75_);
                v___x_77_ = l_Lean_determineLakePath___closed__2;
                v___x_78_ = l_System_FilePath_join(v___x_76_, v___x_77_);
                if v_isShared_74_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_73_, 0);
                    crate::leanh::lean_ctor_set(v___x_73_, 0, v___x_78_);
                    v___x_80_ = v___x_73_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_81_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_78_);
                    v___x_80_ = v_reuseFailAlloc_81_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_80_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_determineLakePath___boxed(
    mut v_a_83_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_84_ = l_Lean_determineLakePath();
    return v_res_84_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_LakePath(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_LakePath(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_LakePath(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_LakePath(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_LakePath(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_LakePath(builtin);
}
