// Lean compiler output
// Module: Std.Time.Zoned.Database
// Imports: Std.Time.Zoned.ZonedDateTime Std.Time.Zoned.Database.Basic Std.Time.Zoned.Database.TZdb Std.Time.Zoned.Database.Windows Init.System.Platform
use crate::r#gen::Init::System::Platform::{
    initialize_Init_System_Platform, l_System_Platform_isWindows,
    runtime_initialize_Init_System_Platform,
};
use crate::r#gen::Std::Time::Zoned::Database::Basic::{
    initialize_Std_Time_Zoned_Database_Basic, runtime_initialize_Std_Time_Zoned_Database_Basic,
};
use crate::r#gen::Std::Time::Zoned::Database::TZdb::{
    initialize_Std_Time_Zoned_Database_TZdb, l_Std_Time_Database_TZdb_default,
    l_Std_Time_Database_TZdb_getLocalZoneRules, l_Std_Time_Database_TZdb_getZoneRules,
    runtime_initialize_Std_Time_Zoned_Database_TZdb,
};
use crate::r#gen::Std::Time::Zoned::Database::Windows::{
    initialize_Std_Time_Zoned_Database_Windows, l_Std_Time_Database_Windows_getZoneRules,
    runtime_initialize_Std_Time_Zoned_Database_Windows,
};
use crate::r#gen::Std::Time::Zoned::ZonedDateTime::{
    initialize_Std_Time_Zoned_ZonedDateTime, runtime_initialize_Std_Time_Zoned_ZonedDateTime,
};
use crate::ffi::{lean_int64_neg, lean_int64_of_nat};
use crate::ffi::lean_get_windows_local_timezone_id_at;
static mut l_Std_Time_Database_defaultGetLocalZoneRules___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Database_defaultGetLocalZoneRules___closed__0: u64 = 0;
static mut l_Std_Time_Database_defaultGetLocalZoneRules___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Database_defaultGetLocalZoneRules___closed__1: u64 = 0;
pub unsafe fn l_Std_Time_Database_defaultGetZoneRules(
    mut v_name_32_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_34_: u8 = 0;
    v___x_34_ = l_System_Platform_isWindows;
    if v___x_34_ == 0 {
        let mut v___x_35_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_35_ = l_Std_Time_Database_TZdb_default;
        v___x_36_ = l_Std_Time_Database_TZdb_getZoneRules(v___x_35_, v_name_32_);
        return v___x_36_;
    } else {
        let mut v___x_37_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_37_ = l_Std_Time_Database_Windows_getZoneRules(v_name_32_);
        crate::leanh::lean_dec_ref(v_name_32_);
        return v___x_37_;
    }
}
pub unsafe fn l_Std_Time_Database_defaultGetZoneRules___boxed(
    mut v_name_38_: *mut crate::leanh::LeanObject,
    mut v_a_39_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_40_ = l_Std_Time_Database_defaultGetZoneRules(v_name_38_);
    return v_res_40_;
}
pub unsafe fn _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__0() -> u64 {
    let mut v___x_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_42_: u64 = 0;
    v___x_41_ = crate::leanh::lean_unsigned_to_nat(2147483648);
    v___x_42_ = lean_int64_of_nat(v___x_41_);
    return v___x_42_;
}
pub unsafe fn _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__1() -> u64 {
    let mut v___x_43_: u64 = 0;
    let mut v___x_44_: u64 = 0;
    v___x_43_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Std_Time_Database_defaultGetLocalZoneRules___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Database_defaultGetLocalZoneRules___closed__0_once),
        _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__0,
    );
    v___x_44_ = lean_int64_neg(v___x_43_);
    return v___x_44_;
}
pub unsafe fn l_Std_Time_Database_defaultGetLocalZoneRules() -> *mut crate::leanh::LeanObject {
    let mut v___x_46_: u8 = 0;
    let mut v___x_47_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_49_: u64 = 0;
    let mut v___x_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_56_: u8 = 0;
    let mut v___x_58_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_59_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_60_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_46_ = l_System_Platform_isWindows;
                if v___x_46_ == 0 {
                    v___x_47_ = l_Std_Time_Database_TZdb_default;
                    v___x_48_ = l_Std_Time_Database_TZdb_getLocalZoneRules(v___x_47_);
                    return v___x_48_;
                } else {
                    v___x_49_ = crate::leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_Database_defaultGetLocalZoneRules___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_Database_defaultGetLocalZoneRules___closed__1_once
                        ),
                        _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__1,
                    );
                    v___x_50_ = lean_get_windows_local_timezone_id_at(v___x_49_);
                    if crate::leanh::lean_obj_tag(v___x_50_) == 0 {
                        v_a_51_ = crate::leanh::lean_ctor_get(v___x_50_, 0);
                        crate::leanh::lean_inc(v_a_51_);
                        crate::leanh::lean_dec_ref_known(v___x_50_, 1);
                        v___x_52_ = l_Std_Time_Database_Windows_getZoneRules(v_a_51_);
                        crate::leanh::lean_dec(v_a_51_);
                        return v___x_52_;
                    } else {
                        v_a_53_ = crate::leanh::lean_ctor_get(v___x_50_, 0);
                        v_isSharedCheck_60_ = (!crate::leanh::lean_is_exclusive(v___x_50_)) as u8;
                        if v_isSharedCheck_60_ == 0 {
                            v___x_55_ = v___x_50_;
                            v_isShared_56_ = v_isSharedCheck_60_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_53_);
                            crate::leanh::lean_dec(v___x_50_);
                            v___x_55_ = crate::leanh::lean_box(0);
                            v_isShared_56_ = v_isSharedCheck_60_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_56_ == 0 {
                    v___x_58_ = v___x_55_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_59_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_59_, 0, v_a_53_);
                    v___x_58_ = v_reuseFailAlloc_59_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_58_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_Database_defaultGetLocalZoneRules___boxed(
    mut v_a_61_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_62_ = l_Std_Time_Database_defaultGetLocalZoneRules();
    return v_res_62_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Zoned_Database(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Zoned_ZonedDateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_Database_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_Database_TZdb(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_Database_Windows(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Zoned_Database(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Zoned_Database(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Zoned_ZonedDateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Zoned_Database_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Zoned_Database_TZdb(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Zoned_Database_Windows(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_System_Platform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_Database(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Zoned_Database(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_Zoned_Database(builtin);
}
