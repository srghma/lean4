// Lean compiler output
// Module: Init.Data.Option.BasicAux
// Imports: Init.Util
use crate::r#gen::Init::Prelude::l_panic___redArg;
use crate::r#gen::Init::Util::{
    initialize_Init_Util, l_mkPanicMessageWithDecl, runtime_initialize_Init_Util,
};
pub static l_Option_get_x21___redArg___closed__0_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
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
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97,
            115, 105, 99, 65, 117, 120, 0,
        ],
    };
static mut l_Option_get_x21___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Option_get_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_get_x21___redArg___closed__1_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
    };
static mut l_Option_get_x21___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Option_get_x21___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_get_x21___redArg___closed__2_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
        ],
    };
static mut l_Option_get_x21___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Option_get_x21___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Option_get_x21___redArg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Option_get_x21___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Option_get_x21___redArg___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_31_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_32_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_33_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_34_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_35_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_31_ = l_Option_get_x21___redArg___closed__2;
    v___x_32_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_33_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_34_ = l_Option_get_x21___redArg___closed__1;
    v___x_35_ = l_Option_get_x21___redArg___closed__0;
    v___x_36_ = l_mkPanicMessageWithDecl(v___x_35_, v___x_34_, v___x_33_, v___x_32_, v___x_31_);
    return v___x_36_;
}
pub unsafe fn l_Option_get_x21___redArg(
    mut v_inst_37_: *mut crate::leanh::LeanObject,
    mut v_x_38_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_38_) == 0 {
        let mut v___x_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_39_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Option_get_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Option_get_x21___redArg___closed__3_once),
            _init_l_Option_get_x21___redArg___closed__3,
        );
        v___x_40_ = l_panic___redArg(v_inst_37_, v___x_39_);
        return v___x_40_;
    } else {
        let mut v_val_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_41_ = crate::leanh::lean_ctor_get(v_x_38_, 0);
        crate::leanh::lean_inc(v_val_41_);
        return v_val_41_;
    }
}
pub unsafe fn l_Option_get_x21___redArg___boxed(
    mut v_inst_42_: *mut crate::leanh::LeanObject,
    mut v_x_43_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_44_ = l_Option_get_x21___redArg(v_inst_42_, v_x_43_);
    crate::leanh::lean_dec(v_x_43_);
    crate::leanh::lean_dec(v_inst_42_);
    return v_res_44_;
}
pub unsafe fn l_Option_get_x21(
    mut v_00_u03b1_45_: *mut crate::leanh::LeanObject,
    mut v_inst_46_: *mut crate::leanh::LeanObject,
    mut v_x_47_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_47_) == 0 {
        let mut v___x_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_48_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Option_get_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Option_get_x21___redArg___closed__3_once),
            _init_l_Option_get_x21___redArg___closed__3,
        );
        v___x_49_ = l_panic___redArg(v_inst_46_, v___x_48_);
        return v___x_49_;
    } else {
        let mut v_val_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_50_ = crate::leanh::lean_ctor_get(v_x_47_, 0);
        crate::leanh::lean_inc(v_val_50_);
        return v_val_50_;
    }
}
pub unsafe fn l_Option_get_x21___boxed(
    mut v_00_u03b1_51_: *mut crate::leanh::LeanObject,
    mut v_inst_52_: *mut crate::leanh::LeanObject,
    mut v_x_53_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_54_ = l_Option_get_x21(v_00_u03b1_51_, v_inst_52_, v_x_53_);
    crate::leanh::lean_dec(v_x_53_);
    crate::leanh::lean_dec(v_inst_52_);
    return v_res_54_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Option_BasicAux(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Option_BasicAux(
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
pub unsafe fn initialize_Init_Data_Option_BasicAux(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Option_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Option_BasicAux(builtin);
}
