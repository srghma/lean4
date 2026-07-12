use leanh_l1::{
    datatypes::{LeanObject, LeanOnceCell, LeanStringObject},
    emitted::{lean_box::lean_box, lean_obj_once::lean_obj_once},
};

use crate::todo_import_from_lean::lean_name_mk_string::lean_name_mk_string;

static mut OUT_PARAM_NAME___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut OUT_PARAM_NAME___closed__0: *mut LeanObject = core::ptr::null_mut();
static OUT_PARAM_NAME___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: leanh_l1::datatypes::LeanObject::new(0, 0, 0, leanh_l1::datatypes::LeanObjectTag::String),
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [111, 117, 116, 80, 97, 114, 97, 109, 0],
};

static mut SEMI_OUT_PARAM_NAME___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut SEMI_OUT_PARAM_NAME___closed__0: *mut LeanObject = core::ptr::null_mut();
static SEMI_OUT_PARAM_NAME___closed__0_value: LeanStringObject<13> = LeanStringObject {
    m_header: leanh_l1::datatypes::LeanObject::new(0, 0, 0, leanh_l1::datatypes::LeanObjectTag::String),
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [115, 101, 109, 105, 79, 117, 116, 80, 97, 114, 97, 109, 0],
};

static mut OPT_PARAM_NAME___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut OPT_PARAM_NAME___closed__0: *mut LeanObject = core::ptr::null_mut();
static OPT_PARAM_NAME___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: leanh_l1::datatypes::LeanObject::new(0, 0, 0, leanh_l1::datatypes::LeanObjectTag::String),
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [111, 112, 116, 80, 97, 114, 97, 109, 0],
};

static mut AUTO_PARAM_NAME___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut AUTO_PARAM_NAME___closed__0: *mut LeanObject = core::ptr::null_mut();
static AUTO_PARAM_NAME___closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: leanh_l1::datatypes::LeanObject::new(0, 0, 0, leanh_l1::datatypes::LeanObjectTag::String),
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [97, 117, 116, 111, 80, 97, 114, 97, 109, 0],
};

unsafe fn init_out_param_name() -> *mut LeanObject {
    lean_name_mk_string(
        lean_box(0),
        core::ptr::addr_of!(OUT_PARAM_NAME___closed__0_value) as *mut LeanObject,
    )
}

unsafe fn init_semi_out_param_name() -> *mut LeanObject {
    lean_name_mk_string(
        lean_box(0),
        core::ptr::addr_of!(SEMI_OUT_PARAM_NAME___closed__0_value) as *mut LeanObject,
    )
}

unsafe fn init_opt_param_name() -> *mut LeanObject {
    lean_name_mk_string(
        lean_box(0),
        core::ptr::addr_of!(OPT_PARAM_NAME___closed__0_value) as *mut LeanObject,
    )
}

unsafe fn init_auto_param_name() -> *mut LeanObject {
    lean_name_mk_string(
        lean_box(0),
        core::ptr::addr_of!(AUTO_PARAM_NAME___closed__0_value) as *mut LeanObject,
    )
}

#[inline]
pub unsafe fn out_param_name() -> *mut LeanObject {
    lean_obj_once(
        core::ptr::addr_of_mut!(OUT_PARAM_NAME___closed__0),
        core::ptr::addr_of_mut!(OUT_PARAM_NAME___closed__0_once),
        init_out_param_name,
    )
}

#[inline]
pub unsafe fn semi_out_param_name() -> *mut LeanObject {
    lean_obj_once(
        core::ptr::addr_of_mut!(SEMI_OUT_PARAM_NAME___closed__0),
        core::ptr::addr_of_mut!(SEMI_OUT_PARAM_NAME___closed__0_once),
        init_semi_out_param_name,
    )
}

#[inline]
pub unsafe fn opt_param_name() -> *mut LeanObject {
    lean_obj_once(
        core::ptr::addr_of_mut!(OPT_PARAM_NAME___closed__0),
        core::ptr::addr_of_mut!(OPT_PARAM_NAME___closed__0_once),
        init_opt_param_name,
    )
}

#[inline]
pub unsafe fn auto_param_name() -> *mut LeanObject {
    lean_obj_once(
        core::ptr::addr_of_mut!(AUTO_PARAM_NAME___closed__0),
        core::ptr::addr_of_mut!(AUTO_PARAM_NAME___closed__0_once),
        init_auto_param_name,
    )
}
