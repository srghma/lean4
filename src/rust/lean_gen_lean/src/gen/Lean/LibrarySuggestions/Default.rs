// Lean compiler output
// Module: Lean.LibrarySuggestions.Default
// Imports: Lean.LibrarySuggestions.SineQuaNon
use crate::r#gen::Init::Data::OfScientific::l_Float_ofScientific;
use crate::r#gen::Lean::LibrarySuggestions::Basic::{
    l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___boxed,
    l_Lean_LibrarySuggestions_Selector_intersperse, l_Lean_LibrarySuggestions_currentFile___boxed,
};
use crate::r#gen::Lean::LibrarySuggestions::SineQuaNon::{
    initialize_Lean_LibrarySuggestions_SineQuaNon,
    l_Lean_LibrarySuggestions_sineQuaNonSelector___boxed,
    runtime_initialize_Lean_LibrarySuggestions_SineQuaNon,
};
static mut l_Lean_LibrarySuggestions___librarySuggestions___closed__0_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_LibrarySuggestions___librarySuggestions___closed__0_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_: f64 = 0.0;
pub static mut l_Lean_LibrarySuggestions___librarySuggestions___closed__1___boxed__const__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_LibrarySuggestions___librarySuggestions___closed__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_LibrarySuggestions___librarySuggestions___closed__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_LibrarySuggestions___librarySuggestions___closed__2_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_LibrarySuggestions___librarySuggestions___closed__2_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_LibrarySuggestions___librarySuggestions___closed__3_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_LibrarySuggestions___librarySuggestions___closed__3_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_: f64 = 0.0;
pub unsafe fn _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__0_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_()
-> f64 {
    let mut v___x_34_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_35_: u8 = 0;
    let mut v___x_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_37_: f64 = 0.0;
    v___x_34_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_35_ = 1;
    v___x_36_ = crate::leanh::lean_unsigned_to_nat(15);
    v___x_37_ = l_Float_ofScientific(v___x_36_, v___x_35_, v___x_34_);
    return v___x_37_;
}
pub unsafe fn _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__1___boxed__const__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_38_: f64 = 0.0;
    let mut v___x_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_38_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_LibrarySuggestions___librarySuggestions___closed__0_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l_Lean_LibrarySuggestions___librarySuggestions___closed__0_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2__once), _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__0_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_);
    v___x_39_ = crate::leanh::lean_box_float(v___x_38_);
    return v___x_39_;
}
pub unsafe fn _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_40_ = l_Lean_LibrarySuggestions___librarySuggestions___closed__1___boxed__const__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_;
    v___x_41_ = crate::leanh::lean_alloc_closure(
        l_Lean_LibrarySuggestions_sineQuaNonSelector___boxed as *mut core::ffi::c_void,
        8,
        1,
    );
    crate::leanh::lean_closure_set(v___x_41_, 0, v___x_40_);
    return v___x_41_;
}
pub unsafe fn _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__2_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_42_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_LibrarySuggestions___librarySuggestions___closed__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l_Lean_LibrarySuggestions___librarySuggestions___closed__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2__once), _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_);
    v___x_43_ = crate::leanh::lean_alloc_closure(
        l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___boxed as *mut core::ffi::c_void,
        8,
        1,
    );
    crate::leanh::lean_closure_set(v___x_43_, 0, v___x_42_);
    return v___x_43_;
}
pub unsafe fn _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__3_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_()
-> f64 {
    let mut v___x_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_45_: u8 = 0;
    let mut v___x_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_47_: f64 = 0.0;
    v___x_44_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_45_ = 1;
    v___x_46_ = crate::leanh::lean_unsigned_to_nat(5);
    v___x_47_ = l_Float_ofScientific(v___x_46_, v___x_45_, v___x_44_);
    return v___x_47_;
}
pub unsafe fn l_Lean_LibrarySuggestions___librarySuggestions_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_(
    mut v_a_48_: *mut crate::leanh::LeanObject,
    mut v_a_49_: *mut crate::leanh::LeanObject,
    mut v_a_50_: *mut crate::leanh::LeanObject,
    mut v_a_51_: *mut crate::leanh::LeanObject,
    mut v_a_52_: *mut crate::leanh::LeanObject,
    mut v_a_53_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_57_: f64 = 0.0;
    let mut v___x_58_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_55_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_LibrarySuggestions___librarySuggestions___closed__2_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l_Lean_LibrarySuggestions___librarySuggestions___closed__2_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2__once), _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__2_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_);
    v___x_56_ = crate::leanh::lean_alloc_closure(
        l_Lean_LibrarySuggestions_currentFile___boxed as *mut core::ffi::c_void,
        7,
        0,
    );
    v___x_57_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_LibrarySuggestions___librarySuggestions___closed__3_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l_Lean_LibrarySuggestions___librarySuggestions___closed__3_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2__once), _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__3_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_);
    v___x_58_ = l_Lean_LibrarySuggestions_Selector_intersperse(
        v___x_55_, v___x_56_, v___x_57_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_,
    );
    return v___x_58_;
}
pub unsafe fn l_Lean_LibrarySuggestions___librarySuggestions_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2____boxed(
    mut v_a_59_: *mut crate::leanh::LeanObject,
    mut v_a_60_: *mut crate::leanh::LeanObject,
    mut v_a_61_: *mut crate::leanh::LeanObject,
    mut v_a_62_: *mut crate::leanh::LeanObject,
    mut v_a_63_: *mut crate::leanh::LeanObject,
    mut v_a_64_: *mut crate::leanh::LeanObject,
    mut v_a_65_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_66_ = l_Lean_LibrarySuggestions___librarySuggestions_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_(v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
    crate::leanh::lean_dec(v_a_64_);
    crate::leanh::lean_dec_ref(v_a_63_);
    crate::leanh::lean_dec(v_a_62_);
    crate::leanh::lean_dec_ref(v_a_61_);
    return v_res_66_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_LibrarySuggestions_Default(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    l_Lean_LibrarySuggestions___librarySuggestions___closed__1___boxed__const__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_ = _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__1___boxed__const__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_();
    crate::leanh::lean_mark_persistent(l_Lean_LibrarySuggestions___librarySuggestions___closed__1___boxed__const__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_LibrarySuggestions_Default(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_LibrarySuggestions_SineQuaNon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_LibrarySuggestions_Default(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_LibrarySuggestions_SineQuaNon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_LibrarySuggestions_Default(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_LibrarySuggestions_Default(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_LibrarySuggestions_Default(builtin);
}
