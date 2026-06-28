// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Stream
// Imports: Init.Data.Stream Init.Data.Iterators.Consumers.Monadic.Access
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Access::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Access,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access,
};
use crate::r#gen::Init::Data::Stream::{
    initialize_Init_Data_Stream, runtime_initialize_Init_Data_Stream,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub unsafe fn l_Std_instStreamIterOfProductiveOfIteratorAccessId___redArg___lam__0(
    mut v_inst_30_: *mut LeanObject,
    mut v_it_31_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_32_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_33_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_34_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_35_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_37_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_38_: u8 = 0;
    let mut v___x_40_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_41_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_42_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_43_: u8 = 0;
    let mut v___x_44_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_32_ = lean_unsigned_to_nat(0);
                v_val_33_ = lean_apply_2(v_inst_30_, v_it_31_, v___x_32_);
                if lean_obj_tag(v_val_33_) == 0 {
                    v_it_34_ = lean_ctor_get(v_val_33_, 0);
                    v_out_35_ = lean_ctor_get(v_val_33_, 1);
                    v_isSharedCheck_43_ = (!lean_is_exclusive(v_val_33_)) as u8;
                    if v_isSharedCheck_43_ == 0 {
                        v___x_37_ = v_val_33_;
                        v_isShared_38_ = v_isSharedCheck_43_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_out_35_);
                        lean_inc(v_it_34_);
                        lean_dec(v_val_33_);
                        v___x_37_ = lean_box(0);
                        v_isShared_38_ = v_isSharedCheck_43_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_44_ = lean_box(0);
                    return v___x_44_;
                }
            }
            1 => {
                if v_isShared_38_ == 0 {
                    lean_ctor_set(v___x_37_, 1, v_it_34_);
                    lean_ctor_set(v___x_37_, 0, v_out_35_);
                    v___x_40_ = v___x_37_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_42_, 0, v_out_35_);
                    lean_ctor_set(v_reuseFailAlloc_42_, 1, v_it_34_);
                    v___x_40_ = v_reuseFailAlloc_42_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_41_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_41_, 0, v___x_40_);
                return v___x_41_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_instStreamIterOfProductiveOfIteratorAccessId___redArg(
    mut v_inst_45_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_46_: *mut LeanObject = core::ptr::null_mut();
    v___f_46_ = lean_alloc_closure(
        l_Std_instStreamIterOfProductiveOfIteratorAccessId___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_46_, 0, v_inst_45_);
    return v___f_46_;
}
pub unsafe fn l_Std_instStreamIterOfProductiveOfIteratorAccessId(
    mut v_00_u03b1_47_: *mut LeanObject,
    mut v_00_u03b2_48_: *mut LeanObject,
    mut v_inst_49_: *mut LeanObject,
    mut v_inst_50_: *mut LeanObject,
    mut v_inst_51_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_52_: *mut LeanObject = core::ptr::null_mut();
    v___f_52_ = lean_alloc_closure(
        l_Std_instStreamIterOfProductiveOfIteratorAccessId___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_52_, 0, v_inst_51_);
    return v___f_52_;
}
pub unsafe fn l_Std_instStreamIterOfProductiveOfIteratorAccessId___boxed(
    mut v_00_u03b1_53_: *mut LeanObject,
    mut v_00_u03b2_54_: *mut LeanObject,
    mut v_inst_55_: *mut LeanObject,
    mut v_inst_56_: *mut LeanObject,
    mut v_inst_57_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_58_: *mut LeanObject = core::ptr::null_mut();
    v_res_58_ = l_Std_instStreamIterOfProductiveOfIteratorAccessId(
        v_00_u03b1_53_,
        v_00_u03b2_54_,
        v_inst_55_,
        v_inst_56_,
        v_inst_57_,
    );
    lean_dec(v_inst_55_);
    return v_res_58_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Consumers_Stream(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Stream(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Consumers_Stream(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Iterators_Consumers_Stream(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Stream(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Stream(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Consumers_Stream(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Consumers_Stream(builtin);
}
