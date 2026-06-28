// Lean compiler output
// Module: Init.Data.Int.Repr
// Imports: Init.Data.Repr Init.Data.String.Defs
use crate::r#gen::Init::Data::Repr::{
    initialize_Init_Data_Repr, l_Nat_reprFast, l_Repr_addAppParen,
    runtime_initialize_Init_Data_Repr,
};
use crate::r#gen::Init::Data::String::Defs::{
    initialize_Init_Data_String_Defs, runtime_initialize_Init_Data_String_Defs,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{lean_nat_add, lean_nat_sub};
static mut l_Int_repr___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_repr___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Int_repr___closed__1_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [45, 0],
    };
static mut l_Int_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_repr___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Int_instRepr___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int_instRepr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int_instRepr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_instRepr___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int_instRepr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_instRepr___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Int_repr___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v_natZero_32_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_33_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_natZero_32_ = crate::leanh::lean_unsigned_to_nat(0);
    v_intZero_33_ = lean_nat_to_int(v_natZero_32_);
    return v_intZero_33_;
}
pub unsafe fn l_Int_repr(
    mut v_x_35_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_intZero_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_37_: u8 = 0;
    v_intZero_36_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_repr___closed__0),
        core::ptr::addr_of_mut!(l_Int_repr___closed__0_once),
        _init_l_Int_repr___closed__0,
    );
    v_isNeg_37_ = lean_int_dec_lt(v_x_35_, v_intZero_36_);
    if v_isNeg_37_ == 0 {
        let mut v_a_38_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_38_ = lean_nat_abs(v_x_35_);
        v___x_39_ = l_Nat_reprFast(v_a_38_);
        return v___x_39_;
    } else {
        let mut v_abs_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_abs_40_ = lean_nat_abs(v_x_35_);
        v_one_41_ = crate::leanh::lean_unsigned_to_nat(1);
        v_a_42_ = lean_nat_sub(v_abs_40_, v_one_41_);
        crate::leanh::lean_dec(v_abs_40_);
        v___x_43_ = l_Int_repr___closed__1;
        v___x_44_ = lean_nat_add(v_a_42_, v_one_41_);
        crate::leanh::lean_dec(v_a_42_);
        v___x_45_ = l_Nat_reprFast(v___x_44_);
        v___x_46_ = lean_string_append(v___x_43_, v___x_45_);
        crate::leanh::lean_dec_ref(v___x_45_);
        return v___x_46_;
    }
}
pub unsafe fn l_Int_repr___boxed(
    mut v_x_47_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_48_ = l_Int_repr(v_x_47_);
    crate::leanh::lean_dec(v_x_47_);
    return v_res_48_;
}
pub unsafe fn l_Int_instRepr___lam__0(
    mut v_i_49_: *mut crate::leanh::LeanObject,
    mut v_prec_50_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_52_: u8 = 0;
    v___x_51_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_repr___closed__0),
        core::ptr::addr_of_mut!(l_Int_repr___closed__0_once),
        _init_l_Int_repr___closed__0,
    );
    v___x_52_ = lean_int_dec_lt(v_i_49_, v___x_51_);
    if v___x_52_ == 0 {
        let mut v___x_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_53_ = l_Int_repr(v_i_49_);
        v___x_54_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_54_, 0, v___x_53_);
        return v___x_54_;
    } else {
        let mut v___x_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_57_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_55_ = l_Int_repr(v_i_49_);
        v___x_56_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_56_, 0, v___x_55_);
        v___x_57_ = l_Repr_addAppParen(v___x_56_, v_prec_50_);
        return v___x_57_;
    }
}
pub unsafe fn l_Int_instRepr___lam__0___boxed(
    mut v_i_58_: *mut crate::leanh::LeanObject,
    mut v_prec_59_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_60_ = l_Int_instRepr___lam__0(v_i_58_, v_prec_59_);
    crate::leanh::lean_dec(v_prec_59_);
    crate::leanh::lean_dec(v_i_58_);
    return v_res_60_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Int_Repr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Repr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Int_Repr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Int_Repr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Repr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Repr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Int_Repr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Int_Repr(builtin);
}
