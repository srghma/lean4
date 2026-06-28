// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Telescope
// Imports: Lean.Meta.Sym.Simp.SimpM Lean.Meta.Sym.Simp.Have Lean.Meta.Sym.Simp.Forall
use crate::r#gen::Lean::Meta::Sym::Simp::Forall::{
    initialize_Lean_Meta_Sym_Simp_Forall, l_Lean_Meta_Sym_Simp_simpArrowTelescope___boxed,
    l_Lean_Meta_Sym_Simp_simpForall_x27, runtime_initialize_Lean_Meta_Sym_Simp_Forall,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Have::{
    initialize_Lean_Meta_Sym_Simp_Have, l_Lean_Meta_Sym_Simp_simpLet_x27,
    runtime_initialize_Lean_Meta_Sym_Simp_Have,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Lambda::l_Lean_Meta_Sym_Simp_simpLambda_x27___boxed;
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    initialize_Lean_Meta_Sym_Simp_SimpM, runtime_initialize_Lean_Meta_Sym_Simp_SimpM,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_set, lean_dec, lean_dec_ref, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub static l_Lean_Meta_Sym_Simp_simpTelescope___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [0 as *mut LeanObject],
    };
static mut l_Lean_Meta_Sym_Simp_simpTelescope___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpTelescope___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Sym_Simp_simpTelescope___boxed(
    mut v_e_37_: *mut LeanObject,
    mut v_a_38_: *mut LeanObject,
    mut v_a_39_: *mut LeanObject,
    mut v_a_40_: *mut LeanObject,
    mut v_a_41_: *mut LeanObject,
    mut v_a_42_: *mut LeanObject,
    mut v_a_43_: *mut LeanObject,
    mut v_a_44_: *mut LeanObject,
    mut v_a_45_: *mut LeanObject,
    mut v_a_46_: *mut LeanObject,
    mut v_a_47_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_48_: *mut LeanObject = core::ptr::null_mut();
    v_res_48_ = l_Lean_Meta_Sym_Simp_simpTelescope(
        v_e_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_,
    );
    lean_dec(v_a_46_);
    lean_dec_ref(v_a_45_);
    lean_dec(v_a_44_);
    lean_dec_ref(v_a_43_);
    lean_dec(v_a_42_);
    lean_dec_ref(v_a_41_);
    lean_dec(v_a_40_);
    lean_dec_ref(v_a_39_);
    lean_dec(v_a_38_);
    return v_res_48_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpTelescope(
    mut v_e_49_: *mut LeanObject,
    mut v_a_50_: *mut LeanObject,
    mut v_a_51_: *mut LeanObject,
    mut v_a_52_: *mut LeanObject,
    mut v_a_53_: *mut LeanObject,
    mut v_a_54_: *mut LeanObject,
    mut v_a_55_: *mut LeanObject,
    mut v_a_56_: *mut LeanObject,
    mut v_a_57_: *mut LeanObject,
    mut v_a_58_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_e_49_) {
        8 => {
            let mut v___x_60_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_61_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
            v___x_60_ = lean_alloc_closure(
                l_Lean_Meta_Sym_Simp_simpTelescope___boxed as *mut core::ffi::c_void,
                11,
                0,
            );
            v___x_61_ = lean_alloc_closure(
                l_Lean_Meta_Sym_Simp_simpLambda_x27___boxed as *mut core::ffi::c_void,
                12,
                1,
            );
            lean_closure_set(v___x_61_, 0, v___x_60_);
            v___x_62_ = l_Lean_Meta_Sym_Simp_simpLet_x27(
                v___x_61_, v_e_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_,
                v_a_57_, v_a_58_,
            );
            return v___x_62_;
        }
        7 => {
            let mut v___x_63_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_64_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_65_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_66_: *mut LeanObject = core::ptr::null_mut();
            v___x_63_ = lean_alloc_closure(
                l_Lean_Meta_Sym_Simp_simpTelescope___boxed as *mut core::ffi::c_void,
                11,
                0,
            );
            lean_inc_ref(v___x_63_);
            v___x_64_ = lean_alloc_closure(
                l_Lean_Meta_Sym_Simp_simpArrowTelescope___boxed as *mut core::ffi::c_void,
                12,
                1,
            );
            lean_closure_set(v___x_64_, 0, v___x_63_);
            v___x_65_ = lean_alloc_closure(
                l_Lean_Meta_Sym_Simp_simpLambda_x27___boxed as *mut core::ffi::c_void,
                12,
                1,
            );
            lean_closure_set(v___x_65_, 0, v___x_63_);
            v___x_66_ = l_Lean_Meta_Sym_Simp_simpForall_x27(
                v___x_64_, v___x_65_, v_e_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_,
                v_a_55_, v_a_56_, v_a_57_, v_a_58_,
            );
            return v___x_66_;
        }
        _ => {
            let mut v___x_67_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_68_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_e_49_);
            v___x_67_ = l_Lean_Meta_Sym_Simp_simpTelescope___closed__0;
            v___x_68_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_68_, 0, v___x_67_);
            return v___x_68_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_Telescope(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Have(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Forall(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_Telescope(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Simp_Telescope(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Have(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Forall(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
}
