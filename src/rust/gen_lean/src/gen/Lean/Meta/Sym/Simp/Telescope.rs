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
pub static l_Lean_Meta_Sym_Simp_simpTelescope___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [0 as *mut leanh::LeanObject],
    };
static mut l_Lean_Meta_Sym_Simp_simpTelescope___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpTelescope___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Sym_Simp_simpTelescope___boxed(
    mut v_e_37_: *mut leanh::LeanObject,
    mut v_a_38_: *mut leanh::LeanObject,
    mut v_a_39_: *mut leanh::LeanObject,
    mut v_a_40_: *mut leanh::LeanObject,
    mut v_a_41_: *mut leanh::LeanObject,
    mut v_a_42_: *mut leanh::LeanObject,
    mut v_a_43_: *mut leanh::LeanObject,
    mut v_a_44_: *mut leanh::LeanObject,
    mut v_a_45_: *mut leanh::LeanObject,
    mut v_a_46_: *mut leanh::LeanObject,
    mut v_a_47_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_48_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_48_ = l_Lean_Meta_Sym_Simp_simpTelescope(
        v_e_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_,
    );
    leanh::lean_dec(v_a_46_);
    leanh::lean_dec_ref(v_a_45_);
    leanh::lean_dec(v_a_44_);
    leanh::lean_dec_ref(v_a_43_);
    leanh::lean_dec(v_a_42_);
    leanh::lean_dec_ref(v_a_41_);
    leanh::lean_dec(v_a_40_);
    leanh::lean_dec_ref(v_a_39_);
    leanh::lean_dec(v_a_38_);
    return v_res_48_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpTelescope(
    mut v_e_49_: *mut leanh::LeanObject,
    mut v_a_50_: *mut leanh::LeanObject,
    mut v_a_51_: *mut leanh::LeanObject,
    mut v_a_52_: *mut leanh::LeanObject,
    mut v_a_53_: *mut leanh::LeanObject,
    mut v_a_54_: *mut leanh::LeanObject,
    mut v_a_55_: *mut leanh::LeanObject,
    mut v_a_56_: *mut leanh::LeanObject,
    mut v_a_57_: *mut leanh::LeanObject,
    mut v_a_58_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_e_49_) {
        8 => {
            let mut v___x_60_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_61_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_62_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_60_ = leanh::lean_alloc_closure(
                l_Lean_Meta_Sym_Simp_simpTelescope___boxed as *mut core::ffi::c_void,
                11,
                0,
            );
            v___x_61_ = leanh::lean_alloc_closure(
                l_Lean_Meta_Sym_Simp_simpLambda_x27___boxed as *mut core::ffi::c_void,
                12,
                1,
            );
            leanh::lean_closure_set(v___x_61_, 0, v___x_60_);
            v___x_62_ = l_Lean_Meta_Sym_Simp_simpLet_x27(
                v___x_61_, v_e_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_,
                v_a_57_, v_a_58_,
            );
            return v___x_62_;
        }
        7 => {
            let mut v___x_63_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_64_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_65_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_66_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_63_ = leanh::lean_alloc_closure(
                l_Lean_Meta_Sym_Simp_simpTelescope___boxed as *mut core::ffi::c_void,
                11,
                0,
            );
            leanh::lean_inc_ref(v___x_63_);
            v___x_64_ = leanh::lean_alloc_closure(
                l_Lean_Meta_Sym_Simp_simpArrowTelescope___boxed as *mut core::ffi::c_void,
                12,
                1,
            );
            leanh::lean_closure_set(v___x_64_, 0, v___x_63_);
            v___x_65_ = leanh::lean_alloc_closure(
                l_Lean_Meta_Sym_Simp_simpLambda_x27___boxed as *mut core::ffi::c_void,
                12,
                1,
            );
            leanh::lean_closure_set(v___x_65_, 0, v___x_63_);
            v___x_66_ = l_Lean_Meta_Sym_Simp_simpForall_x27(
                v___x_64_, v___x_65_, v_e_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_,
                v_a_55_, v_a_56_, v_a_57_, v_a_58_,
            );
            return v___x_66_;
        }
        _ => {
            let mut v___x_67_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_68_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_e_49_);
            v___x_67_ = l_Lean_Meta_Sym_Simp_simpTelescope___closed__0;
            v___x_68_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_68_, 0, v___x_67_);
            return v___x_68_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_Telescope(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Have(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Forall(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_Telescope(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Simp_Telescope(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Have(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Forall(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
}