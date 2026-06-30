// Lean compiler output
// Module: Init.Control.MonadAttach
// Imports: Init.Core
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
pub static l_MonadAttach_trivial___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_MonadAttach_trivial___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_MonadAttach_trivial___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_MonadAttach_trivial___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_MonadAttach_pbind___redArg___lam__0(
    mut v_f_38_: *mut leanh::LeanObject,
    mut v_x_39_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_40_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_40_ = leanh::lean_apply_2(v_f_38_, v_x_39_, leanh::lean_box(0));
    return v___x_40_;
}
pub unsafe fn l_MonadAttach_pbind___redArg(
    mut v_inst_41_: *mut leanh::LeanObject,
    mut v_inst_42_: *mut leanh::LeanObject,
    mut v_x_43_: *mut leanh::LeanObject,
    mut v_f_44_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_45_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_46_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_47_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_48_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_45_ = leanh::lean_ctor_get(v_inst_41_, 1);
    leanh::lean_inc(v_toBind_45_);
    leanh::lean_dec_ref(v_inst_41_);
    v___f_46_ = leanh::lean_alloc_closure(
        l_MonadAttach_pbind___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_46_, 0, v_f_44_);
    v___x_47_ = leanh::lean_apply_2(v_inst_42_, leanh::lean_box(0), v_x_43_);
    v___x_48_ = leanh::lean_apply_4(
        v_toBind_45_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_47_,
        v___f_46_,
    );
    return v___x_48_;
}
pub unsafe fn l_MonadAttach_pbind(
    mut v_m_49_: *mut leanh::LeanObject,
    mut v_00_u03b1_50_: *mut leanh::LeanObject,
    mut v_00_u03b2_51_: *mut leanh::LeanObject,
    mut v_inst_52_: *mut leanh::LeanObject,
    mut v_inst_53_: *mut leanh::LeanObject,
    mut v_x_54_: *mut leanh::LeanObject,
    mut v_f_55_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_56_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_56_ = l_MonadAttach_pbind___redArg(v_inst_52_, v_inst_53_, v_x_54_, v_f_55_);
    return v___x_56_;
}
pub unsafe fn l_MonadAttach_trivial___redArg___lam__0(
    mut v_x_57_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_57_);
    return v_x_57_;
}
pub unsafe fn l_MonadAttach_trivial___redArg___lam__0___boxed(
    mut v_x_58_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_59_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_59_ = l_MonadAttach_trivial___redArg___lam__0(v_x_58_);
    leanh::lean_dec(v_x_58_);
    return v_res_59_;
}
pub unsafe fn l_MonadAttach_trivial___redArg___lam__1(
    mut v_toFunctor_60_: *mut leanh::LeanObject,
    mut v___f_61_: *mut leanh::LeanObject,
    mut v_00_u03b1_62_: *mut leanh::LeanObject,
    mut v_x_63_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_64_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_65_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_64_ = leanh::lean_ctor_get(v_toFunctor_60_, 0);
    leanh::lean_inc(v_map_64_);
    leanh::lean_dec_ref(v_toFunctor_60_);
    v___x_65_ = leanh::lean_apply_4(
        v_map_64_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_61_,
        v_x_63_,
    );
    return v___x_65_;
}
pub unsafe fn l_MonadAttach_trivial___redArg(
    mut v_inst_67_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_68_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_69_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_71_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_68_ = leanh::lean_ctor_get(v_inst_67_, 0);
    leanh::lean_inc_ref(v_toApplicative_68_);
    leanh::lean_dec_ref(v_inst_67_);
    v_toFunctor_69_ = leanh::lean_ctor_get(v_toApplicative_68_, 0);
    leanh::lean_inc_ref(v_toFunctor_69_);
    leanh::lean_dec_ref(v_toApplicative_68_);
    v___f_70_ = l_MonadAttach_trivial___redArg___closed__0;
    v___f_71_ = leanh::lean_alloc_closure(
        l_MonadAttach_trivial___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_71_, 0, v_toFunctor_69_);
    leanh::lean_closure_set(v___f_71_, 1, v___f_70_);
    return v___f_71_;
}
pub unsafe fn l_MonadAttach_trivial(
    mut v_m_72_: *mut leanh::LeanObject,
    mut v_inst_73_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_74_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_74_ = l_MonadAttach_trivial___redArg(v_inst_73_);
    return v___x_74_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_MonadAttach(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_MonadAttach(
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
pub unsafe fn initialize_Init_Control_MonadAttach(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_MonadAttach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_MonadAttach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Control_MonadAttach(builtin);
}