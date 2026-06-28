// Lean compiler output
// Module: Std.Do.SPred.Laws
// Imports: Std.Do.SPred.Notation
use crate::r#gen::Std::Do::SPred::Notation::{
    initialize_Std_Do_SPred_Notation, runtime_initialize_Std_Do_SPred_Notation,
};
use crate::r#gen::Std::Do::SPred::SPred::l_Std_Do_SPred_pure___redArg;
use crate::r#gen::Std::Do::SPred::SVal::l_Std_Do_SVal_curry___redArg;
static mut l_Std_Do_SVal_evalsTo___redArg___lam__0___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Do_SVal_evalsTo___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Do_SVal_evalsTo___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Do_SVal_evalsTo___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Do_SVal_evalsTo___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_SVal_evalsTo___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Std_Do_SPred_Laws_0__Std_Do_SPred_entails_match__1_splitter___redArg(
    mut v_00_u03c3s_46_: *mut crate::leanh::LeanObject,
    mut v_P_47_: *mut crate::leanh::LeanObject,
    mut v_Q_48_: *mut crate::leanh::LeanObject,
    mut v_h__1_49_: *mut crate::leanh::LeanObject,
    mut v_h__2_50_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_00_u03c3s_46_) == 0 {
        let mut v___x_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_50_);
        v___x_51_ = crate::leanh::lean_apply_2(v_h__1_49_, v_P_47_, v_Q_48_);
        return v___x_51_;
    } else {
        let mut v_tail_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_49_);
        v_tail_52_ = crate::leanh::lean_ctor_get(v_00_u03c3s_46_, 1);
        crate::leanh::lean_inc(v_tail_52_);
        crate::leanh::lean_dec_ref_known(v_00_u03c3s_46_, 2);
        v___x_53_ = crate::leanh::lean_apply_4(
            v_h__2_50_,
            crate::leanh::lean_box(0),
            v_tail_52_,
            v_P_47_,
            v_Q_48_,
        );
        return v___x_53_;
    }
}
pub unsafe fn l___private_Std_Do_SPred_Laws_0__Std_Do_SPred_entails_match__1_splitter(
    mut v_motive_54_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_55_: *mut crate::leanh::LeanObject,
    mut v_P_56_: *mut crate::leanh::LeanObject,
    mut v_Q_57_: *mut crate::leanh::LeanObject,
    mut v_h__1_58_: *mut crate::leanh::LeanObject,
    mut v_h__2_59_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_00_u03c3s_55_) == 0 {
        let mut v___x_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_59_);
        v___x_60_ = crate::leanh::lean_apply_2(v_h__1_58_, v_P_56_, v_Q_57_);
        return v___x_60_;
    } else {
        let mut v_tail_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_58_);
        v_tail_61_ = crate::leanh::lean_ctor_get(v_00_u03c3s_55_, 1);
        crate::leanh::lean_inc(v_tail_61_);
        crate::leanh::lean_dec_ref_known(v_00_u03c3s_55_, 2);
        v___x_62_ = crate::leanh::lean_apply_4(
            v_h__2_59_,
            crate::leanh::lean_box(0),
            v_tail_61_,
            v_P_56_,
            v_Q_57_,
        );
        return v___x_62_;
    }
}
pub unsafe fn l_Std_Do_SPred_instTransEntails(
    mut v_00_u03c3s_63_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_64_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_64_ = crate::leanh::lean_box(0);
    return v___x_64_;
}
pub unsafe fn l_Std_Do_SPred_instTransEntails___boxed(
    mut v_00_u03c3s_65_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_66_ = l_Std_Do_SPred_instTransEntails(v_00_u03c3s_65_);
    crate::leanh::lean_dec(v_00_u03c3s_65_);
    return v_res_66_;
}
pub unsafe fn l_Std_Do_SPred_instTransBientails(
    mut v_00_u03c3s_67_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_68_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_68_ = crate::leanh::lean_box(0);
    return v___x_68_;
}
pub unsafe fn l_Std_Do_SPred_instTransBientails___boxed(
    mut v_00_u03c3s_69_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_70_ = l_Std_Do_SPred_instTransBientails(v_00_u03c3s_69_);
    crate::leanh::lean_dec(v_00_u03c3s_69_);
    return v_res_70_;
}
pub unsafe fn _init_l_Std_Do_SVal_evalsTo___redArg___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_71_ = crate::leanh::lean_box(0);
    v___x_72_ = l_Std_Do_SPred_pure___redArg(v___x_71_);
    return v___x_72_;
}
pub unsafe fn l_Std_Do_SVal_evalsTo___redArg___lam__0(
    mut v_t_73_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_74_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Do_SVal_evalsTo___redArg___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Do_SVal_evalsTo___redArg___lam__0___closed__0_once),
        _init_l_Std_Do_SVal_evalsTo___redArg___lam__0___closed__0,
    );
    return v___x_74_;
}
pub unsafe fn l_Std_Do_SVal_evalsTo___redArg___lam__0___boxed(
    mut v_t_75_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_76_ = l_Std_Do_SVal_evalsTo___redArg___lam__0(v_t_75_);
    crate::leanh::lean_dec(v_t_75_);
    return v_res_76_;
}
pub unsafe fn l_Std_Do_SVal_evalsTo___redArg(
    mut v_00_u03c3s_78_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_79_ = l_Std_Do_SVal_evalsTo___redArg___closed__0;
    v___x_80_ = l_Std_Do_SVal_curry___redArg(v_00_u03c3s_78_, v___f_79_);
    return v___x_80_;
}
pub unsafe fn l_Std_Do_SVal_evalsTo(
    mut v_00_u03b1_81_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_82_: *mut crate::leanh::LeanObject,
    mut v_f_83_: *mut crate::leanh::LeanObject,
    mut v_a_84_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_85_ = l_Std_Do_SVal_evalsTo___redArg(v_00_u03c3s_82_);
    return v___x_85_;
}
pub unsafe fn l_Std_Do_SVal_evalsTo___boxed(
    mut v_00_u03b1_86_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_87_: *mut crate::leanh::LeanObject,
    mut v_f_88_: *mut crate::leanh::LeanObject,
    mut v_a_89_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_90_ = l_Std_Do_SVal_evalsTo(v_00_u03b1_86_, v_00_u03c3s_87_, v_f_88_, v_a_89_);
    crate::leanh::lean_dec(v_a_89_);
    crate::leanh::lean_dec(v_f_88_);
    return v_res_90_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_SPred_Laws(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Do_SPred_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_SPred_Laws(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_SPred_Laws(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Do_SPred_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_SPred_Laws(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Do_SPred_Laws(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Do_SPred_Laws(builtin);
}
