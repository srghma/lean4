// Lean compiler output
// Module: Lean.Util.FVarSubset
// Imports: Lean.Util.CollectFVars Lean.Util.FindExpr
use crate::ffi::{lean_find_ext_expr, lean_mk_array};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_fvarId_x21, l_Lean_Expr_hasFVar, l_Lean_Expr_isFVar};
use crate::r#gen::Lean::Util::CollectFVars::{
    initialize_Lean_Util_CollectFVars, l_Lean_collectFVars,
    runtime_initialize_Lean_Util_CollectFVars,
};
use crate::r#gen::Lean::Util::FindExpr::{
    initialize_Lean_Util_FindExpr, runtime_initialize_Lean_Util_FindExpr,
};
static mut l_Lean_Expr_fvarsSubset___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_fvarsSubset___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Expr_fvarsSubset___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_fvarsSubset___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Expr_fvarsSubset___closed__2_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Expr_fvarsSubset___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_fvarsSubset___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_Expr_fvarsSubset___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_fvarsSubset___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0___redArg(
    mut v_k_67_: *mut leanh::LeanObject,
    mut v_t_68_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_69_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_71_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_72_: u8 = 0;
    let mut v___x_74_: u8 = 0;
    let mut v___x_76_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_68_) == 0 {
                    v_k_69_ = leanh::lean_ctor_get(v_t_68_, 1);
                    v_l_70_ = leanh::lean_ctor_get(v_t_68_, 3);
                    v_r_71_ = leanh::lean_ctor_get(v_t_68_, 4);
                    v___x_72_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_67_, v_k_69_);
                    match v___x_72_ {
                        0 => {
                            v_t_68_ = v_l_70_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_74_ = 1;
                            return v___x_74_;
                        }
                        _ => {
                            v_t_68_ = v_r_71_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_76_ = 0;
                    return v___x_76_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0___redArg___boxed(
    mut v_k_77_: *mut leanh::LeanObject,
    mut v_t_78_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_79_: u8 = 0;
    let mut v_r_80_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_79_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0___redArg(
            v_k_77_, v_t_78_,
        );
    leanh::lean_dec(v_t_78_);
    leanh::lean_dec(v_k_77_);
    v_r_80_ = leanh::lean_box((v_res_79_) as usize);
    return v_r_80_;
}
pub unsafe fn l_Lean_Expr_fvarsSubset___lam__0(
    mut v_s_81_: *mut leanh::LeanObject,
    mut v_e_82_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_84_: u8 = 0;
    let mut v___x_85_: u8 = 0;
    let mut v___x_86_: u8 = 0;
    let mut v___x_87_: u8 = 0;
    let mut v___x_88_: u8 = 0;
    let mut v___x_89_: u8 = 0;
    let mut v_fvarSet_90_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_91_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_92_: u8 = 0;
    let mut v___x_93_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_87_ = l_Lean_Expr_hasFVar(v_e_82_);
                if v___x_87_ == 0 {
                    v___x_88_ = 2;
                    return v___x_88_;
                } else {
                    v___x_89_ = l_Lean_Expr_isFVar(v_e_82_);
                    if v___x_89_ == 0 {
                        v___y_84_ = v___x_89_;
                        state = 1;
                        continue;
                    } else {
                        v_fvarSet_90_ = leanh::lean_ctor_get(v_s_81_, 1);
                        v___x_91_ = l_Lean_Expr_fvarId_x21(v_e_82_);
                        v___x_92_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0___redArg(v___x_91_, v_fvarSet_90_);
                        leanh::lean_dec(v___x_91_);
                        if v___x_92_ == 0 {
                            v___y_84_ = v___x_89_;
                            state = 1;
                            continue;
                        } else {
                            v___x_93_ = 1;
                            return v___x_93_;
                        }
                    }
                }
            }
            1 => {
                if v___y_84_ == 0 {
                    v___x_85_ = 1;
                    return v___x_85_;
                } else {
                    v___x_86_ = 0;
                    return v___x_86_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_fvarsSubset___lam__0___boxed(
    mut v_s_94_: *mut leanh::LeanObject,
    mut v_e_95_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_96_: u8 = 0;
    let mut v_r_97_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_96_ = l_Lean_Expr_fvarsSubset___lam__0(v_s_94_, v_e_95_);
    leanh::lean_dec_ref(v_e_95_);
    leanh::lean_dec_ref(v_s_94_);
    v_r_97_ = leanh::lean_box((v_res_96_) as usize);
    return v_r_97_;
}
pub unsafe fn _init_l_Lean_Expr_fvarsSubset___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_98_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_99_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_98_ = leanh::lean_box(0);
    v___x_99_ = leanh::lean_unsigned_to_nat(16);
    v___x_100_ = lean_mk_array(v___x_99_, v___x_98_);
    return v___x_100_;
}
pub unsafe fn _init_l_Lean_Expr_fvarsSubset___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_101_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_fvarsSubset___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Expr_fvarsSubset___closed__0_once),
        _init_l_Lean_Expr_fvarsSubset___closed__0,
    );
    v___x_102_ = leanh::lean_unsigned_to_nat(0);
    v___x_103_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_103_, 0, v___x_102_);
    leanh::lean_ctor_set(v___x_103_, 1, v___x_101_);
    return v___x_103_;
}
pub unsafe fn _init_l_Lean_Expr_fvarsSubset___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_106_ = l_Lean_Expr_fvarsSubset___closed__2;
    v___x_107_ = leanh::lean_box(1);
    v___x_108_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_fvarsSubset___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Expr_fvarsSubset___closed__1_once),
        _init_l_Lean_Expr_fvarsSubset___closed__1,
    );
    v___x_109_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_109_, 0, v___x_108_);
    leanh::lean_ctor_set(v___x_109_, 1, v___x_107_);
    leanh::lean_ctor_set(v___x_109_, 2, v___x_106_);
    return v___x_109_;
}
pub unsafe fn l_Lean_Expr_fvarsSubset(
    mut v_a_110_: *mut leanh::LeanObject,
    mut v_b_111_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_112_: u8 = 0;
    v___x_112_ = l_Lean_Expr_hasFVar(v_a_110_);
    if v___x_112_ == 0 {
        let mut v___x_113_: u8 = 0;
        leanh::lean_dec_ref(v_b_111_);
        v___x_113_ = 1;
        return v___x_113_;
    } else {
        let mut v___x_114_: u8 = 0;
        let mut v___x_115_: u8 = 0;
        v___x_114_ = 0;
        v___x_115_ = l_Lean_Expr_hasFVar(v_b_111_);
        if v___x_115_ == 0 {
            leanh::lean_dec_ref(v_b_111_);
            return v___x_114_;
        } else {
            let mut v___x_116_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_117_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_118_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_119_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_116_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Expr_fvarsSubset___closed__3),
                core::ptr::addr_of_mut!(l_Lean_Expr_fvarsSubset___closed__3_once),
                _init_l_Lean_Expr_fvarsSubset___closed__3,
            );
            v_s_117_ = l_Lean_collectFVars(v___x_116_, v_b_111_);
            v___f_118_ = leanh::lean_alloc_closure(
                l_Lean_Expr_fvarsSubset___lam__0___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            leanh::lean_closure_set(v___f_118_, 0, v_s_117_);
            v___x_119_ = lean_find_ext_expr(v___f_118_, v_a_110_);
            leanh::lean_dec_ref(v___f_118_);
            if leanh::lean_obj_tag(v___x_119_) == 0 {
                return v___x_115_;
            } else {
                leanh::lean_dec_ref_known(v___x_119_, 1);
                return v___x_114_;
            }
        }
    }
}
pub unsafe fn l_Lean_Expr_fvarsSubset___boxed(
    mut v_a_120_: *mut leanh::LeanObject,
    mut v_b_121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_122_: u8 = 0;
    let mut v_r_123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_122_ = l_Lean_Expr_fvarsSubset(v_a_120_, v_b_121_);
    leanh::lean_dec_ref(v_a_120_);
    v_r_123_ = leanh::lean_box((v_res_122_) as usize);
    return v_r_123_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0(
    mut v_00_u03b2_124_: *mut leanh::LeanObject,
    mut v_k_125_: *mut leanh::LeanObject,
    mut v_t_126_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_127_: u8 = 0;
    v___x_127_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0___redArg(
            v_k_125_, v_t_126_,
        );
    return v___x_127_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0___boxed(
    mut v_00_u03b2_128_: *mut leanh::LeanObject,
    mut v_k_129_: *mut leanh::LeanObject,
    mut v_t_130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_131_: u8 = 0;
    let mut v_r_132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_131_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Expr_fvarsSubset_spec__0(
        v_00_u03b2_128_,
        v_k_129_,
        v_t_130_,
    );
    leanh::lean_dec(v_t_130_);
    leanh::lean_dec(v_k_129_);
    v_r_132_ = leanh::lean_box((v_res_131_) as usize);
    return v_r_132_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_FVarSubset(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_CollectFVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_FindExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_FVarSubset(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_FVarSubset(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_CollectFVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_FindExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_FVarSubset(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_FVarSubset(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Util_FVarSubset(builtin);
}