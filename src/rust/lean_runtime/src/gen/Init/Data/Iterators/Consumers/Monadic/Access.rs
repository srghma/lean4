// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Monadic.Access
// Imports: Init.Data.Iterators.Basic
use crate::r#gen::Init::Data::Iterators::Basic::{
    initialize_Init_Data_Iterators_Basic, runtime_initialize_Init_Data_Iterators_Basic,
};
pub unsafe fn l_Std_IterM_nextAtIdx_x3f___redArg(
    mut v_inst_64_: *mut crate::leanh::LeanObject,
    mut v_it_65_: *mut crate::leanh::LeanObject,
    mut v_n_66_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_67_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_67_ = crate::leanh::lean_apply_2(v_inst_64_, v_it_65_, v_n_66_);
    return v___x_67_;
}
pub unsafe fn l_Std_IterM_nextAtIdx_x3f(
    mut v_00_u03b1_68_: *mut crate::leanh::LeanObject,
    mut v_m_69_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_70_: *mut crate::leanh::LeanObject,
    mut v_inst_71_: *mut crate::leanh::LeanObject,
    mut v_inst_72_: *mut crate::leanh::LeanObject,
    mut v_it_73_: *mut crate::leanh::LeanObject,
    mut v_n_74_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_75_ = crate::leanh::lean_apply_2(v_inst_72_, v_it_73_, v_n_74_);
    return v___x_75_;
}
pub unsafe fn l_Std_IterM_nextAtIdx_x3f___boxed(
    mut v_00_u03b1_76_: *mut crate::leanh::LeanObject,
    mut v_m_77_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_78_: *mut crate::leanh::LeanObject,
    mut v_inst_79_: *mut crate::leanh::LeanObject,
    mut v_inst_80_: *mut crate::leanh::LeanObject,
    mut v_it_81_: *mut crate::leanh::LeanObject,
    mut v_n_82_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_83_ = l_Std_IterM_nextAtIdx_x3f(
        v_00_u03b1_76_,
        v_m_77_,
        v_00_u03b2_78_,
        v_inst_79_,
        v_inst_80_,
        v_it_81_,
        v_n_82_,
    );
    crate::leanh::lean_dec(v_inst_79_);
    return v_res_83_;
}
pub unsafe fn l_Std_IterM_atIdx_x3f___redArg___lam__0(
    mut v_toPure_84_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_85_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_85_) == 0 {
        let mut v_out_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_out_86_ = crate::leanh::lean_ctor_get(v_____do__lift_85_, 1);
        crate::leanh::lean_inc(v_out_86_);
        v___x_87_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_87_, 0, v_out_86_);
        v___x_88_ = crate::leanh::lean_apply_2(v_toPure_84_, crate::leanh::lean_box(0), v___x_87_);
        return v___x_88_;
    } else {
        let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_89_ = crate::leanh::lean_box(0);
        v___x_90_ = crate::leanh::lean_apply_2(v_toPure_84_, crate::leanh::lean_box(0), v___x_89_);
        return v___x_90_;
    }
}
pub unsafe fn l_Std_IterM_atIdx_x3f___redArg___lam__0___boxed(
    mut v_toPure_91_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_92_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_93_ = l_Std_IterM_atIdx_x3f___redArg___lam__0(v_toPure_91_, v_____do__lift_92_);
    crate::leanh::lean_dec(v_____do__lift_92_);
    return v_res_93_;
}
pub unsafe fn l_Std_IterM_atIdx_x3f___redArg(
    mut v_inst_94_: *mut crate::leanh::LeanObject,
    mut v_inst_95_: *mut crate::leanh::LeanObject,
    mut v_it_96_: *mut crate::leanh::LeanObject,
    mut v_n_97_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_98_ = crate::leanh::lean_ctor_get(v_inst_95_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_98_);
    v_toBind_99_ = crate::leanh::lean_ctor_get(v_inst_95_, 1);
    crate::leanh::lean_inc(v_toBind_99_);
    crate::leanh::lean_dec_ref(v_inst_95_);
    v_toPure_100_ = crate::leanh::lean_ctor_get(v_toApplicative_98_, 1);
    crate::leanh::lean_inc(v_toPure_100_);
    crate::leanh::lean_dec_ref(v_toApplicative_98_);
    v___x_101_ = crate::leanh::lean_apply_2(v_inst_94_, v_it_96_, v_n_97_);
    v___f_102_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_atIdx_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_102_, 0, v_toPure_100_);
    v___x_103_ = crate::leanh::lean_apply_4(
        v_toBind_99_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_101_,
        v___f_102_,
    );
    return v___x_103_;
}
pub unsafe fn l_Std_IterM_atIdx_x3f(
    mut v_00_u03b1_104_: *mut crate::leanh::LeanObject,
    mut v_m_105_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_106_: *mut crate::leanh::LeanObject,
    mut v_inst_107_: *mut crate::leanh::LeanObject,
    mut v_inst_108_: *mut crate::leanh::LeanObject,
    mut v_inst_109_: *mut crate::leanh::LeanObject,
    mut v_it_110_: *mut crate::leanh::LeanObject,
    mut v_n_111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_112_ = crate::leanh::lean_ctor_get(v_inst_109_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_112_);
    v_toBind_113_ = crate::leanh::lean_ctor_get(v_inst_109_, 1);
    crate::leanh::lean_inc(v_toBind_113_);
    crate::leanh::lean_dec_ref(v_inst_109_);
    v_toPure_114_ = crate::leanh::lean_ctor_get(v_toApplicative_112_, 1);
    crate::leanh::lean_inc(v_toPure_114_);
    crate::leanh::lean_dec_ref(v_toApplicative_112_);
    v___x_115_ = crate::leanh::lean_apply_2(v_inst_108_, v_it_110_, v_n_111_);
    v___f_116_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_atIdx_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_116_, 0, v_toPure_114_);
    v___x_117_ = crate::leanh::lean_apply_4(
        v_toBind_113_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_115_,
        v___f_116_,
    );
    return v___x_117_;
}
pub unsafe fn l_Std_IterM_atIdx_x3f___boxed(
    mut v_00_u03b1_118_: *mut crate::leanh::LeanObject,
    mut v_m_119_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_120_: *mut crate::leanh::LeanObject,
    mut v_inst_121_: *mut crate::leanh::LeanObject,
    mut v_inst_122_: *mut crate::leanh::LeanObject,
    mut v_inst_123_: *mut crate::leanh::LeanObject,
    mut v_it_124_: *mut crate::leanh::LeanObject,
    mut v_n_125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_126_ = l_Std_IterM_atIdx_x3f(
        v_00_u03b1_118_,
        v_m_119_,
        v_00_u03b2_120_,
        v_inst_121_,
        v_inst_122_,
        v_inst_123_,
        v_it_124_,
        v_n_125_,
    );
    crate::leanh::lean_dec(v_inst_121_);
    return v_res_126_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Consumers_Monadic_Access(
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
pub unsafe fn initialize_Init_Data_Iterators_Consumers_Monadic_Access(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
}
