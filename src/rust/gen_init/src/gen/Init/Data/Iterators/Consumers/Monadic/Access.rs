// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Monadic.Access
// Imports: Init.Data.Iterators.Basic
use crate::r#gen::Init::Data::Iterators::Basic::{
    initialize_Init_Data_Iterators_Basic, runtime_initialize_Init_Data_Iterators_Basic,
};
pub unsafe fn l_Std_IterM_nextAtIdx_x3f___redArg(
    mut v_inst_64_: *mut leanh::LeanObject,
    mut v_it_65_: *mut leanh::LeanObject,
    mut v_n_66_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_67_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_67_ = leanh::lean_apply_2(v_inst_64_, v_it_65_, v_n_66_);
    return v___x_67_;
}
pub unsafe fn l_Std_IterM_nextAtIdx_x3f(
    mut v_00_u03b1_68_: *mut leanh::LeanObject,
    mut v_m_69_: *mut leanh::LeanObject,
    mut v_00_u03b2_70_: *mut leanh::LeanObject,
    mut v_inst_71_: *mut leanh::LeanObject,
    mut v_inst_72_: *mut leanh::LeanObject,
    mut v_it_73_: *mut leanh::LeanObject,
    mut v_n_74_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_75_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_75_ = leanh::lean_apply_2(v_inst_72_, v_it_73_, v_n_74_);
    return v___x_75_;
}
pub unsafe fn l_Std_IterM_nextAtIdx_x3f___boxed(
    mut v_00_u03b1_76_: *mut leanh::LeanObject,
    mut v_m_77_: *mut leanh::LeanObject,
    mut v_00_u03b2_78_: *mut leanh::LeanObject,
    mut v_inst_79_: *mut leanh::LeanObject,
    mut v_inst_80_: *mut leanh::LeanObject,
    mut v_it_81_: *mut leanh::LeanObject,
    mut v_n_82_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_83_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_83_ = l_Std_IterM_nextAtIdx_x3f(
        v_00_u03b1_76_,
        v_m_77_,
        v_00_u03b2_78_,
        v_inst_79_,
        v_inst_80_,
        v_it_81_,
        v_n_82_,
    );
    leanh::lean_dec(v_inst_79_);
    return v_res_83_;
}
pub unsafe fn l_Std_IterM_atIdx_x3f___redArg___lam__0(
    mut v_toPure_84_: *mut leanh::LeanObject,
    mut v_____do__lift_85_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_85_) == 0 {
        let mut v_out_86_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_87_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_88_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_out_86_ = leanh::lean_ctor_get(v_____do__lift_85_, 1);
        leanh::lean_inc(v_out_86_);
        v___x_87_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_87_, 0, v_out_86_);
        v___x_88_ = leanh::lean_apply_2(v_toPure_84_, leanh::lean_box(0), v___x_87_);
        return v___x_88_;
    } else {
        let mut v___x_89_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_90_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_89_ = leanh::lean_box(0);
        v___x_90_ = leanh::lean_apply_2(v_toPure_84_, leanh::lean_box(0), v___x_89_);
        return v___x_90_;
    }
}
pub unsafe fn l_Std_IterM_atIdx_x3f___redArg___lam__0___boxed(
    mut v_toPure_91_: *mut leanh::LeanObject,
    mut v_____do__lift_92_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_93_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_93_ = l_Std_IterM_atIdx_x3f___redArg___lam__0(v_toPure_91_, v_____do__lift_92_);
    leanh::lean_dec(v_____do__lift_92_);
    return v_res_93_;
}
pub unsafe fn l_Std_IterM_atIdx_x3f___redArg(
    mut v_inst_94_: *mut leanh::LeanObject,
    mut v_inst_95_: *mut leanh::LeanObject,
    mut v_it_96_: *mut leanh::LeanObject,
    mut v_n_97_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_98_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_99_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_98_ = leanh::lean_ctor_get(v_inst_95_, 0);
    leanh::lean_inc_ref(v_toApplicative_98_);
    v_toBind_99_ = leanh::lean_ctor_get(v_inst_95_, 1);
    leanh::lean_inc(v_toBind_99_);
    leanh::lean_dec_ref(v_inst_95_);
    v_toPure_100_ = leanh::lean_ctor_get(v_toApplicative_98_, 1);
    leanh::lean_inc(v_toPure_100_);
    leanh::lean_dec_ref(v_toApplicative_98_);
    v___x_101_ = leanh::lean_apply_2(v_inst_94_, v_it_96_, v_n_97_);
    v___f_102_ = leanh::lean_alloc_closure(
        l_Std_IterM_atIdx_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_102_, 0, v_toPure_100_);
    v___x_103_ = leanh::lean_apply_4(
        v_toBind_99_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_101_,
        v___f_102_,
    );
    return v___x_103_;
}
pub unsafe fn l_Std_IterM_atIdx_x3f(
    mut v_00_u03b1_104_: *mut leanh::LeanObject,
    mut v_m_105_: *mut leanh::LeanObject,
    mut v_00_u03b2_106_: *mut leanh::LeanObject,
    mut v_inst_107_: *mut leanh::LeanObject,
    mut v_inst_108_: *mut leanh::LeanObject,
    mut v_inst_109_: *mut leanh::LeanObject,
    mut v_it_110_: *mut leanh::LeanObject,
    mut v_n_111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_112_ = leanh::lean_ctor_get(v_inst_109_, 0);
    leanh::lean_inc_ref(v_toApplicative_112_);
    v_toBind_113_ = leanh::lean_ctor_get(v_inst_109_, 1);
    leanh::lean_inc(v_toBind_113_);
    leanh::lean_dec_ref(v_inst_109_);
    v_toPure_114_ = leanh::lean_ctor_get(v_toApplicative_112_, 1);
    leanh::lean_inc(v_toPure_114_);
    leanh::lean_dec_ref(v_toApplicative_112_);
    v___x_115_ = leanh::lean_apply_2(v_inst_108_, v_it_110_, v_n_111_);
    v___f_116_ = leanh::lean_alloc_closure(
        l_Std_IterM_atIdx_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_116_, 0, v_toPure_114_);
    v___x_117_ = leanh::lean_apply_4(
        v_toBind_113_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_115_,
        v___f_116_,
    );
    return v___x_117_;
}
pub unsafe fn l_Std_IterM_atIdx_x3f___boxed(
    mut v_00_u03b1_118_: *mut leanh::LeanObject,
    mut v_m_119_: *mut leanh::LeanObject,
    mut v_00_u03b2_120_: *mut leanh::LeanObject,
    mut v_inst_121_: *mut leanh::LeanObject,
    mut v_inst_122_: *mut leanh::LeanObject,
    mut v_inst_123_: *mut leanh::LeanObject,
    mut v_it_124_: *mut leanh::LeanObject,
    mut v_n_125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_126_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_inst_121_);
    return v_res_126_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Consumers_Monadic_Access(
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
pub unsafe fn initialize_Init_Data_Iterators_Consumers_Monadic_Access(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
}