// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Monadic.Access
// Imports: Init.Data.Iterators.Basic
use crate::r#gen::Init::Data::Iterators::Basic::{
    initialize_Init_Data_Iterators_Basic, runtime_initialize_Init_Data_Iterators_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l_Std_IterM_nextAtIdx_x3f___redArg(
    mut v_inst_64_: *mut LeanObject,
    mut v_it_65_: *mut LeanObject,
    mut v_n_66_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_67_: *mut LeanObject = core::ptr::null_mut();
    v___x_67_ = lean_apply_2(v_inst_64_, v_it_65_, v_n_66_);
    return v___x_67_;
}
pub unsafe fn l_Std_IterM_nextAtIdx_x3f(
    mut v_00_u03b1_68_: *mut LeanObject,
    mut v_m_69_: *mut LeanObject,
    mut v_00_u03b2_70_: *mut LeanObject,
    mut v_inst_71_: *mut LeanObject,
    mut v_inst_72_: *mut LeanObject,
    mut v_it_73_: *mut LeanObject,
    mut v_n_74_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_75_: *mut LeanObject = core::ptr::null_mut();
    v___x_75_ = lean_apply_2(v_inst_72_, v_it_73_, v_n_74_);
    return v___x_75_;
}
pub unsafe fn l_Std_IterM_nextAtIdx_x3f___boxed(
    mut v_00_u03b1_76_: *mut LeanObject,
    mut v_m_77_: *mut LeanObject,
    mut v_00_u03b2_78_: *mut LeanObject,
    mut v_inst_79_: *mut LeanObject,
    mut v_inst_80_: *mut LeanObject,
    mut v_it_81_: *mut LeanObject,
    mut v_n_82_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_83_: *mut LeanObject = core::ptr::null_mut();
    v_res_83_ = l_Std_IterM_nextAtIdx_x3f(
        v_00_u03b1_76_,
        v_m_77_,
        v_00_u03b2_78_,
        v_inst_79_,
        v_inst_80_,
        v_it_81_,
        v_n_82_,
    );
    lean_dec(v_inst_79_);
    return v_res_83_;
}
pub unsafe fn l_Std_IterM_atIdx_x3f___redArg___lam__0(
    mut v_toPure_84_: *mut LeanObject,
    mut v_____do__lift_85_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_85_) == 0 {
        let mut v_out_86_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_87_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_88_: *mut LeanObject = core::ptr::null_mut();
        v_out_86_ = lean_ctor_get(v_____do__lift_85_, 1);
        lean_inc(v_out_86_);
        v___x_87_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_87_, 0, v_out_86_);
        v___x_88_ = lean_apply_2(v_toPure_84_, lean_box(0), v___x_87_);
        return v___x_88_;
    } else {
        let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_90_: *mut LeanObject = core::ptr::null_mut();
        v___x_89_ = lean_box(0);
        v___x_90_ = lean_apply_2(v_toPure_84_, lean_box(0), v___x_89_);
        return v___x_90_;
    }
}
pub unsafe fn l_Std_IterM_atIdx_x3f___redArg___lam__0___boxed(
    mut v_toPure_91_: *mut LeanObject,
    mut v_____do__lift_92_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_93_: *mut LeanObject = core::ptr::null_mut();
    v_res_93_ = l_Std_IterM_atIdx_x3f___redArg___lam__0(v_toPure_91_, v_____do__lift_92_);
    lean_dec(v_____do__lift_92_);
    return v_res_93_;
}
pub unsafe fn l_Std_IterM_atIdx_x3f___redArg(
    mut v_inst_94_: *mut LeanObject,
    mut v_inst_95_: *mut LeanObject,
    mut v_it_96_: *mut LeanObject,
    mut v_n_97_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_98_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_98_ = lean_ctor_get(v_inst_95_, 0);
    lean_inc_ref(v_toApplicative_98_);
    v_toBind_99_ = lean_ctor_get(v_inst_95_, 1);
    lean_inc(v_toBind_99_);
    lean_dec_ref(v_inst_95_);
    v_toPure_100_ = lean_ctor_get(v_toApplicative_98_, 1);
    lean_inc(v_toPure_100_);
    lean_dec_ref(v_toApplicative_98_);
    v___x_101_ = lean_apply_2(v_inst_94_, v_it_96_, v_n_97_);
    v___f_102_ = lean_alloc_closure(
        l_Std_IterM_atIdx_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_102_, 0, v_toPure_100_);
    v___x_103_ = lean_apply_4(
        v_toBind_99_,
        lean_box(0),
        lean_box(0),
        v___x_101_,
        v___f_102_,
    );
    return v___x_103_;
}
pub unsafe fn l_Std_IterM_atIdx_x3f(
    mut v_00_u03b1_104_: *mut LeanObject,
    mut v_m_105_: *mut LeanObject,
    mut v_00_u03b2_106_: *mut LeanObject,
    mut v_inst_107_: *mut LeanObject,
    mut v_inst_108_: *mut LeanObject,
    mut v_inst_109_: *mut LeanObject,
    mut v_it_110_: *mut LeanObject,
    mut v_n_111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_117_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_112_ = lean_ctor_get(v_inst_109_, 0);
    lean_inc_ref(v_toApplicative_112_);
    v_toBind_113_ = lean_ctor_get(v_inst_109_, 1);
    lean_inc(v_toBind_113_);
    lean_dec_ref(v_inst_109_);
    v_toPure_114_ = lean_ctor_get(v_toApplicative_112_, 1);
    lean_inc(v_toPure_114_);
    lean_dec_ref(v_toApplicative_112_);
    v___x_115_ = lean_apply_2(v_inst_108_, v_it_110_, v_n_111_);
    v___f_116_ = lean_alloc_closure(
        l_Std_IterM_atIdx_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_116_, 0, v_toPure_114_);
    v___x_117_ = lean_apply_4(
        v_toBind_113_,
        lean_box(0),
        lean_box(0),
        v___x_115_,
        v___f_116_,
    );
    return v___x_117_;
}
pub unsafe fn l_Std_IterM_atIdx_x3f___boxed(
    mut v_00_u03b1_118_: *mut LeanObject,
    mut v_m_119_: *mut LeanObject,
    mut v_00_u03b2_120_: *mut LeanObject,
    mut v_inst_121_: *mut LeanObject,
    mut v_inst_122_: *mut LeanObject,
    mut v_inst_123_: *mut LeanObject,
    mut v_it_124_: *mut LeanObject,
    mut v_n_125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_126_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_121_);
    return v_res_126_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Consumers_Monadic_Access(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Iterators_Consumers_Monadic_Access(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
}
