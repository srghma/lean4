// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Basic
// Imports: Init.Data.Iterators.Basic
use crate::r#gen::Init::Data::Iterators::Basic::{
    initialize_Init_Data_Iterators_Basic, runtime_initialize_Init_Data_Iterators_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_2, lean_apply_3, lean_box,
    lean_closure_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub unsafe fn l_Std_Iter_inductSteps___redArg___lam__0___boxed(
    mut v_step_60_: *mut LeanObject,
    mut v_it_x27_61_: *mut LeanObject,
    mut v_x_62_: *mut LeanObject,
    mut v_x_63_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_64_: *mut LeanObject = core::ptr::null_mut();
    v_res_64_ =
        l_Std_Iter_inductSteps___redArg___lam__0(v_step_60_, v_it_x27_61_, v_x_62_, v_x_63_);
    lean_dec(v_x_62_);
    return v_res_64_;
}
pub unsafe fn l_Std_Iter_inductSteps___redArg___lam__1(
    mut v_step_65_: *mut LeanObject,
    mut v_it_x27_66_: *mut LeanObject,
    mut v_x_67_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_68_: *mut LeanObject = core::ptr::null_mut();
    v___x_68_ = l_Std_Iter_inductSteps___redArg(v_step_65_, v_it_x27_66_);
    return v___x_68_;
}
pub unsafe fn l_Std_Iter_inductSteps___redArg(
    mut v_step_69_: *mut LeanObject,
    mut v_it_70_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_71_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_72_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_73_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_step_69_, 2);
    v___f_71_ = lean_alloc_closure(
        l_Std_Iter_inductSteps___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_71_, 0, v_step_69_);
    v___f_72_ = lean_alloc_closure(
        l_Std_Iter_inductSteps___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_72_, 0, v_step_69_);
    v___x_73_ = lean_apply_3(v_step_69_, v_it_70_, v___f_71_, v___f_72_);
    return v___x_73_;
}
pub unsafe fn l_Std_Iter_inductSteps___redArg___lam__0(
    mut v_step_74_: *mut LeanObject,
    mut v_it_x27_75_: *mut LeanObject,
    mut v_x_76_: *mut LeanObject,
    mut v_x_77_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_78_: *mut LeanObject = core::ptr::null_mut();
    v___x_78_ = l_Std_Iter_inductSteps___redArg(v_step_74_, v_it_x27_75_);
    return v___x_78_;
}
pub unsafe fn l_Std_Iter_inductSteps(
    mut v_00_u03b1_79_: *mut LeanObject,
    mut v_00_u03b2_80_: *mut LeanObject,
    mut v_inst_81_: *mut LeanObject,
    mut v_inst_82_: *mut LeanObject,
    mut v_motive_83_: *mut LeanObject,
    mut v_step_84_: *mut LeanObject,
    mut v_it_85_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_86_: *mut LeanObject = core::ptr::null_mut();
    v___x_86_ = l_Std_Iter_inductSteps___redArg(v_step_84_, v_it_85_);
    return v___x_86_;
}
pub unsafe fn l_Std_Iter_inductSteps___boxed(
    mut v_00_u03b1_87_: *mut LeanObject,
    mut v_00_u03b2_88_: *mut LeanObject,
    mut v_inst_89_: *mut LeanObject,
    mut v_inst_90_: *mut LeanObject,
    mut v_motive_91_: *mut LeanObject,
    mut v_step_92_: *mut LeanObject,
    mut v_it_93_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_94_: *mut LeanObject = core::ptr::null_mut();
    v_res_94_ = l_Std_Iter_inductSteps(
        v_00_u03b1_87_,
        v_00_u03b2_88_,
        v_inst_89_,
        v_inst_90_,
        v_motive_91_,
        v_step_92_,
        v_it_93_,
    );
    lean_dec(v_inst_89_);
    return v_res_94_;
}
pub unsafe fn l_Std_Iter_inductSkips___redArg(
    mut v_step_95_: *mut LeanObject,
    mut v_it_96_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_97_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_step_95_);
    v___f_97_ = lean_alloc_closure(
        l_Std_Iter_inductSkips___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_97_, 0, v_step_95_);
    v___x_98_ = lean_apply_2(v_step_95_, v_it_96_, v___f_97_);
    return v___x_98_;
}
pub unsafe fn l_Std_Iter_inductSkips___redArg___lam__0(
    mut v_step_99_: *mut LeanObject,
    mut v_it_x27_100_: *mut LeanObject,
    mut v_x_101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
    v___x_102_ = l_Std_Iter_inductSkips___redArg(v_step_99_, v_it_x27_100_);
    return v___x_102_;
}
pub unsafe fn l_Std_Iter_inductSkips(
    mut v_00_u03b1_103_: *mut LeanObject,
    mut v_00_u03b2_104_: *mut LeanObject,
    mut v_inst_105_: *mut LeanObject,
    mut v_inst_106_: *mut LeanObject,
    mut v_motive_107_: *mut LeanObject,
    mut v_step_108_: *mut LeanObject,
    mut v_it_109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
    v___x_110_ = l_Std_Iter_inductSkips___redArg(v_step_108_, v_it_109_);
    return v___x_110_;
}
pub unsafe fn l_Std_Iter_inductSkips___boxed(
    mut v_00_u03b1_111_: *mut LeanObject,
    mut v_00_u03b2_112_: *mut LeanObject,
    mut v_inst_113_: *mut LeanObject,
    mut v_inst_114_: *mut LeanObject,
    mut v_motive_115_: *mut LeanObject,
    mut v_step_116_: *mut LeanObject,
    mut v_it_117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_118_: *mut LeanObject = core::ptr::null_mut();
    v_res_118_ = l_Std_Iter_inductSkips(
        v_00_u03b1_111_,
        v_00_u03b2_112_,
        v_inst_113_,
        v_inst_114_,
        v_motive_115_,
        v_step_116_,
        v_it_117_,
    );
    lean_dec(v_inst_113_);
    return v_res_118_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin: u8) -> *mut LeanObject {
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
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Basic(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
}
