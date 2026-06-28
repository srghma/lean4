// Lean compiler output
// Module: Init.GrindInstances.Ring.Fin
// Imports: Init.Data.Zero Init.GrindInstances.ToInt Init.GrindInstances.ToInt Init.Data.Fin.Lemmas Init.Grind.Ring.Basic Init.Data.Nat.Lemmas Init.Data.Nat.MinMax
use crate::r#gen::Init::Data::Fin::Basic::{
    l_Fin_add___boxed, l_Fin_mul, l_Fin_mul___boxed, l_Fin_neg___lam__0___boxed, l_Fin_sub___boxed,
};
use crate::r#gen::Init::Data::Fin::Lemmas::{
    initialize_Init_Data_Fin_Lemmas, l_Fin_NatCast_instNatCast___redArg___lam__0,
    l_Fin_NatCast_instNatCast___redArg___lam__0___boxed, l_Fin_intCast___boxed,
    l_Fin_intCast___redArg, runtime_initialize_Init_Data_Fin_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Nat::MinMax::{
    initialize_Init_Data_Nat_MinMax, runtime_initialize_Init_Data_Nat_MinMax,
};
use crate::r#gen::Init::Data::Zero::{
    initialize_Init_Data_Zero, l_npowRec___redArg, runtime_initialize_Init_Data_Zero,
};
use crate::r#gen::Init::Grind::Ring::Basic::{
    initialize_Init_Grind_Ring_Basic, runtime_initialize_Init_Grind_Ring_Basic,
};
use crate::r#gen::Init::GrindInstances::ToInt::{
    initialize_Init_GrindInstances_ToInt, runtime_initialize_Init_GrindInstances_ToInt,
};
use crate::lean_imports_rs::Init::Prelude::lean_nat_mod;
pub unsafe fn l_Lean_Grind_Fin_npow___redArg(
    mut v_n_72_: *mut crate::leanh::LeanObject,
    mut v_x_73_: *mut crate::leanh::LeanObject,
    mut v_y_74_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_75_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_76_ = lean_nat_mod(v___x_75_, v_n_72_);
    v___x_77_ = crate::leanh::lean_alloc_closure(l_Fin_mul___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_77_, 0, v_n_72_);
    v___x_78_ = l_npowRec___redArg(v___x_76_, v___x_77_, v_y_74_, v_x_73_);
    crate::leanh::lean_dec(v___x_76_);
    return v___x_78_;
}
pub unsafe fn l_Lean_Grind_Fin_npow___redArg___boxed(
    mut v_n_79_: *mut crate::leanh::LeanObject,
    mut v_x_80_: *mut crate::leanh::LeanObject,
    mut v_y_81_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_82_ = l_Lean_Grind_Fin_npow___redArg(v_n_79_, v_x_80_, v_y_81_);
    crate::leanh::lean_dec(v_y_81_);
    return v_res_82_;
}
pub unsafe fn l_Lean_Grind_Fin_npow(
    mut v_n_83_: *mut crate::leanh::LeanObject,
    mut v_inst_84_: *mut crate::leanh::LeanObject,
    mut v_x_85_: *mut crate::leanh::LeanObject,
    mut v_y_86_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_87_ = l_Lean_Grind_Fin_npow___redArg(v_n_83_, v_x_85_, v_y_86_);
    return v___x_87_;
}
pub unsafe fn l_Lean_Grind_Fin_npow___boxed(
    mut v_n_88_: *mut crate::leanh::LeanObject,
    mut v_inst_89_: *mut crate::leanh::LeanObject,
    mut v_x_90_: *mut crate::leanh::LeanObject,
    mut v_y_91_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_92_ = l_Lean_Grind_Fin_npow(v_n_88_, v_inst_89_, v_x_90_, v_y_91_);
    crate::leanh::lean_dec(v_y_91_);
    return v_res_92_;
}
pub unsafe fn l_Lean_Grind_Fin_instHPowFinNatOfNeZero___redArg(
    mut v_n_93_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_94_ = crate::leanh::lean_alloc_closure(
        l_Lean_Grind_Fin_npow___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_94_, 0, v_n_93_);
    crate::leanh::lean_closure_set(v___x_94_, 1, crate::leanh::lean_box(0));
    return v___x_94_;
}
pub unsafe fn l_Lean_Grind_Fin_instHPowFinNatOfNeZero(
    mut v_n_95_: *mut crate::leanh::LeanObject,
    mut v_inst_96_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_97_ = crate::leanh::lean_alloc_closure(
        l_Lean_Grind_Fin_npow___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_97_, 0, v_n_95_);
    crate::leanh::lean_closure_set(v___x_97_, 1, crate::leanh::lean_box(0));
    return v___x_97_;
}
pub unsafe fn l_Lean_Grind_Fin_instPowFinNatOfNeZero___redArg(
    mut v_n_98_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_99_ = crate::leanh::lean_alloc_closure(
        l_Lean_Grind_Fin_npow___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_99_, 0, v_n_98_);
    crate::leanh::lean_closure_set(v___x_99_, 1, crate::leanh::lean_box(0));
    return v___x_99_;
}
pub unsafe fn l_Lean_Grind_Fin_instPowFinNatOfNeZero(
    mut v_n_100_: *mut crate::leanh::LeanObject,
    mut v_inst_101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_102_ = crate::leanh::lean_alloc_closure(
        l_Lean_Grind_Fin_npow___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_102_, 0, v_n_100_);
    crate::leanh::lean_closure_set(v___x_102_, 1, crate::leanh::lean_box(0));
    return v___x_102_;
}
pub unsafe fn l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0(
    mut v_n_103_: *mut crate::leanh::LeanObject,
    mut v_n_104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_105_ = lean_nat_mod(v_n_104_, v_n_103_);
    return v___x_105_;
}
pub unsafe fn l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0___boxed(
    mut v_n_106_: *mut crate::leanh::LeanObject,
    mut v_n_107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_108_ = l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0(v_n_106_, v_n_107_);
    crate::leanh::lean_dec(v_n_107_);
    crate::leanh::lean_dec(v_n_106_);
    return v_res_108_;
}
pub unsafe fn l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__1(
    mut v_n_109_: *mut crate::leanh::LeanObject,
    mut v_k_110_: *mut crate::leanh::LeanObject,
    mut v_i_111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_112_ = l_Fin_NatCast_instNatCast___redArg___lam__0(v_n_109_, v_k_110_);
    v___x_113_ = l_Fin_mul(v_n_109_, v___x_112_, v_i_111_);
    crate::leanh::lean_dec(v___x_112_);
    return v___x_113_;
}
pub unsafe fn l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__1___boxed(
    mut v_n_114_: *mut crate::leanh::LeanObject,
    mut v_k_115_: *mut crate::leanh::LeanObject,
    mut v_i_116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_117_ =
        l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__1(v_n_114_, v_k_115_, v_i_116_);
    crate::leanh::lean_dec(v_i_116_);
    crate::leanh::lean_dec(v_k_115_);
    crate::leanh::lean_dec(v_n_114_);
    return v_res_117_;
}
pub unsafe fn l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__2(
    mut v_n_118_: *mut crate::leanh::LeanObject,
    mut v_k_119_: *mut crate::leanh::LeanObject,
    mut v_i_120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_121_ = l_Fin_intCast___redArg(v_n_118_, v_k_119_);
    v___x_122_ = l_Fin_mul(v_n_118_, v___x_121_, v_i_120_);
    crate::leanh::lean_dec(v___x_121_);
    return v___x_122_;
}
pub unsafe fn l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__2___boxed(
    mut v_n_123_: *mut crate::leanh::LeanObject,
    mut v_k_124_: *mut crate::leanh::LeanObject,
    mut v_i_125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_126_ =
        l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__2(v_n_123_, v_k_124_, v_i_125_);
    crate::leanh::lean_dec(v_i_125_);
    crate::leanh::lean_dec(v_k_124_);
    crate::leanh::lean_dec(v_n_123_);
    return v_res_126_;
}
pub unsafe fn l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg(
    mut v_n_127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_n_127_, 9);
    v___f_128_ = crate::leanh::lean_alloc_closure(
        l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_128_, 0, v_n_127_);
    v___f_129_ = crate::leanh::lean_alloc_closure(
        l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_129_, 0, v_n_127_);
    v___f_130_ = crate::leanh::lean_alloc_closure(
        l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg___lam__2___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_130_, 0, v_n_127_);
    v___x_131_ =
        crate::leanh::lean_alloc_closure(l_Fin_add___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_131_, 0, v_n_127_);
    v___x_132_ =
        crate::leanh::lean_alloc_closure(l_Fin_mul___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_132_, 0, v_n_127_);
    v___f_133_ = crate::leanh::lean_alloc_closure(
        l_Fin_NatCast_instNatCast___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_133_, 0, v_n_127_);
    v___f_134_ = crate::leanh::lean_alloc_closure(
        l_Fin_neg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_134_, 0, v_n_127_);
    v___x_135_ =
        crate::leanh::lean_alloc_closure(l_Fin_sub___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_135_, 0, v_n_127_);
    v___x_136_ = crate::leanh::lean_alloc_closure(
        l_Lean_Grind_Fin_npow___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_136_, 0, v_n_127_);
    crate::leanh::lean_closure_set(v___x_136_, 1, crate::leanh::lean_box(0));
    v___x_137_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_137_, 0, v___x_131_);
    crate::leanh::lean_ctor_set(v___x_137_, 1, v___x_132_);
    crate::leanh::lean_ctor_set(v___x_137_, 2, v___f_133_);
    crate::leanh::lean_ctor_set(v___x_137_, 3, v___f_128_);
    crate::leanh::lean_ctor_set(v___x_137_, 4, v___f_129_);
    crate::leanh::lean_ctor_set(v___x_137_, 5, v___x_136_);
    v___x_138_ =
        crate::leanh::lean_alloc_closure(l_Fin_intCast___boxed as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_138_, 0, v_n_127_);
    crate::leanh::lean_closure_set(v___x_138_, 1, crate::leanh::lean_box(0));
    v___x_139_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_139_, 0, v___x_137_);
    crate::leanh::lean_ctor_set(v___x_139_, 1, v___f_134_);
    crate::leanh::lean_ctor_set(v___x_139_, 2, v___x_135_);
    crate::leanh::lean_ctor_set(v___x_139_, 3, v___x_138_);
    crate::leanh::lean_ctor_set(v___x_139_, 4, v___f_130_);
    return v___x_139_;
}
pub unsafe fn l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat(
    mut v_n_140_: *mut crate::leanh::LeanObject,
    mut v_inst_141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_142_ = l_Lean_Grind_Fin_instCommRingFinOfNeZeroNat___redArg(v_n_140_);
    return v___x_142_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_GrindInstances_Ring_Fin(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Zero(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_GrindInstances_Ring_Fin(
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
pub unsafe fn initialize_Init_GrindInstances_Ring_Fin(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Zero(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_GrindInstances_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_GrindInstances_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Ring_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_MinMax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_Ring_Fin(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_GrindInstances_Ring_Fin(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_GrindInstances_Ring_Fin(builtin);
}
