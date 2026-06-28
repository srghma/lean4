// Lean compiler output
// Module: Lean.Elab.Tactic.Omega.MinNatAbs
// Imports: Init.Data.Int.Order Init.Data.List.MinMax Init.Data.Nat.Order Init.ByCases Init.Data.Bool Init.Data.Option.Lemmas Init.TacticsExtra
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Int::Order::{
    initialize_Init_Data_Int_Order, runtime_initialize_Init_Data_Int_Order,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::MinMax::{
    initialize_Init_Data_List_MinMax, runtime_initialize_Init_Data_List_MinMax,
};
use crate::r#gen::Init::Data::Nat::Order::{
    initialize_Init_Data_Nat_Order, runtime_initialize_Init_Data_Nat_Order,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_abs;
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_dec_le};
pub unsafe fn l_List_filterTR_loop___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__0(
    mut v_a_83_: *mut crate::leanh::LeanObject,
    mut v_a_84_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_90_: u8 = 0;
    let mut v___x_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_92_: u8 = 0;
    let mut v___x_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_98_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_83_) == 0 {
                    v___x_85_ = l_List_reverse___redArg(v_a_84_);
                    return v___x_85_;
                } else {
                    v_head_86_ = crate::leanh::lean_ctor_get(v_a_83_, 0);
                    v_tail_87_ = crate::leanh::lean_ctor_get(v_a_83_, 1);
                    v_isSharedCheck_98_ = (!crate::leanh::lean_is_exclusive(v_a_83_)) as u8;
                    if v_isSharedCheck_98_ == 0 {
                        v___x_89_ = v_a_83_;
                        v_isShared_90_ = v_isSharedCheck_98_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_87_);
                        crate::leanh::lean_inc(v_head_86_);
                        crate::leanh::lean_dec(v_a_83_);
                        v___x_89_ = crate::leanh::lean_box(0);
                        v_isShared_90_ = v_isSharedCheck_98_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_91_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_92_ = lean_nat_dec_eq(v_head_86_, v___x_91_);
                if v___x_92_ == 0 {
                    if v_isShared_90_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_89_, 1, v_a_84_);
                        v___x_94_ = v___x_89_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_96_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_96_, 0, v_head_86_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_96_, 1, v_a_84_);
                        v___x_94_ = v_reuseFailAlloc_96_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_89_);
                    crate::leanh::lean_dec(v_head_86_);
                    v_a_83_ = v_tail_87_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_a_83_ = v_tail_87_;
                v_a_84_ = v___x_94_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1_spec__1(
    mut v_x_99_: *mut crate::leanh::LeanObject,
    mut v_x_100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_103_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_100_) == 0 {
                    crate::leanh::lean_inc(v_x_99_);
                    return v_x_99_;
                } else {
                    v_head_101_ = crate::leanh::lean_ctor_get(v_x_100_, 0);
                    v_tail_102_ = crate::leanh::lean_ctor_get(v_x_100_, 1);
                    v___x_103_ = lean_nat_dec_le(v_x_99_, v_head_101_);
                    if v___x_103_ == 0 {
                        v_x_99_ = v_head_101_;
                        v_x_100_ = v_tail_102_;
                        state = 0;
                        continue;
                    } else {
                        v_x_100_ = v_tail_102_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1_spec__1___boxed(
    mut v_x_106_: *mut crate::leanh::LeanObject,
    mut v_x_107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_108_ = l_List_foldl___at___00List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1_spec__1(v_x_106_, v_x_107_);
    crate::leanh::lean_dec(v_x_107_);
    crate::leanh::lean_dec(v_x_106_);
    return v_res_108_;
}
pub unsafe fn l_List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1(
    mut v_x_109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_109_) == 0 {
        let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_110_ = crate::leanh::lean_box(0);
        return v___x_110_;
    } else {
        let mut v_head_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_111_ = crate::leanh::lean_ctor_get(v_x_109_, 0);
        v_tail_112_ = crate::leanh::lean_ctor_get(v_x_109_, 1);
        v___x_113_ = l_List_foldl___at___00List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1_spec__1(v_head_111_, v_tail_112_);
        v___x_114_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_114_, 0, v___x_113_);
        return v___x_114_;
    }
}
pub unsafe fn l_List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1___boxed(
    mut v_x_115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_116_ =
        l_List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1(v_x_115_);
    crate::leanh::lean_dec(v_x_115_);
    return v_res_116_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_List_nonzeroMinimum(
    mut v_xs_117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_118_ = crate::leanh::lean_box(0);
    v___x_119_ = l_List_filterTR_loop___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__0(
        v_xs_117_, v___x_118_,
    );
    v___x_120_ =
        l_List_min_x3f___at___00Lean_Elab_Tactic_Omega_List_nonzeroMinimum_spec__1(v___x_119_);
    crate::leanh::lean_dec(v___x_119_);
    if crate::leanh::lean_obj_tag(v___x_120_) == 0 {
        let mut v___x_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_121_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_121_;
    } else {
        let mut v_val_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_122_ = crate::leanh::lean_ctor_get(v___x_120_, 0);
        crate::leanh::lean_inc(v_val_122_);
        crate::leanh::lean_dec_ref_known(v___x_120_, 1);
        return v_val_122_;
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_List_minNatAbs_spec__0(
    mut v_a_123_: *mut crate::leanh::LeanObject,
    mut v_a_124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_130_: u8 = 0;
    let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_136_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_123_) == 0 {
                    v___x_125_ = l_List_reverse___redArg(v_a_124_);
                    return v___x_125_;
                } else {
                    v_head_126_ = crate::leanh::lean_ctor_get(v_a_123_, 0);
                    v_tail_127_ = crate::leanh::lean_ctor_get(v_a_123_, 1);
                    v_isSharedCheck_136_ = (!crate::leanh::lean_is_exclusive(v_a_123_)) as u8;
                    if v_isSharedCheck_136_ == 0 {
                        v___x_129_ = v_a_123_;
                        v_isShared_130_ = v_isSharedCheck_136_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_127_);
                        crate::leanh::lean_inc(v_head_126_);
                        crate::leanh::lean_dec(v_a_123_);
                        v___x_129_ = crate::leanh::lean_box(0);
                        v_isShared_130_ = v_isSharedCheck_136_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_131_ = lean_nat_abs(v_head_126_);
                crate::leanh::lean_dec(v_head_126_);
                if v_isShared_130_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_129_, 1, v_a_124_);
                    crate::leanh::lean_ctor_set(v___x_129_, 0, v___x_131_);
                    v___x_133_ = v___x_129_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_135_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_131_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_135_, 1, v_a_124_);
                    v___x_133_ = v_reuseFailAlloc_135_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_123_ = v_tail_127_;
                v_a_124_ = v___x_133_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_List_minNatAbs(
    mut v_xs_137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_138_ = crate::leanh::lean_box(0);
    v___x_139_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_List_minNatAbs_spec__0(
        v_xs_137_, v___x_138_,
    );
    v___x_140_ = l_Lean_Elab_Tactic_Omega_List_nonzeroMinimum(v___x_139_);
    return v___x_140_;
}
pub unsafe fn l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0_spec__0(
    mut v_x_141_: *mut crate::leanh::LeanObject,
    mut v_x_142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_142_) == 0 {
                    crate::leanh::lean_inc(v_x_141_);
                    return v_x_141_;
                } else {
                    v_head_143_ = crate::leanh::lean_ctor_get(v_x_142_, 0);
                    v_tail_144_ = crate::leanh::lean_ctor_get(v_x_142_, 1);
                    v___x_145_ = lean_nat_dec_le(v_x_141_, v_head_143_);
                    if v___x_145_ == 0 {
                        v_x_142_ = v_tail_144_;
                        state = 0;
                        continue;
                    } else {
                        v_x_141_ = v_head_143_;
                        v_x_142_ = v_tail_144_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0_spec__0___boxed(
    mut v_x_148_: *mut crate::leanh::LeanObject,
    mut v_x_149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_150_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0_spec__0(v_x_148_, v_x_149_);
    crate::leanh::lean_dec(v_x_149_);
    crate::leanh::lean_dec(v_x_148_);
    return v_res_150_;
}
pub unsafe fn l_List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0(
    mut v_x_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_151_) == 0 {
        let mut v___x_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_152_ = crate::leanh::lean_box(0);
        return v___x_152_;
    } else {
        let mut v_head_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_153_ = crate::leanh::lean_ctor_get(v_x_151_, 0);
        v_tail_154_ = crate::leanh::lean_ctor_get(v_x_151_, 1);
        v___x_155_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0_spec__0(v_head_153_, v_tail_154_);
        v___x_156_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_156_, 0, v___x_155_);
        return v___x_156_;
    }
}
pub unsafe fn l_List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0___boxed(
    mut v_x_157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_158_ = l_List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0(v_x_157_);
    crate::leanh::lean_dec(v_x_157_);
    return v_res_158_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_List_maxNatAbs(
    mut v_xs_159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_160_ = crate::leanh::lean_box(0);
    v___x_161_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_List_minNatAbs_spec__0(
        v_xs_159_, v___x_160_,
    );
    v___x_162_ = l_List_max_x3f___at___00Lean_Elab_Tactic_Omega_List_maxNatAbs_spec__0(v___x_161_);
    crate::leanh::lean_dec(v___x_161_);
    if crate::leanh::lean_obj_tag(v___x_162_) == 0 {
        let mut v___x_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_163_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_163_;
    } else {
        let mut v_val_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_164_ = crate::leanh::lean_ctor_get(v___x_162_, 0);
        crate::leanh::lean_inc(v_val_164_);
        crate::leanh::lean_dec_ref_known(v___x_162_, 1);
        return v_val_164_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Omega_MinNatAbs(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_MinMax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Omega_MinNatAbs(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Omega_MinNatAbs(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_MinMax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Omega_MinNatAbs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Omega_MinNatAbs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Omega_MinNatAbs(builtin);
}
