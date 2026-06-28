// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Solve
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Finish
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::Tactic::Grind::Action::l_Lean_Meta_Grind_Action_run;
use crate::r#gen::Lean::Meta::Tactic::Grind::Finish::{
    initialize_Lean_Meta_Tactic_Grind_Finish, l_Lean_Meta_Grind_Action_mkFinish,
    runtime_initialize_Lean_Meta_Tactic_Grind_Finish,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unsigned_to_nat,
};
pub unsafe fn l_Lean_Meta_Grind_solve(
    mut v_goal_76_: *mut LeanObject,
    mut v_a_77_: *mut LeanObject,
    mut v_a_78_: *mut LeanObject,
    mut v_a_79_: *mut LeanObject,
    mut v_a_80_: *mut LeanObject,
    mut v_a_81_: *mut LeanObject,
    mut v_a_82_: *mut LeanObject,
    mut v_a_83_: *mut LeanObject,
    mut v_a_84_: *mut LeanObject,
    mut v_a_85_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_87_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_88_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_89_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_90_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_91_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_93_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_94_: u8 = 0;
    let mut v___x_95_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_97_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_98_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gs_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_102_: u8 = 0;
    let mut v_head_103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_116_: u8 = 0;
    let mut v_isSharedCheck_117_: u8 = 0;
    let mut v_a_118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_121_: u8 = 0;
    let mut v___x_123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_125_: u8 = 0;
    let mut v_a_126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_129_: u8 = 0;
    let mut v_ref_130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_87_ = lean_unsigned_to_nat(10000);
                v___x_88_ = l_Lean_Meta_Grind_Action_mkFinish(v___x_87_);
                if lean_obj_tag(v___x_88_) == 0 {
                    v_a_89_ = lean_ctor_get(v___x_88_, 0);
                    lean_inc(v_a_89_);
                    lean_dec_ref_known(v___x_88_, 1);
                    lean_inc_ref(v_goal_76_);
                    v___x_90_ = l_Lean_Meta_Grind_Action_run(
                        v_goal_76_, v_a_89_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_,
                        v_a_83_, v_a_84_, v_a_85_,
                    );
                    if lean_obj_tag(v___x_90_) == 0 {
                        v_a_91_ = lean_ctor_get(v___x_90_, 0);
                        v_isSharedCheck_117_ = (!lean_is_exclusive(v___x_90_)) as u8;
                        if v_isSharedCheck_117_ == 0 {
                            v___x_93_ = v___x_90_;
                            v_isShared_94_ = v_isSharedCheck_117_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_91_);
                            lean_dec(v___x_90_);
                            v___x_93_ = lean_box(0);
                            v_isShared_94_ = v_isSharedCheck_117_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_goal_76_);
                        v_a_118_ = lean_ctor_get(v___x_90_, 0);
                        v_isSharedCheck_125_ = (!lean_is_exclusive(v___x_90_)) as u8;
                        if v_isSharedCheck_125_ == 0 {
                            v___x_120_ = v___x_90_;
                            v_isShared_121_ = v_isSharedCheck_125_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_118_);
                            lean_dec(v___x_90_);
                            v___x_120_ = lean_box(0);
                            v_isShared_121_ = v_isSharedCheck_125_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_goal_76_);
                    v_a_126_ = lean_ctor_get(v___x_88_, 0);
                    v_isSharedCheck_138_ = (!lean_is_exclusive(v___x_88_)) as u8;
                    if v_isSharedCheck_138_ == 0 {
                        v___x_128_ = v___x_88_;
                        v_isShared_129_ = v_isSharedCheck_138_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_126_);
                        lean_dec(v___x_88_);
                        v___x_128_ = lean_box(0);
                        v_isShared_129_ = v_isSharedCheck_138_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_91_) == 0 {
                    lean_dec_ref_known(v_a_91_, 1);
                    lean_dec_ref(v_goal_76_);
                    v___x_95_ = lean_box(0);
                    if v_isShared_94_ == 0 {
                        lean_ctor_set(v___x_93_, 0, v___x_95_);
                        v___x_97_ = v___x_93_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_95_);
                        v___x_97_ = v_reuseFailAlloc_98_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_gs_99_ = lean_ctor_get(v_a_91_, 0);
                    v_isSharedCheck_116_ = (!lean_is_exclusive(v_a_91_)) as u8;
                    if v_isSharedCheck_116_ == 0 {
                        v___x_101_ = v_a_91_;
                        v_isShared_102_ = v_isSharedCheck_116_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_gs_99_);
                        lean_dec(v_a_91_);
                        v___x_101_ = lean_box(0);
                        v_isShared_102_ = v_isSharedCheck_116_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_97_;
            }
            3 => {
                if lean_obj_tag(v_gs_99_) == 1 {
                    lean_dec_ref(v_goal_76_);
                    v_head_103_ = lean_ctor_get(v_gs_99_, 0);
                    lean_inc(v_head_103_);
                    lean_dec_ref_known(v_gs_99_, 2);
                    if v_isShared_102_ == 0 {
                        lean_ctor_set(v___x_101_, 0, v_head_103_);
                        v___x_105_ = v___x_101_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_109_, 0, v_head_103_);
                        v___x_105_ = v_reuseFailAlloc_109_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_gs_99_);
                    if v_isShared_102_ == 0 {
                        lean_ctor_set(v___x_101_, 0, v_goal_76_);
                        v___x_111_ = v___x_101_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_115_, 0, v_goal_76_);
                        v___x_111_ = v_reuseFailAlloc_115_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_94_ == 0 {
                    lean_ctor_set(v___x_93_, 0, v___x_105_);
                    v___x_107_ = v___x_93_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_105_);
                    v___x_107_ = v_reuseFailAlloc_108_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_107_;
            }
            6 => {
                if v_isShared_94_ == 0 {
                    lean_ctor_set(v___x_93_, 0, v___x_111_);
                    v___x_113_ = v___x_93_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
                    v___x_113_ = v_reuseFailAlloc_114_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_113_;
            }
            8 => {
                if v_isShared_121_ == 0 {
                    v___x_123_ = v___x_120_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
                    v___x_123_ = v_reuseFailAlloc_124_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_123_;
            }
            10 => {
                v_ref_130_ = lean_ctor_get(v_a_84_, 5);
                v___x_131_ = lean_io_error_to_string(v_a_126_);
                v___x_132_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_132_, 0, v___x_131_);
                v___x_133_ = l_Lean_MessageData_ofFormat(v___x_132_);
                lean_inc(v_ref_130_);
                v___x_134_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_134_, 0, v_ref_130_);
                lean_ctor_set(v___x_134_, 1, v___x_133_);
                if v_isShared_129_ == 0 {
                    lean_ctor_set(v___x_128_, 0, v___x_134_);
                    v___x_136_ = v___x_128_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
                    v___x_136_ = v_reuseFailAlloc_137_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_solve___boxed(
    mut v_goal_139_: *mut LeanObject,
    mut v_a_140_: *mut LeanObject,
    mut v_a_141_: *mut LeanObject,
    mut v_a_142_: *mut LeanObject,
    mut v_a_143_: *mut LeanObject,
    mut v_a_144_: *mut LeanObject,
    mut v_a_145_: *mut LeanObject,
    mut v_a_146_: *mut LeanObject,
    mut v_a_147_: *mut LeanObject,
    mut v_a_148_: *mut LeanObject,
    mut v_a_149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_150_: *mut LeanObject = core::ptr::null_mut();
    v_res_150_ = l_Lean_Meta_Grind_solve(
        v_goal_139_,
        v_a_140_,
        v_a_141_,
        v_a_142_,
        v_a_143_,
        v_a_144_,
        v_a_145_,
        v_a_146_,
        v_a_147_,
        v_a_148_,
    );
    lean_dec(v_a_148_);
    lean_dec_ref(v_a_147_);
    lean_dec(v_a_146_);
    lean_dec_ref(v_a_145_);
    lean_dec(v_a_144_);
    lean_dec_ref(v_a_143_);
    lean_dec(v_a_142_);
    lean_dec_ref(v_a_141_);
    lean_dec(v_a_140_);
    return v_res_150_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Solve(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Solve(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Solve(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Solve(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Solve(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Solve(builtin);
}
