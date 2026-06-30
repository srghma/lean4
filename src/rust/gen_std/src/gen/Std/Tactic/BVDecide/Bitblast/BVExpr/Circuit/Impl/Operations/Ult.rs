// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Ult
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Carry Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Carry::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry,
    l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Not::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not,
    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not,
};
pub static l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg___closed__0_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        1 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(
    mut v_inst_72_: *mut leanh::LeanObject,
    mut v_inst_73_: *mut leanh::LeanObject,
    mut v_w_74_: *mut leanh::LeanObject,
    mut v_aig_75_: *mut leanh::LeanObject,
    mut v_pair_76_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_77_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_78_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_80_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_81_: u8 = 0;
    let mut v_res_82_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_83_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_84_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_85_: u8 = 0;
    let mut v_trueRef_86_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_88_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_89_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_90_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_91_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_92_: u8 = 0;
    let mut v_aig_93_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_95_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_96_: u8 = 0;
    let mut v_gate_97_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_99_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_100_: u8 = 0;
    let mut v___x_102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_107_: u8 = 0;
    let mut v_isSharedCheck_108_: u8 = 0;
    let mut v_unused_109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_113_: u8 = 0;
    let mut v_gate_114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_117_: u8 = 0;
    let mut v___x_118_: u8 = 0;
    let mut v___x_120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_125_: u8 = 0;
    let mut v_isSharedCheck_126_: u8 = 0;
    let mut v_unused_127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_129_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_77_ = leanh::lean_ctor_get(v_pair_76_, 0);
                v_rhs_78_ = leanh::lean_ctor_get(v_pair_76_, 1);
                v_isSharedCheck_129_ = (!leanh::lean_is_exclusive(v_pair_76_)) as u8;
                if v_isSharedCheck_129_ == 0 {
                    v___x_80_ = v_pair_76_;
                    v_isShared_81_ = v_isSharedCheck_129_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rhs_78_);
                    leanh::lean_inc(v_lhs_77_);
                    leanh::lean_dec(v_pair_76_);
                    v___x_80_ = leanh::lean_box(0);
                    v_isShared_81_ = v_isSharedCheck_129_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_73_);
                leanh::lean_inc_ref(v_inst_72_);
                v_res_82_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(
                    v_inst_72_, v_inst_73_, v_w_74_, v_aig_75_, v_rhs_78_,
                );
                v_aig_83_ = leanh::lean_ctor_get(v_res_82_, 0);
                leanh::lean_inc_ref(v_aig_83_);
                v_vec_84_ = leanh::lean_ctor_get(v_res_82_, 1);
                leanh::lean_inc_ref(v_vec_84_);
                leanh::lean_dec_ref(v_res_82_);
                v___x_85_ = 1;
                v_trueRef_86_ = l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg___closed__0;
                if v_isShared_81_ == 0 {
                    leanh::lean_ctor_set(v___x_80_, 1, v_vec_84_);
                    v___x_88_ = v___x_80_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_128_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_128_, 0, v_lhs_77_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_128_, 1, v_vec_84_);
                    v___x_88_ = v_reuseFailAlloc_128_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_89_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_89_, 0, v_w_74_);
                leanh::lean_ctor_set(v___x_89_, 1, v___x_88_);
                leanh::lean_ctor_set(v___x_89_, 2, v_trueRef_86_);
                v_res_90_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(
                    v_inst_72_, v_inst_73_, v_aig_83_, v___x_89_,
                );
                v_ref_91_ = leanh::lean_ctor_get(v_res_90_, 1);
                leanh::lean_inc_ref(v_ref_91_);
                v_invert_92_ = leanh::lean_ctor_get_uint8(
                    v_ref_91_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_92_ == 0 {
                    v_aig_93_ = leanh::lean_ctor_get(v_res_90_, 0);
                    v_isSharedCheck_108_ = (!leanh::lean_is_exclusive(v_res_90_)) as u8;
                    if v_isSharedCheck_108_ == 0 {
                        v_unused_109_ = leanh::lean_ctor_get(v_res_90_, 1);
                        leanh::lean_dec(v_unused_109_);
                        v___x_95_ = v_res_90_;
                        v_isShared_96_ = v_isSharedCheck_108_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_aig_93_);
                        leanh::lean_dec(v_res_90_);
                        v___x_95_ = leanh::lean_box(0);
                        v_isShared_96_ = v_isSharedCheck_108_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_aig_110_ = leanh::lean_ctor_get(v_res_90_, 0);
                    v_isSharedCheck_126_ = (!leanh::lean_is_exclusive(v_res_90_)) as u8;
                    if v_isSharedCheck_126_ == 0 {
                        v_unused_127_ = leanh::lean_ctor_get(v_res_90_, 1);
                        leanh::lean_dec(v_unused_127_);
                        v___x_112_ = v_res_90_;
                        v_isShared_113_ = v_isSharedCheck_126_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_aig_110_);
                        leanh::lean_dec(v_res_90_);
                        v___x_112_ = leanh::lean_box(0);
                        v_isShared_113_ = v_isSharedCheck_126_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v_gate_97_ = leanh::lean_ctor_get(v_ref_91_, 0);
                v_isSharedCheck_107_ = (!leanh::lean_is_exclusive(v_ref_91_)) as u8;
                if v_isSharedCheck_107_ == 0 {
                    v___x_99_ = v_ref_91_;
                    v_isShared_100_ = v_isSharedCheck_107_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_97_);
                    leanh::lean_dec(v_ref_91_);
                    v___x_99_ = leanh::lean_box(0);
                    v_isShared_100_ = v_isSharedCheck_107_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_100_ == 0 {
                    v___x_102_ = v___x_99_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_106_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_106_, 0, v_gate_97_);
                    v___x_102_ = v_reuseFailAlloc_106_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_ctor_set_uint8(
                    v___x_102_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_85_,
                );
                if v_isShared_96_ == 0 {
                    leanh::lean_ctor_set(v___x_95_, 1, v___x_102_);
                    v___x_104_ = v___x_95_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_105_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_105_, 0, v_aig_93_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_105_, 1, v___x_102_);
                    v___x_104_ = v_reuseFailAlloc_105_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_104_;
            }
            7 => {
                v_gate_114_ = leanh::lean_ctor_get(v_ref_91_, 0);
                v_isSharedCheck_125_ = (!leanh::lean_is_exclusive(v_ref_91_)) as u8;
                if v_isSharedCheck_125_ == 0 {
                    v___x_116_ = v_ref_91_;
                    v_isShared_117_ = v_isSharedCheck_125_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_114_);
                    leanh::lean_dec(v_ref_91_);
                    v___x_116_ = leanh::lean_box(0);
                    v_isShared_117_ = v_isSharedCheck_125_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_118_ = 0;
                if v_isShared_117_ == 0 {
                    v___x_120_ = v___x_116_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_124_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_124_, 0, v_gate_114_);
                    v___x_120_ = v_reuseFailAlloc_124_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                leanh::lean_ctor_set_uint8(
                    v___x_120_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_118_,
                );
                if v_isShared_113_ == 0 {
                    leanh::lean_ctor_set(v___x_112_, 1, v___x_120_);
                    v___x_122_ = v___x_112_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_123_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_123_, 0, v_aig_110_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_123_, 1, v___x_120_);
                    v___x_122_ = v_reuseFailAlloc_123_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_122_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_mkUlt(
    mut v_00_u03b1_130_: *mut leanh::LeanObject,
    mut v_inst_131_: *mut leanh::LeanObject,
    mut v_inst_132_: *mut leanh::LeanObject,
    mut v_w_133_: *mut leanh::LeanObject,
    mut v_aig_134_: *mut leanh::LeanObject,
    mut v_pair_135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_136_ = l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(
        v_inst_131_,
        v_inst_132_,
        v_w_133_,
        v_aig_134_,
        v_pair_135_,
    );
    return v___x_136_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(builtin);
}