// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Neg
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
use crate::r#gen::Init::Prelude::l_BitVec_ofNat;
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Const::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const,
    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Add::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add,
    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Not::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not,
    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_unsigned_to_nat,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___redArg(
    mut v_inst_40_: *mut LeanObject,
    mut v_inst_41_: *mut LeanObject,
    mut v_w_42_: *mut LeanObject,
    mut v_aig_43_: *mut LeanObject,
    mut v_input_44_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_45_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_46_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_47_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_49_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_50_: u8 = 0;
    let mut v___x_51_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_52_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_53_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_55_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_56_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_57_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_58_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_inst_41_);
                lean_inc_ref(v_inst_40_);
                v_res_45_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(
                    v_inst_40_,
                    v_inst_41_,
                    v_w_42_,
                    v_aig_43_,
                    v_input_44_,
                );
                v_aig_46_ = lean_ctor_get(v_res_45_, 0);
                v_vec_47_ = lean_ctor_get(v_res_45_, 1);
                v_isSharedCheck_58_ = (!lean_is_exclusive(v_res_45_)) as u8;
                if v_isSharedCheck_58_ == 0 {
                    v___x_49_ = v_res_45_;
                    v_isShared_50_ = v_isSharedCheck_58_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vec_47_);
                    lean_inc(v_aig_46_);
                    lean_dec(v_res_45_);
                    v___x_49_ = lean_box(0);
                    v_isShared_50_ = v_isSharedCheck_58_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_51_ = lean_unsigned_to_nat(1);
                v___x_52_ = l_BitVec_ofNat(v_w_42_, v___x_51_);
                v_one_53_ =
                    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_42_, v___x_52_);
                lean_dec(v___x_52_);
                if v_isShared_50_ == 0 {
                    lean_ctor_set(v___x_49_, 1, v_one_53_);
                    lean_ctor_set(v___x_49_, 0, v_vec_47_);
                    v___x_55_ = v___x_49_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_57_, 0, v_vec_47_);
                    lean_ctor_set(v_reuseFailAlloc_57_, 1, v_one_53_);
                    v___x_55_ = v_reuseFailAlloc_57_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_56_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(
                    v_inst_40_, v_inst_41_, v_w_42_, v_aig_46_, v___x_55_,
                );
                return v___x_56_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___redArg___boxed(
    mut v_inst_59_: *mut LeanObject,
    mut v_inst_60_: *mut LeanObject,
    mut v_w_61_: *mut LeanObject,
    mut v_aig_62_: *mut LeanObject,
    mut v_input_63_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_64_: *mut LeanObject = core::ptr::null_mut();
    v_res_64_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___redArg(
        v_inst_59_,
        v_inst_60_,
        v_w_61_,
        v_aig_62_,
        v_input_63_,
    );
    lean_dec(v_w_61_);
    return v_res_64_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg(
    mut v_00_u03b1_65_: *mut LeanObject,
    mut v_inst_66_: *mut LeanObject,
    mut v_inst_67_: *mut LeanObject,
    mut v_w_68_: *mut LeanObject,
    mut v_aig_69_: *mut LeanObject,
    mut v_input_70_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_71_: *mut LeanObject = core::ptr::null_mut();
    v___x_71_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___redArg(
        v_inst_66_,
        v_inst_67_,
        v_w_68_,
        v_aig_69_,
        v_input_70_,
    );
    return v___x_71_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___boxed(
    mut v_00_u03b1_72_: *mut LeanObject,
    mut v_inst_73_: *mut LeanObject,
    mut v_inst_74_: *mut LeanObject,
    mut v_w_75_: *mut LeanObject,
    mut v_aig_76_: *mut LeanObject,
    mut v_input_77_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_78_: *mut LeanObject = core::ptr::null_mut();
    v_res_78_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg(
        v_00_u03b1_72_,
        v_inst_73_,
        v_inst_74_,
        v_w_75_,
        v_aig_76_,
        v_input_77_,
    );
    lean_dec(v_w_75_);
    return v_res_78_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(builtin);
}
