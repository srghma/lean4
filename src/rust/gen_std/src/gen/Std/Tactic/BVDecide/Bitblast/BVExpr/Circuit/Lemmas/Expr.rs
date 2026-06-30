// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Expr
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Var Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ShiftRight Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Append Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Replicate Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Extract Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.RotateLeft Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.RotateRight Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Mul Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Umod Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Reverse Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Clz Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr Init.ByCases Init.Data.Nat.Linear Init.Omega
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Var::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Var, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Var};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Operations::ShiftRight::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_ShiftRight, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_ShiftRight};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Operations::Append::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Append, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Append};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Operations::Replicate::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Replicate, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Replicate};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Operations::Extract::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Extract, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Extract};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Operations::RotateLeft::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateLeft, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateLeft};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Operations::RotateRight::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateRight, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateRight};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Operations::Mul::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Mul, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Mul};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Operations::Umod::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Operations::Reverse::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Reverse, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Reverse};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Operations::Clz::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Clz, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Clz};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Operations::Cpop::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Cpop, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Cpop};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Expr::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Nat::Linear::{initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter___redArg(
    mut v_x_257_: *mut leanh::LeanObject,
    mut v_h__1_258_: *mut leanh::LeanObject,
    mut v_h__2_259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_257_) == 0 {
        let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_258_);
        v___x_260_ = leanh::lean_apply_1(v_h__2_259_, leanh::lean_box(0));
        return v___x_260_;
    } else {
        let mut v_val_261_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_259_);
        v_val_261_ = leanh::lean_ctor_get(v_x_257_, 0);
        leanh::lean_inc(v_val_261_);
        leanh::lean_dec_ref_known(v_x_257_, 1);
        v___x_262_ = leanh::lean_apply_2(v_h__1_258_, v_val_261_, leanh::lean_box(0));
        return v___x_262_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter(
    mut v_w_263_: *mut leanh::LeanObject,
    mut v_expr_264_: *mut leanh::LeanObject,
    mut v_motive_265_: *mut leanh::LeanObject,
    mut v_x_266_: *mut leanh::LeanObject,
    mut v_h__1_267_: *mut leanh::LeanObject,
    mut v_h__2_268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_266_) == 0 {
        let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_267_);
        v___x_269_ = leanh::lean_apply_1(v_h__2_268_, leanh::lean_box(0));
        return v___x_269_;
    } else {
        let mut v_val_270_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_268_);
        v_val_270_ = leanh::lean_ctor_get(v_x_266_, 0);
        leanh::lean_inc(v_val_270_);
        leanh::lean_dec_ref_known(v_x_266_, 1);
        v___x_271_ = leanh::lean_apply_2(v_h__1_267_, v_val_270_, leanh::lean_box(0));
        return v___x_271_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter___boxed(
    mut v_w_272_: *mut leanh::LeanObject,
    mut v_expr_273_: *mut leanh::LeanObject,
    mut v_motive_274_: *mut leanh::LeanObject,
    mut v_x_275_: *mut leanh::LeanObject,
    mut v_h__1_276_: *mut leanh::LeanObject,
    mut v_h__2_277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_278_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter(v_w_272_, v_expr_273_, v_motive_274_, v_x_275_, v_h__1_276_, v_h__2_277_);
    leanh::lean_dec_ref(v_expr_273_);
    leanh::lean_dec(v_w_272_);
    return v_res_278_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter___redArg(
    mut v_x_279_: *mut leanh::LeanObject,
    mut v_h__1_280_: *mut leanh::LeanObject,
    mut v_h__2_281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_279_) == 0 {
        let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_280_);
        v___x_282_ = leanh::lean_box(0);
        v___x_283_ = leanh::lean_apply_1(v_h__2_281_, v___x_282_);
        return v___x_283_;
    } else {
        let mut v_val_284_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_281_);
        v_val_284_ = leanh::lean_ctor_get(v_x_279_, 0);
        leanh::lean_inc(v_val_284_);
        leanh::lean_dec_ref_known(v_x_279_, 1);
        v___x_285_ = leanh::lean_apply_1(v_h__1_280_, v_val_284_);
        return v___x_285_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter(
    mut v_w_286_: *mut leanh::LeanObject,
    mut v_aig_287_: *mut leanh::LeanObject,
    mut v_motive_288_: *mut leanh::LeanObject,
    mut v_x_289_: *mut leanh::LeanObject,
    mut v_h__1_290_: *mut leanh::LeanObject,
    mut v_h__2_291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_289_) == 0 {
        let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_290_);
        v___x_292_ = leanh::lean_box(0);
        v___x_293_ = leanh::lean_apply_1(v_h__2_291_, v___x_292_);
        return v___x_293_;
    } else {
        let mut v_val_294_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_291_);
        v_val_294_ = leanh::lean_ctor_get(v_x_289_, 0);
        leanh::lean_inc(v_val_294_);
        leanh::lean_dec_ref_known(v_x_289_, 1);
        v___x_295_ = leanh::lean_apply_1(v_h__1_290_, v_val_294_);
        return v___x_295_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter___boxed(
    mut v_w_296_: *mut leanh::LeanObject,
    mut v_aig_297_: *mut leanh::LeanObject,
    mut v_motive_298_: *mut leanh::LeanObject,
    mut v_x_299_: *mut leanh::LeanObject,
    mut v_h__1_300_: *mut leanh::LeanObject,
    mut v_h__2_301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_302_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter(v_w_296_, v_aig_297_, v_motive_298_, v_x_299_, v_h__1_300_, v_h__2_301_);
    leanh::lean_dec_ref(v_aig_297_);
    leanh::lean_dec(v_w_296_);
    return v_res_302_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__17_splitter___redArg(
    mut v_w_303_: *mut leanh::LeanObject,
    mut v_expr_304_: *mut leanh::LeanObject,
    mut v_h__1_305_: *mut leanh::LeanObject,
    mut v_h__2_306_: *mut leanh::LeanObject,
    mut v_h__3_307_: *mut leanh::LeanObject,
    mut v_h__4_308_: *mut leanh::LeanObject,
    mut v_h__5_309_: *mut leanh::LeanObject,
    mut v_h__6_310_: *mut leanh::LeanObject,
    mut v_h__7_311_: *mut leanh::LeanObject,
    mut v_h__8_312_: *mut leanh::LeanObject,
    mut v_h__9_313_: *mut leanh::LeanObject,
    mut v_h__10_314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_expr_304_) {
        0 => {
            let mut v_idx_315_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_314_);
            leanh::lean_dec(v_h__9_313_);
            leanh::lean_dec(v_h__8_312_);
            leanh::lean_dec(v_h__7_311_);
            leanh::lean_dec(v_h__6_310_);
            leanh::lean_dec(v_h__5_309_);
            leanh::lean_dec(v_h__4_308_);
            leanh::lean_dec(v_h__3_307_);
            leanh::lean_dec(v_h__2_306_);
            v_idx_315_ = leanh::lean_ctor_get(v_expr_304_, 1);
            leanh::lean_inc(v_idx_315_);
            leanh::lean_dec_ref_known(v_expr_304_, 2);
            v___x_316_ = leanh::lean_apply_2(v_h__1_305_, v_w_303_, v_idx_315_);
            return v___x_316_;
        }
        1 => {
            let mut v_val_317_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_314_);
            leanh::lean_dec(v_h__9_313_);
            leanh::lean_dec(v_h__8_312_);
            leanh::lean_dec(v_h__7_311_);
            leanh::lean_dec(v_h__6_310_);
            leanh::lean_dec(v_h__5_309_);
            leanh::lean_dec(v_h__4_308_);
            leanh::lean_dec(v_h__3_307_);
            leanh::lean_dec(v_h__1_305_);
            v_val_317_ = leanh::lean_ctor_get(v_expr_304_, 1);
            leanh::lean_inc(v_val_317_);
            leanh::lean_dec_ref_known(v_expr_304_, 2);
            v___x_318_ = leanh::lean_apply_2(v_h__2_306_, v_w_303_, v_val_317_);
            return v___x_318_;
        }
        2 => {
            let mut v_w_319_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_start_320_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_321_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_314_);
            leanh::lean_dec(v_h__9_313_);
            leanh::lean_dec(v_h__8_312_);
            leanh::lean_dec(v_h__6_310_);
            leanh::lean_dec(v_h__5_309_);
            leanh::lean_dec(v_h__4_308_);
            leanh::lean_dec(v_h__3_307_);
            leanh::lean_dec(v_h__2_306_);
            leanh::lean_dec(v_h__1_305_);
            v_w_319_ = leanh::lean_ctor_get(v_expr_304_, 0);
            leanh::lean_inc(v_w_319_);
            v_start_320_ = leanh::lean_ctor_get(v_expr_304_, 1);
            leanh::lean_inc(v_start_320_);
            v_expr_321_ = leanh::lean_ctor_get(v_expr_304_, 3);
            leanh::lean_inc_ref(v_expr_321_);
            leanh::lean_dec_ref_known(v_expr_304_, 4);
            v___x_322_ = leanh::lean_apply_4(
                v_h__7_311_,
                v_w_303_,
                v_w_319_,
                v_start_320_,
                v_expr_321_,
            );
            return v___x_322_;
        }
        3 => {
            let mut v_lhs_323_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_op_324_: u8 = 0;
            let mut v_rhs_325_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_314_);
            leanh::lean_dec(v_h__9_313_);
            leanh::lean_dec(v_h__8_312_);
            leanh::lean_dec(v_h__7_311_);
            leanh::lean_dec(v_h__6_310_);
            leanh::lean_dec(v_h__5_309_);
            leanh::lean_dec(v_h__4_308_);
            leanh::lean_dec(v_h__2_306_);
            leanh::lean_dec(v_h__1_305_);
            v_lhs_323_ = leanh::lean_ctor_get(v_expr_304_, 1);
            leanh::lean_inc_ref(v_lhs_323_);
            v_op_324_ = leanh::lean_ctor_get_uint8(
                v_expr_304_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
            );
            v_rhs_325_ = leanh::lean_ctor_get(v_expr_304_, 2);
            leanh::lean_inc_ref(v_rhs_325_);
            leanh::lean_dec_ref_known(v_expr_304_, 3);
            v___x_326_ = leanh::lean_box((v_op_324_) as usize);
            v___x_327_ = leanh::lean_apply_4(
                v_h__3_307_,
                v_w_303_,
                v_lhs_323_,
                v___x_326_,
                v_rhs_325_,
            );
            return v___x_327_;
        }
        4 => {
            let mut v_op_328_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_operand_329_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_314_);
            leanh::lean_dec(v_h__9_313_);
            leanh::lean_dec(v_h__8_312_);
            leanh::lean_dec(v_h__7_311_);
            leanh::lean_dec(v_h__6_310_);
            leanh::lean_dec(v_h__5_309_);
            leanh::lean_dec(v_h__3_307_);
            leanh::lean_dec(v_h__2_306_);
            leanh::lean_dec(v_h__1_305_);
            v_op_328_ = leanh::lean_ctor_get(v_expr_304_, 1);
            leanh::lean_inc(v_op_328_);
            v_operand_329_ = leanh::lean_ctor_get(v_expr_304_, 2);
            leanh::lean_inc_ref(v_operand_329_);
            leanh::lean_dec_ref_known(v_expr_304_, 3);
            v___x_330_ =
                leanh::lean_apply_3(v_h__4_308_, v_w_303_, v_op_328_, v_operand_329_);
            return v___x_330_;
        }
        5 => {
            let mut v_l_331_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_332_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_333_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_334_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_314_);
            leanh::lean_dec(v_h__9_313_);
            leanh::lean_dec(v_h__8_312_);
            leanh::lean_dec(v_h__7_311_);
            leanh::lean_dec(v_h__6_310_);
            leanh::lean_dec(v_h__4_308_);
            leanh::lean_dec(v_h__3_307_);
            leanh::lean_dec(v_h__2_306_);
            leanh::lean_dec(v_h__1_305_);
            v_l_331_ = leanh::lean_ctor_get(v_expr_304_, 0);
            leanh::lean_inc(v_l_331_);
            v_r_332_ = leanh::lean_ctor_get(v_expr_304_, 1);
            leanh::lean_inc(v_r_332_);
            v_lhs_333_ = leanh::lean_ctor_get(v_expr_304_, 3);
            leanh::lean_inc_ref(v_lhs_333_);
            v_rhs_334_ = leanh::lean_ctor_get(v_expr_304_, 4);
            leanh::lean_inc_ref(v_rhs_334_);
            leanh::lean_dec_ref_known(v_expr_304_, 5);
            v___x_335_ = leanh::lean_apply_6(
                v_h__5_309_,
                v_w_303_,
                v_l_331_,
                v_r_332_,
                v_lhs_333_,
                v_rhs_334_,
                leanh::lean_box(0),
            );
            return v___x_335_;
        }
        6 => {
            let mut v_w_336_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_337_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_338_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_314_);
            leanh::lean_dec(v_h__9_313_);
            leanh::lean_dec(v_h__8_312_);
            leanh::lean_dec(v_h__7_311_);
            leanh::lean_dec(v_h__5_309_);
            leanh::lean_dec(v_h__4_308_);
            leanh::lean_dec(v_h__3_307_);
            leanh::lean_dec(v_h__2_306_);
            leanh::lean_dec(v_h__1_305_);
            v_w_336_ = leanh::lean_ctor_get(v_expr_304_, 0);
            leanh::lean_inc(v_w_336_);
            v_n_337_ = leanh::lean_ctor_get(v_expr_304_, 2);
            leanh::lean_inc(v_n_337_);
            v_expr_338_ = leanh::lean_ctor_get(v_expr_304_, 3);
            leanh::lean_inc_ref(v_expr_338_);
            leanh::lean_dec_ref_known(v_expr_304_, 4);
            v___x_339_ = leanh::lean_apply_5(
                v_h__6_310_,
                v_w_303_,
                v_w_336_,
                v_n_337_,
                v_expr_338_,
                leanh::lean_box(0),
            );
            return v___x_339_;
        }
        7 => {
            let mut v_n_340_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_341_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_342_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_314_);
            leanh::lean_dec(v_h__9_313_);
            leanh::lean_dec(v_h__7_311_);
            leanh::lean_dec(v_h__6_310_);
            leanh::lean_dec(v_h__5_309_);
            leanh::lean_dec(v_h__4_308_);
            leanh::lean_dec(v_h__3_307_);
            leanh::lean_dec(v_h__2_306_);
            leanh::lean_dec(v_h__1_305_);
            v_n_340_ = leanh::lean_ctor_get(v_expr_304_, 1);
            leanh::lean_inc(v_n_340_);
            v_lhs_341_ = leanh::lean_ctor_get(v_expr_304_, 2);
            leanh::lean_inc_ref(v_lhs_341_);
            v_rhs_342_ = leanh::lean_ctor_get(v_expr_304_, 3);
            leanh::lean_inc_ref(v_rhs_342_);
            leanh::lean_dec_ref_known(v_expr_304_, 4);
            v___x_343_ =
                leanh::lean_apply_4(v_h__8_312_, v_w_303_, v_n_340_, v_lhs_341_, v_rhs_342_);
            return v___x_343_;
        }
        8 => {
            let mut v_n_344_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_345_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_346_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_314_);
            leanh::lean_dec(v_h__8_312_);
            leanh::lean_dec(v_h__7_311_);
            leanh::lean_dec(v_h__6_310_);
            leanh::lean_dec(v_h__5_309_);
            leanh::lean_dec(v_h__4_308_);
            leanh::lean_dec(v_h__3_307_);
            leanh::lean_dec(v_h__2_306_);
            leanh::lean_dec(v_h__1_305_);
            v_n_344_ = leanh::lean_ctor_get(v_expr_304_, 1);
            leanh::lean_inc(v_n_344_);
            v_lhs_345_ = leanh::lean_ctor_get(v_expr_304_, 2);
            leanh::lean_inc_ref(v_lhs_345_);
            v_rhs_346_ = leanh::lean_ctor_get(v_expr_304_, 3);
            leanh::lean_inc_ref(v_rhs_346_);
            leanh::lean_dec_ref_known(v_expr_304_, 4);
            v___x_347_ =
                leanh::lean_apply_4(v_h__9_313_, v_w_303_, v_n_344_, v_lhs_345_, v_rhs_346_);
            return v___x_347_;
        }
        _ => {
            let mut v_n_348_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_349_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_350_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_313_);
            leanh::lean_dec(v_h__8_312_);
            leanh::lean_dec(v_h__7_311_);
            leanh::lean_dec(v_h__6_310_);
            leanh::lean_dec(v_h__5_309_);
            leanh::lean_dec(v_h__4_308_);
            leanh::lean_dec(v_h__3_307_);
            leanh::lean_dec(v_h__2_306_);
            leanh::lean_dec(v_h__1_305_);
            v_n_348_ = leanh::lean_ctor_get(v_expr_304_, 1);
            leanh::lean_inc(v_n_348_);
            v_lhs_349_ = leanh::lean_ctor_get(v_expr_304_, 2);
            leanh::lean_inc_ref(v_lhs_349_);
            v_rhs_350_ = leanh::lean_ctor_get(v_expr_304_, 3);
            leanh::lean_inc_ref(v_rhs_350_);
            leanh::lean_dec_ref_known(v_expr_304_, 4);
            v___x_351_ = leanh::lean_apply_4(
                v_h__10_314_,
                v_w_303_,
                v_n_348_,
                v_lhs_349_,
                v_rhs_350_,
            );
            return v___x_351_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__17_splitter(
    mut v_motive_352_: *mut leanh::LeanObject,
    mut v_w_353_: *mut leanh::LeanObject,
    mut v_expr_354_: *mut leanh::LeanObject,
    mut v_h__1_355_: *mut leanh::LeanObject,
    mut v_h__2_356_: *mut leanh::LeanObject,
    mut v_h__3_357_: *mut leanh::LeanObject,
    mut v_h__4_358_: *mut leanh::LeanObject,
    mut v_h__5_359_: *mut leanh::LeanObject,
    mut v_h__6_360_: *mut leanh::LeanObject,
    mut v_h__7_361_: *mut leanh::LeanObject,
    mut v_h__8_362_: *mut leanh::LeanObject,
    mut v_h__9_363_: *mut leanh::LeanObject,
    mut v_h__10_364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_expr_354_) {
        0 => {
            let mut v_idx_365_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_364_);
            leanh::lean_dec(v_h__9_363_);
            leanh::lean_dec(v_h__8_362_);
            leanh::lean_dec(v_h__7_361_);
            leanh::lean_dec(v_h__6_360_);
            leanh::lean_dec(v_h__5_359_);
            leanh::lean_dec(v_h__4_358_);
            leanh::lean_dec(v_h__3_357_);
            leanh::lean_dec(v_h__2_356_);
            v_idx_365_ = leanh::lean_ctor_get(v_expr_354_, 1);
            leanh::lean_inc(v_idx_365_);
            leanh::lean_dec_ref_known(v_expr_354_, 2);
            v___x_366_ = leanh::lean_apply_2(v_h__1_355_, v_w_353_, v_idx_365_);
            return v___x_366_;
        }
        1 => {
            let mut v_val_367_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_364_);
            leanh::lean_dec(v_h__9_363_);
            leanh::lean_dec(v_h__8_362_);
            leanh::lean_dec(v_h__7_361_);
            leanh::lean_dec(v_h__6_360_);
            leanh::lean_dec(v_h__5_359_);
            leanh::lean_dec(v_h__4_358_);
            leanh::lean_dec(v_h__3_357_);
            leanh::lean_dec(v_h__1_355_);
            v_val_367_ = leanh::lean_ctor_get(v_expr_354_, 1);
            leanh::lean_inc(v_val_367_);
            leanh::lean_dec_ref_known(v_expr_354_, 2);
            v___x_368_ = leanh::lean_apply_2(v_h__2_356_, v_w_353_, v_val_367_);
            return v___x_368_;
        }
        2 => {
            let mut v_w_369_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_start_370_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_371_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_364_);
            leanh::lean_dec(v_h__9_363_);
            leanh::lean_dec(v_h__8_362_);
            leanh::lean_dec(v_h__6_360_);
            leanh::lean_dec(v_h__5_359_);
            leanh::lean_dec(v_h__4_358_);
            leanh::lean_dec(v_h__3_357_);
            leanh::lean_dec(v_h__2_356_);
            leanh::lean_dec(v_h__1_355_);
            v_w_369_ = leanh::lean_ctor_get(v_expr_354_, 0);
            leanh::lean_inc(v_w_369_);
            v_start_370_ = leanh::lean_ctor_get(v_expr_354_, 1);
            leanh::lean_inc(v_start_370_);
            v_expr_371_ = leanh::lean_ctor_get(v_expr_354_, 3);
            leanh::lean_inc_ref(v_expr_371_);
            leanh::lean_dec_ref_known(v_expr_354_, 4);
            v___x_372_ = leanh::lean_apply_4(
                v_h__7_361_,
                v_w_353_,
                v_w_369_,
                v_start_370_,
                v_expr_371_,
            );
            return v___x_372_;
        }
        3 => {
            let mut v_lhs_373_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_op_374_: u8 = 0;
            let mut v_rhs_375_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_364_);
            leanh::lean_dec(v_h__9_363_);
            leanh::lean_dec(v_h__8_362_);
            leanh::lean_dec(v_h__7_361_);
            leanh::lean_dec(v_h__6_360_);
            leanh::lean_dec(v_h__5_359_);
            leanh::lean_dec(v_h__4_358_);
            leanh::lean_dec(v_h__2_356_);
            leanh::lean_dec(v_h__1_355_);
            v_lhs_373_ = leanh::lean_ctor_get(v_expr_354_, 1);
            leanh::lean_inc_ref(v_lhs_373_);
            v_op_374_ = leanh::lean_ctor_get_uint8(
                v_expr_354_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
            );
            v_rhs_375_ = leanh::lean_ctor_get(v_expr_354_, 2);
            leanh::lean_inc_ref(v_rhs_375_);
            leanh::lean_dec_ref_known(v_expr_354_, 3);
            v___x_376_ = leanh::lean_box((v_op_374_) as usize);
            v___x_377_ = leanh::lean_apply_4(
                v_h__3_357_,
                v_w_353_,
                v_lhs_373_,
                v___x_376_,
                v_rhs_375_,
            );
            return v___x_377_;
        }
        4 => {
            let mut v_op_378_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_operand_379_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_364_);
            leanh::lean_dec(v_h__9_363_);
            leanh::lean_dec(v_h__8_362_);
            leanh::lean_dec(v_h__7_361_);
            leanh::lean_dec(v_h__6_360_);
            leanh::lean_dec(v_h__5_359_);
            leanh::lean_dec(v_h__3_357_);
            leanh::lean_dec(v_h__2_356_);
            leanh::lean_dec(v_h__1_355_);
            v_op_378_ = leanh::lean_ctor_get(v_expr_354_, 1);
            leanh::lean_inc(v_op_378_);
            v_operand_379_ = leanh::lean_ctor_get(v_expr_354_, 2);
            leanh::lean_inc_ref(v_operand_379_);
            leanh::lean_dec_ref_known(v_expr_354_, 3);
            v___x_380_ =
                leanh::lean_apply_3(v_h__4_358_, v_w_353_, v_op_378_, v_operand_379_);
            return v___x_380_;
        }
        5 => {
            let mut v_l_381_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_382_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_383_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_384_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_364_);
            leanh::lean_dec(v_h__9_363_);
            leanh::lean_dec(v_h__8_362_);
            leanh::lean_dec(v_h__7_361_);
            leanh::lean_dec(v_h__6_360_);
            leanh::lean_dec(v_h__4_358_);
            leanh::lean_dec(v_h__3_357_);
            leanh::lean_dec(v_h__2_356_);
            leanh::lean_dec(v_h__1_355_);
            v_l_381_ = leanh::lean_ctor_get(v_expr_354_, 0);
            leanh::lean_inc(v_l_381_);
            v_r_382_ = leanh::lean_ctor_get(v_expr_354_, 1);
            leanh::lean_inc(v_r_382_);
            v_lhs_383_ = leanh::lean_ctor_get(v_expr_354_, 3);
            leanh::lean_inc_ref(v_lhs_383_);
            v_rhs_384_ = leanh::lean_ctor_get(v_expr_354_, 4);
            leanh::lean_inc_ref(v_rhs_384_);
            leanh::lean_dec_ref_known(v_expr_354_, 5);
            v___x_385_ = leanh::lean_apply_6(
                v_h__5_359_,
                v_w_353_,
                v_l_381_,
                v_r_382_,
                v_lhs_383_,
                v_rhs_384_,
                leanh::lean_box(0),
            );
            return v___x_385_;
        }
        6 => {
            let mut v_w_386_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_387_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_388_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_364_);
            leanh::lean_dec(v_h__9_363_);
            leanh::lean_dec(v_h__8_362_);
            leanh::lean_dec(v_h__7_361_);
            leanh::lean_dec(v_h__5_359_);
            leanh::lean_dec(v_h__4_358_);
            leanh::lean_dec(v_h__3_357_);
            leanh::lean_dec(v_h__2_356_);
            leanh::lean_dec(v_h__1_355_);
            v_w_386_ = leanh::lean_ctor_get(v_expr_354_, 0);
            leanh::lean_inc(v_w_386_);
            v_n_387_ = leanh::lean_ctor_get(v_expr_354_, 2);
            leanh::lean_inc(v_n_387_);
            v_expr_388_ = leanh::lean_ctor_get(v_expr_354_, 3);
            leanh::lean_inc_ref(v_expr_388_);
            leanh::lean_dec_ref_known(v_expr_354_, 4);
            v___x_389_ = leanh::lean_apply_5(
                v_h__6_360_,
                v_w_353_,
                v_w_386_,
                v_n_387_,
                v_expr_388_,
                leanh::lean_box(0),
            );
            return v___x_389_;
        }
        7 => {
            let mut v_n_390_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_391_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_392_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_364_);
            leanh::lean_dec(v_h__9_363_);
            leanh::lean_dec(v_h__7_361_);
            leanh::lean_dec(v_h__6_360_);
            leanh::lean_dec(v_h__5_359_);
            leanh::lean_dec(v_h__4_358_);
            leanh::lean_dec(v_h__3_357_);
            leanh::lean_dec(v_h__2_356_);
            leanh::lean_dec(v_h__1_355_);
            v_n_390_ = leanh::lean_ctor_get(v_expr_354_, 1);
            leanh::lean_inc(v_n_390_);
            v_lhs_391_ = leanh::lean_ctor_get(v_expr_354_, 2);
            leanh::lean_inc_ref(v_lhs_391_);
            v_rhs_392_ = leanh::lean_ctor_get(v_expr_354_, 3);
            leanh::lean_inc_ref(v_rhs_392_);
            leanh::lean_dec_ref_known(v_expr_354_, 4);
            v___x_393_ =
                leanh::lean_apply_4(v_h__8_362_, v_w_353_, v_n_390_, v_lhs_391_, v_rhs_392_);
            return v___x_393_;
        }
        8 => {
            let mut v_n_394_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_395_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_396_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_364_);
            leanh::lean_dec(v_h__8_362_);
            leanh::lean_dec(v_h__7_361_);
            leanh::lean_dec(v_h__6_360_);
            leanh::lean_dec(v_h__5_359_);
            leanh::lean_dec(v_h__4_358_);
            leanh::lean_dec(v_h__3_357_);
            leanh::lean_dec(v_h__2_356_);
            leanh::lean_dec(v_h__1_355_);
            v_n_394_ = leanh::lean_ctor_get(v_expr_354_, 1);
            leanh::lean_inc(v_n_394_);
            v_lhs_395_ = leanh::lean_ctor_get(v_expr_354_, 2);
            leanh::lean_inc_ref(v_lhs_395_);
            v_rhs_396_ = leanh::lean_ctor_get(v_expr_354_, 3);
            leanh::lean_inc_ref(v_rhs_396_);
            leanh::lean_dec_ref_known(v_expr_354_, 4);
            v___x_397_ =
                leanh::lean_apply_4(v_h__9_363_, v_w_353_, v_n_394_, v_lhs_395_, v_rhs_396_);
            return v___x_397_;
        }
        _ => {
            let mut v_n_398_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_399_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_400_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_363_);
            leanh::lean_dec(v_h__8_362_);
            leanh::lean_dec(v_h__7_361_);
            leanh::lean_dec(v_h__6_360_);
            leanh::lean_dec(v_h__5_359_);
            leanh::lean_dec(v_h__4_358_);
            leanh::lean_dec(v_h__3_357_);
            leanh::lean_dec(v_h__2_356_);
            leanh::lean_dec(v_h__1_355_);
            v_n_398_ = leanh::lean_ctor_get(v_expr_354_, 1);
            leanh::lean_inc(v_n_398_);
            v_lhs_399_ = leanh::lean_ctor_get(v_expr_354_, 2);
            leanh::lean_inc_ref(v_lhs_399_);
            v_rhs_400_ = leanh::lean_ctor_get(v_expr_354_, 3);
            leanh::lean_inc_ref(v_rhs_400_);
            leanh::lean_dec_ref_known(v_expr_354_, 4);
            v___x_401_ = leanh::lean_apply_4(
                v_h__10_364_,
                v_w_353_,
                v_n_398_,
                v_lhs_399_,
                v_rhs_400_,
            );
            return v___x_401_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__15_splitter___redArg(
    mut v_op_402_: *mut leanh::LeanObject,
    mut v_h__1_403_: *mut leanh::LeanObject,
    mut v_h__2_404_: *mut leanh::LeanObject,
    mut v_h__3_405_: *mut leanh::LeanObject,
    mut v_h__4_406_: *mut leanh::LeanObject,
    mut v_h__5_407_: *mut leanh::LeanObject,
    mut v_h__6_408_: *mut leanh::LeanObject,
    mut v_h__7_409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_op_402_) {
        0 => {
            let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_409_);
            leanh::lean_dec(v_h__6_408_);
            leanh::lean_dec(v_h__5_407_);
            leanh::lean_dec(v_h__4_406_);
            leanh::lean_dec(v_h__3_405_);
            leanh::lean_dec(v_h__2_404_);
            v___x_410_ = leanh::lean_box(0);
            v___x_411_ = leanh::lean_apply_1(v_h__1_403_, v___x_410_);
            return v___x_411_;
        }
        1 => {
            let mut v_n_412_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_409_);
            leanh::lean_dec(v_h__6_408_);
            leanh::lean_dec(v_h__5_407_);
            leanh::lean_dec(v_h__4_406_);
            leanh::lean_dec(v_h__3_405_);
            leanh::lean_dec(v_h__1_403_);
            v_n_412_ = leanh::lean_ctor_get(v_op_402_, 0);
            leanh::lean_inc(v_n_412_);
            leanh::lean_dec_ref_known(v_op_402_, 1);
            v___x_413_ = leanh::lean_apply_1(v_h__2_404_, v_n_412_);
            return v___x_413_;
        }
        2 => {
            let mut v_n_414_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_409_);
            leanh::lean_dec(v_h__6_408_);
            leanh::lean_dec(v_h__5_407_);
            leanh::lean_dec(v_h__4_406_);
            leanh::lean_dec(v_h__2_404_);
            leanh::lean_dec(v_h__1_403_);
            v_n_414_ = leanh::lean_ctor_get(v_op_402_, 0);
            leanh::lean_inc(v_n_414_);
            leanh::lean_dec_ref_known(v_op_402_, 1);
            v___x_415_ = leanh::lean_apply_1(v_h__3_405_, v_n_414_);
            return v___x_415_;
        }
        3 => {
            let mut v_n_416_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_409_);
            leanh::lean_dec(v_h__6_408_);
            leanh::lean_dec(v_h__5_407_);
            leanh::lean_dec(v_h__3_405_);
            leanh::lean_dec(v_h__2_404_);
            leanh::lean_dec(v_h__1_403_);
            v_n_416_ = leanh::lean_ctor_get(v_op_402_, 0);
            leanh::lean_inc(v_n_416_);
            leanh::lean_dec_ref_known(v_op_402_, 1);
            v___x_417_ = leanh::lean_apply_1(v_h__4_406_, v_n_416_);
            return v___x_417_;
        }
        4 => {
            let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_409_);
            leanh::lean_dec(v_h__6_408_);
            leanh::lean_dec(v_h__4_406_);
            leanh::lean_dec(v_h__3_405_);
            leanh::lean_dec(v_h__2_404_);
            leanh::lean_dec(v_h__1_403_);
            v___x_418_ = leanh::lean_box(0);
            v___x_419_ = leanh::lean_apply_1(v_h__5_407_, v___x_418_);
            return v___x_419_;
        }
        5 => {
            let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_409_);
            leanh::lean_dec(v_h__5_407_);
            leanh::lean_dec(v_h__4_406_);
            leanh::lean_dec(v_h__3_405_);
            leanh::lean_dec(v_h__2_404_);
            leanh::lean_dec(v_h__1_403_);
            v___x_420_ = leanh::lean_box(0);
            v___x_421_ = leanh::lean_apply_1(v_h__6_408_, v___x_420_);
            return v___x_421_;
        }
        _ => {
            let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__6_408_);
            leanh::lean_dec(v_h__5_407_);
            leanh::lean_dec(v_h__4_406_);
            leanh::lean_dec(v_h__3_405_);
            leanh::lean_dec(v_h__2_404_);
            leanh::lean_dec(v_h__1_403_);
            v___x_422_ = leanh::lean_box(0);
            v___x_423_ = leanh::lean_apply_1(v_h__7_409_, v___x_422_);
            return v___x_423_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__15_splitter(
    mut v_motive_424_: *mut leanh::LeanObject,
    mut v_op_425_: *mut leanh::LeanObject,
    mut v_h__1_426_: *mut leanh::LeanObject,
    mut v_h__2_427_: *mut leanh::LeanObject,
    mut v_h__3_428_: *mut leanh::LeanObject,
    mut v_h__4_429_: *mut leanh::LeanObject,
    mut v_h__5_430_: *mut leanh::LeanObject,
    mut v_h__6_431_: *mut leanh::LeanObject,
    mut v_h__7_432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_op_425_) {
        0 => {
            let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_432_);
            leanh::lean_dec(v_h__6_431_);
            leanh::lean_dec(v_h__5_430_);
            leanh::lean_dec(v_h__4_429_);
            leanh::lean_dec(v_h__3_428_);
            leanh::lean_dec(v_h__2_427_);
            v___x_433_ = leanh::lean_box(0);
            v___x_434_ = leanh::lean_apply_1(v_h__1_426_, v___x_433_);
            return v___x_434_;
        }
        1 => {
            let mut v_n_435_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_432_);
            leanh::lean_dec(v_h__6_431_);
            leanh::lean_dec(v_h__5_430_);
            leanh::lean_dec(v_h__4_429_);
            leanh::lean_dec(v_h__3_428_);
            leanh::lean_dec(v_h__1_426_);
            v_n_435_ = leanh::lean_ctor_get(v_op_425_, 0);
            leanh::lean_inc(v_n_435_);
            leanh::lean_dec_ref_known(v_op_425_, 1);
            v___x_436_ = leanh::lean_apply_1(v_h__2_427_, v_n_435_);
            return v___x_436_;
        }
        2 => {
            let mut v_n_437_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_432_);
            leanh::lean_dec(v_h__6_431_);
            leanh::lean_dec(v_h__5_430_);
            leanh::lean_dec(v_h__4_429_);
            leanh::lean_dec(v_h__2_427_);
            leanh::lean_dec(v_h__1_426_);
            v_n_437_ = leanh::lean_ctor_get(v_op_425_, 0);
            leanh::lean_inc(v_n_437_);
            leanh::lean_dec_ref_known(v_op_425_, 1);
            v___x_438_ = leanh::lean_apply_1(v_h__3_428_, v_n_437_);
            return v___x_438_;
        }
        3 => {
            let mut v_n_439_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_432_);
            leanh::lean_dec(v_h__6_431_);
            leanh::lean_dec(v_h__5_430_);
            leanh::lean_dec(v_h__3_428_);
            leanh::lean_dec(v_h__2_427_);
            leanh::lean_dec(v_h__1_426_);
            v_n_439_ = leanh::lean_ctor_get(v_op_425_, 0);
            leanh::lean_inc(v_n_439_);
            leanh::lean_dec_ref_known(v_op_425_, 1);
            v___x_440_ = leanh::lean_apply_1(v_h__4_429_, v_n_439_);
            return v___x_440_;
        }
        4 => {
            let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_432_);
            leanh::lean_dec(v_h__6_431_);
            leanh::lean_dec(v_h__4_429_);
            leanh::lean_dec(v_h__3_428_);
            leanh::lean_dec(v_h__2_427_);
            leanh::lean_dec(v_h__1_426_);
            v___x_441_ = leanh::lean_box(0);
            v___x_442_ = leanh::lean_apply_1(v_h__5_430_, v___x_441_);
            return v___x_442_;
        }
        5 => {
            let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_432_);
            leanh::lean_dec(v_h__5_430_);
            leanh::lean_dec(v_h__4_429_);
            leanh::lean_dec(v_h__3_428_);
            leanh::lean_dec(v_h__2_427_);
            leanh::lean_dec(v_h__1_426_);
            v___x_443_ = leanh::lean_box(0);
            v___x_444_ = leanh::lean_apply_1(v_h__6_431_, v___x_443_);
            return v___x_444_;
        }
        _ => {
            let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__6_431_);
            leanh::lean_dec(v_h__5_430_);
            leanh::lean_dec(v_h__4_429_);
            leanh::lean_dec(v_h__3_428_);
            leanh::lean_dec(v_h__2_427_);
            leanh::lean_dec(v_h__1_426_);
            v___x_445_ = leanh::lean_box(0);
            v___x_446_ = leanh::lean_apply_1(v_h__7_432_, v___x_445_);
            return v___x_446_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg(
    mut v_op_447_: u8,
    mut v_h__1_448_: *mut leanh::LeanObject,
    mut v_h__2_449_: *mut leanh::LeanObject,
    mut v_h__3_450_: *mut leanh::LeanObject,
    mut v_h__4_451_: *mut leanh::LeanObject,
    mut v_h__5_452_: *mut leanh::LeanObject,
    mut v_h__6_453_: *mut leanh::LeanObject,
    mut v_h__7_454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_op_447_ {
        0 => {
            let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_454_);
            leanh::lean_dec(v_h__6_453_);
            leanh::lean_dec(v_h__5_452_);
            leanh::lean_dec(v_h__4_451_);
            leanh::lean_dec(v_h__3_450_);
            leanh::lean_dec(v_h__2_449_);
            v___x_455_ = leanh::lean_box(0);
            v___x_456_ = leanh::lean_apply_1(v_h__1_448_, v___x_455_);
            return v___x_456_;
        }
        1 => {
            let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_454_);
            leanh::lean_dec(v_h__6_453_);
            leanh::lean_dec(v_h__5_452_);
            leanh::lean_dec(v_h__4_451_);
            leanh::lean_dec(v_h__3_450_);
            leanh::lean_dec(v_h__1_448_);
            v___x_457_ = leanh::lean_box(0);
            v___x_458_ = leanh::lean_apply_1(v_h__2_449_, v___x_457_);
            return v___x_458_;
        }
        2 => {
            let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_454_);
            leanh::lean_dec(v_h__6_453_);
            leanh::lean_dec(v_h__5_452_);
            leanh::lean_dec(v_h__4_451_);
            leanh::lean_dec(v_h__2_449_);
            leanh::lean_dec(v_h__1_448_);
            v___x_459_ = leanh::lean_box(0);
            v___x_460_ = leanh::lean_apply_1(v_h__3_450_, v___x_459_);
            return v___x_460_;
        }
        3 => {
            let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_454_);
            leanh::lean_dec(v_h__6_453_);
            leanh::lean_dec(v_h__5_452_);
            leanh::lean_dec(v_h__3_450_);
            leanh::lean_dec(v_h__2_449_);
            leanh::lean_dec(v_h__1_448_);
            v___x_461_ = leanh::lean_box(0);
            v___x_462_ = leanh::lean_apply_1(v_h__4_451_, v___x_461_);
            return v___x_462_;
        }
        4 => {
            let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_454_);
            leanh::lean_dec(v_h__6_453_);
            leanh::lean_dec(v_h__4_451_);
            leanh::lean_dec(v_h__3_450_);
            leanh::lean_dec(v_h__2_449_);
            leanh::lean_dec(v_h__1_448_);
            v___x_463_ = leanh::lean_box(0);
            v___x_464_ = leanh::lean_apply_1(v_h__5_452_, v___x_463_);
            return v___x_464_;
        }
        5 => {
            let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_454_);
            leanh::lean_dec(v_h__5_452_);
            leanh::lean_dec(v_h__4_451_);
            leanh::lean_dec(v_h__3_450_);
            leanh::lean_dec(v_h__2_449_);
            leanh::lean_dec(v_h__1_448_);
            v___x_465_ = leanh::lean_box(0);
            v___x_466_ = leanh::lean_apply_1(v_h__6_453_, v___x_465_);
            return v___x_466_;
        }
        _ => {
            let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__6_453_);
            leanh::lean_dec(v_h__5_452_);
            leanh::lean_dec(v_h__4_451_);
            leanh::lean_dec(v_h__3_450_);
            leanh::lean_dec(v_h__2_449_);
            leanh::lean_dec(v_h__1_448_);
            v___x_467_ = leanh::lean_box(0);
            v___x_468_ = leanh::lean_apply_1(v_h__7_454_, v___x_467_);
            return v___x_468_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg___boxed(
    mut v_op_469_: *mut leanh::LeanObject,
    mut v_h__1_470_: *mut leanh::LeanObject,
    mut v_h__2_471_: *mut leanh::LeanObject,
    mut v_h__3_472_: *mut leanh::LeanObject,
    mut v_h__4_473_: *mut leanh::LeanObject,
    mut v_h__5_474_: *mut leanh::LeanObject,
    mut v_h__6_475_: *mut leanh::LeanObject,
    mut v_h__7_476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_op_76__boxed_477_: u8 = 0;
    let mut v_res_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_op_76__boxed_477_ = (leanh::lean_unbox(v_op_469_) as u8);
    v_res_478_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg(v_op_76__boxed_477_, v_h__1_470_, v_h__2_471_, v_h__3_472_, v_h__4_473_, v_h__5_474_, v_h__6_475_, v_h__7_476_);
    return v_res_478_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter(
    mut v_motive_479_: *mut leanh::LeanObject,
    mut v_op_480_: u8,
    mut v_h__1_481_: *mut leanh::LeanObject,
    mut v_h__2_482_: *mut leanh::LeanObject,
    mut v_h__3_483_: *mut leanh::LeanObject,
    mut v_h__4_484_: *mut leanh::LeanObject,
    mut v_h__5_485_: *mut leanh::LeanObject,
    mut v_h__6_486_: *mut leanh::LeanObject,
    mut v_h__7_487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_op_480_ {
        0 => {
            let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_487_);
            leanh::lean_dec(v_h__6_486_);
            leanh::lean_dec(v_h__5_485_);
            leanh::lean_dec(v_h__4_484_);
            leanh::lean_dec(v_h__3_483_);
            leanh::lean_dec(v_h__2_482_);
            v___x_488_ = leanh::lean_box(0);
            v___x_489_ = leanh::lean_apply_1(v_h__1_481_, v___x_488_);
            return v___x_489_;
        }
        1 => {
            let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_487_);
            leanh::lean_dec(v_h__6_486_);
            leanh::lean_dec(v_h__5_485_);
            leanh::lean_dec(v_h__4_484_);
            leanh::lean_dec(v_h__3_483_);
            leanh::lean_dec(v_h__1_481_);
            v___x_490_ = leanh::lean_box(0);
            v___x_491_ = leanh::lean_apply_1(v_h__2_482_, v___x_490_);
            return v___x_491_;
        }
        2 => {
            let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_487_);
            leanh::lean_dec(v_h__6_486_);
            leanh::lean_dec(v_h__5_485_);
            leanh::lean_dec(v_h__4_484_);
            leanh::lean_dec(v_h__2_482_);
            leanh::lean_dec(v_h__1_481_);
            v___x_492_ = leanh::lean_box(0);
            v___x_493_ = leanh::lean_apply_1(v_h__3_483_, v___x_492_);
            return v___x_493_;
        }
        3 => {
            let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_487_);
            leanh::lean_dec(v_h__6_486_);
            leanh::lean_dec(v_h__5_485_);
            leanh::lean_dec(v_h__3_483_);
            leanh::lean_dec(v_h__2_482_);
            leanh::lean_dec(v_h__1_481_);
            v___x_494_ = leanh::lean_box(0);
            v___x_495_ = leanh::lean_apply_1(v_h__4_484_, v___x_494_);
            return v___x_495_;
        }
        4 => {
            let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_487_);
            leanh::lean_dec(v_h__6_486_);
            leanh::lean_dec(v_h__4_484_);
            leanh::lean_dec(v_h__3_483_);
            leanh::lean_dec(v_h__2_482_);
            leanh::lean_dec(v_h__1_481_);
            v___x_496_ = leanh::lean_box(0);
            v___x_497_ = leanh::lean_apply_1(v_h__5_485_, v___x_496_);
            return v___x_497_;
        }
        5 => {
            let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_487_);
            leanh::lean_dec(v_h__5_485_);
            leanh::lean_dec(v_h__4_484_);
            leanh::lean_dec(v_h__3_483_);
            leanh::lean_dec(v_h__2_482_);
            leanh::lean_dec(v_h__1_481_);
            v___x_498_ = leanh::lean_box(0);
            v___x_499_ = leanh::lean_apply_1(v_h__6_486_, v___x_498_);
            return v___x_499_;
        }
        _ => {
            let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__6_486_);
            leanh::lean_dec(v_h__5_485_);
            leanh::lean_dec(v_h__4_484_);
            leanh::lean_dec(v_h__3_483_);
            leanh::lean_dec(v_h__2_482_);
            leanh::lean_dec(v_h__1_481_);
            v___x_500_ = leanh::lean_box(0);
            v___x_501_ = leanh::lean_apply_1(v_h__7_487_, v___x_500_);
            return v___x_501_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___boxed(
    mut v_motive_502_: *mut leanh::LeanObject,
    mut v_op_503_: *mut leanh::LeanObject,
    mut v_h__1_504_: *mut leanh::LeanObject,
    mut v_h__2_505_: *mut leanh::LeanObject,
    mut v_h__3_506_: *mut leanh::LeanObject,
    mut v_h__4_507_: *mut leanh::LeanObject,
    mut v_h__5_508_: *mut leanh::LeanObject,
    mut v_h__6_509_: *mut leanh::LeanObject,
    mut v_h__7_510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_op_107__boxed_511_: u8 = 0;
    let mut v_res_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_op_107__boxed_511_ = (leanh::lean_unbox(v_op_503_) as u8);
    v_res_512_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter(v_motive_502_, v_op_107__boxed_511_, v_h__1_504_, v_h__2_505_, v_h__3_506_, v_h__4_507_, v_h__5_508_, v_h__6_509_, v_h__7_510_);
    return v_res_512_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Var(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_ShiftRight(
            builtin,
        );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Append(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Replicate(
            builtin,
        );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Extract(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateLeft(
            builtin,
        );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateRight(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Mul(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Reverse(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Clz(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Cpop(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Var(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_ShiftRight(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Append(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res =
        initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Replicate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Extract(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateLeft(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateRight(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Mul(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Reverse(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Clz(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Cpop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(builtin);
}