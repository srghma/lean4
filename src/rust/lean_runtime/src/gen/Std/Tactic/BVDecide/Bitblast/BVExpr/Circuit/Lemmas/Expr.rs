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
    mut v_x_257_: *mut crate::leanh::LeanObject,
    mut v_h__1_258_: *mut crate::leanh::LeanObject,
    mut v_h__2_259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_257_) == 0 {
        let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_258_);
        v___x_260_ = crate::leanh::lean_apply_1(v_h__2_259_, crate::leanh::lean_box(0));
        return v___x_260_;
    } else {
        let mut v_val_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_259_);
        v_val_261_ = crate::leanh::lean_ctor_get(v_x_257_, 0);
        crate::leanh::lean_inc(v_val_261_);
        crate::leanh::lean_dec_ref_known(v_x_257_, 1);
        v___x_262_ = crate::leanh::lean_apply_2(v_h__1_258_, v_val_261_, crate::leanh::lean_box(0));
        return v___x_262_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter(
    mut v_w_263_: *mut crate::leanh::LeanObject,
    mut v_expr_264_: *mut crate::leanh::LeanObject,
    mut v_motive_265_: *mut crate::leanh::LeanObject,
    mut v_x_266_: *mut crate::leanh::LeanObject,
    mut v_h__1_267_: *mut crate::leanh::LeanObject,
    mut v_h__2_268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_266_) == 0 {
        let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_267_);
        v___x_269_ = crate::leanh::lean_apply_1(v_h__2_268_, crate::leanh::lean_box(0));
        return v___x_269_;
    } else {
        let mut v_val_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_268_);
        v_val_270_ = crate::leanh::lean_ctor_get(v_x_266_, 0);
        crate::leanh::lean_inc(v_val_270_);
        crate::leanh::lean_dec_ref_known(v_x_266_, 1);
        v___x_271_ = crate::leanh::lean_apply_2(v_h__1_267_, v_val_270_, crate::leanh::lean_box(0));
        return v___x_271_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter___boxed(
    mut v_w_272_: *mut crate::leanh::LeanObject,
    mut v_expr_273_: *mut crate::leanh::LeanObject,
    mut v_motive_274_: *mut crate::leanh::LeanObject,
    mut v_x_275_: *mut crate::leanh::LeanObject,
    mut v_h__1_276_: *mut crate::leanh::LeanObject,
    mut v_h__2_277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_278_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter(v_w_272_, v_expr_273_, v_motive_274_, v_x_275_, v_h__1_276_, v_h__2_277_);
    crate::leanh::lean_dec_ref(v_expr_273_);
    crate::leanh::lean_dec(v_w_272_);
    return v_res_278_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter___redArg(
    mut v_x_279_: *mut crate::leanh::LeanObject,
    mut v_h__1_280_: *mut crate::leanh::LeanObject,
    mut v_h__2_281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_279_) == 0 {
        let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_280_);
        v___x_282_ = crate::leanh::lean_box(0);
        v___x_283_ = crate::leanh::lean_apply_1(v_h__2_281_, v___x_282_);
        return v___x_283_;
    } else {
        let mut v_val_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_281_);
        v_val_284_ = crate::leanh::lean_ctor_get(v_x_279_, 0);
        crate::leanh::lean_inc(v_val_284_);
        crate::leanh::lean_dec_ref_known(v_x_279_, 1);
        v___x_285_ = crate::leanh::lean_apply_1(v_h__1_280_, v_val_284_);
        return v___x_285_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter(
    mut v_w_286_: *mut crate::leanh::LeanObject,
    mut v_aig_287_: *mut crate::leanh::LeanObject,
    mut v_motive_288_: *mut crate::leanh::LeanObject,
    mut v_x_289_: *mut crate::leanh::LeanObject,
    mut v_h__1_290_: *mut crate::leanh::LeanObject,
    mut v_h__2_291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_289_) == 0 {
        let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_290_);
        v___x_292_ = crate::leanh::lean_box(0);
        v___x_293_ = crate::leanh::lean_apply_1(v_h__2_291_, v___x_292_);
        return v___x_293_;
    } else {
        let mut v_val_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_291_);
        v_val_294_ = crate::leanh::lean_ctor_get(v_x_289_, 0);
        crate::leanh::lean_inc(v_val_294_);
        crate::leanh::lean_dec_ref_known(v_x_289_, 1);
        v___x_295_ = crate::leanh::lean_apply_1(v_h__1_290_, v_val_294_);
        return v___x_295_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter___boxed(
    mut v_w_296_: *mut crate::leanh::LeanObject,
    mut v_aig_297_: *mut crate::leanh::LeanObject,
    mut v_motive_298_: *mut crate::leanh::LeanObject,
    mut v_x_299_: *mut crate::leanh::LeanObject,
    mut v_h__1_300_: *mut crate::leanh::LeanObject,
    mut v_h__2_301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_302_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter(v_w_296_, v_aig_297_, v_motive_298_, v_x_299_, v_h__1_300_, v_h__2_301_);
    crate::leanh::lean_dec_ref(v_aig_297_);
    crate::leanh::lean_dec(v_w_296_);
    return v_res_302_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__17_splitter___redArg(
    mut v_w_303_: *mut crate::leanh::LeanObject,
    mut v_expr_304_: *mut crate::leanh::LeanObject,
    mut v_h__1_305_: *mut crate::leanh::LeanObject,
    mut v_h__2_306_: *mut crate::leanh::LeanObject,
    mut v_h__3_307_: *mut crate::leanh::LeanObject,
    mut v_h__4_308_: *mut crate::leanh::LeanObject,
    mut v_h__5_309_: *mut crate::leanh::LeanObject,
    mut v_h__6_310_: *mut crate::leanh::LeanObject,
    mut v_h__7_311_: *mut crate::leanh::LeanObject,
    mut v_h__8_312_: *mut crate::leanh::LeanObject,
    mut v_h__9_313_: *mut crate::leanh::LeanObject,
    mut v_h__10_314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_expr_304_) {
        0 => {
            let mut v_idx_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_314_);
            crate::leanh::lean_dec(v_h__9_313_);
            crate::leanh::lean_dec(v_h__8_312_);
            crate::leanh::lean_dec(v_h__7_311_);
            crate::leanh::lean_dec(v_h__6_310_);
            crate::leanh::lean_dec(v_h__5_309_);
            crate::leanh::lean_dec(v_h__4_308_);
            crate::leanh::lean_dec(v_h__3_307_);
            crate::leanh::lean_dec(v_h__2_306_);
            v_idx_315_ = crate::leanh::lean_ctor_get(v_expr_304_, 1);
            crate::leanh::lean_inc(v_idx_315_);
            crate::leanh::lean_dec_ref_known(v_expr_304_, 2);
            v___x_316_ = crate::leanh::lean_apply_2(v_h__1_305_, v_w_303_, v_idx_315_);
            return v___x_316_;
        }
        1 => {
            let mut v_val_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_314_);
            crate::leanh::lean_dec(v_h__9_313_);
            crate::leanh::lean_dec(v_h__8_312_);
            crate::leanh::lean_dec(v_h__7_311_);
            crate::leanh::lean_dec(v_h__6_310_);
            crate::leanh::lean_dec(v_h__5_309_);
            crate::leanh::lean_dec(v_h__4_308_);
            crate::leanh::lean_dec(v_h__3_307_);
            crate::leanh::lean_dec(v_h__1_305_);
            v_val_317_ = crate::leanh::lean_ctor_get(v_expr_304_, 1);
            crate::leanh::lean_inc(v_val_317_);
            crate::leanh::lean_dec_ref_known(v_expr_304_, 2);
            v___x_318_ = crate::leanh::lean_apply_2(v_h__2_306_, v_w_303_, v_val_317_);
            return v___x_318_;
        }
        2 => {
            let mut v_w_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_start_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_314_);
            crate::leanh::lean_dec(v_h__9_313_);
            crate::leanh::lean_dec(v_h__8_312_);
            crate::leanh::lean_dec(v_h__6_310_);
            crate::leanh::lean_dec(v_h__5_309_);
            crate::leanh::lean_dec(v_h__4_308_);
            crate::leanh::lean_dec(v_h__3_307_);
            crate::leanh::lean_dec(v_h__2_306_);
            crate::leanh::lean_dec(v_h__1_305_);
            v_w_319_ = crate::leanh::lean_ctor_get(v_expr_304_, 0);
            crate::leanh::lean_inc(v_w_319_);
            v_start_320_ = crate::leanh::lean_ctor_get(v_expr_304_, 1);
            crate::leanh::lean_inc(v_start_320_);
            v_expr_321_ = crate::leanh::lean_ctor_get(v_expr_304_, 3);
            crate::leanh::lean_inc_ref(v_expr_321_);
            crate::leanh::lean_dec_ref_known(v_expr_304_, 4);
            v___x_322_ = crate::leanh::lean_apply_4(
                v_h__7_311_,
                v_w_303_,
                v_w_319_,
                v_start_320_,
                v_expr_321_,
            );
            return v___x_322_;
        }
        3 => {
            let mut v_lhs_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_op_324_: u8 = 0;
            let mut v_rhs_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_314_);
            crate::leanh::lean_dec(v_h__9_313_);
            crate::leanh::lean_dec(v_h__8_312_);
            crate::leanh::lean_dec(v_h__7_311_);
            crate::leanh::lean_dec(v_h__6_310_);
            crate::leanh::lean_dec(v_h__5_309_);
            crate::leanh::lean_dec(v_h__4_308_);
            crate::leanh::lean_dec(v_h__2_306_);
            crate::leanh::lean_dec(v_h__1_305_);
            v_lhs_323_ = crate::leanh::lean_ctor_get(v_expr_304_, 1);
            crate::leanh::lean_inc_ref(v_lhs_323_);
            v_op_324_ = crate::leanh::lean_ctor_get_uint8(
                v_expr_304_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
            );
            v_rhs_325_ = crate::leanh::lean_ctor_get(v_expr_304_, 2);
            crate::leanh::lean_inc_ref(v_rhs_325_);
            crate::leanh::lean_dec_ref_known(v_expr_304_, 3);
            v___x_326_ = crate::leanh::lean_box((v_op_324_) as usize);
            v___x_327_ = crate::leanh::lean_apply_4(
                v_h__3_307_,
                v_w_303_,
                v_lhs_323_,
                v___x_326_,
                v_rhs_325_,
            );
            return v___x_327_;
        }
        4 => {
            let mut v_op_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_operand_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_314_);
            crate::leanh::lean_dec(v_h__9_313_);
            crate::leanh::lean_dec(v_h__8_312_);
            crate::leanh::lean_dec(v_h__7_311_);
            crate::leanh::lean_dec(v_h__6_310_);
            crate::leanh::lean_dec(v_h__5_309_);
            crate::leanh::lean_dec(v_h__3_307_);
            crate::leanh::lean_dec(v_h__2_306_);
            crate::leanh::lean_dec(v_h__1_305_);
            v_op_328_ = crate::leanh::lean_ctor_get(v_expr_304_, 1);
            crate::leanh::lean_inc(v_op_328_);
            v_operand_329_ = crate::leanh::lean_ctor_get(v_expr_304_, 2);
            crate::leanh::lean_inc_ref(v_operand_329_);
            crate::leanh::lean_dec_ref_known(v_expr_304_, 3);
            v___x_330_ =
                crate::leanh::lean_apply_3(v_h__4_308_, v_w_303_, v_op_328_, v_operand_329_);
            return v___x_330_;
        }
        5 => {
            let mut v_l_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_314_);
            crate::leanh::lean_dec(v_h__9_313_);
            crate::leanh::lean_dec(v_h__8_312_);
            crate::leanh::lean_dec(v_h__7_311_);
            crate::leanh::lean_dec(v_h__6_310_);
            crate::leanh::lean_dec(v_h__4_308_);
            crate::leanh::lean_dec(v_h__3_307_);
            crate::leanh::lean_dec(v_h__2_306_);
            crate::leanh::lean_dec(v_h__1_305_);
            v_l_331_ = crate::leanh::lean_ctor_get(v_expr_304_, 0);
            crate::leanh::lean_inc(v_l_331_);
            v_r_332_ = crate::leanh::lean_ctor_get(v_expr_304_, 1);
            crate::leanh::lean_inc(v_r_332_);
            v_lhs_333_ = crate::leanh::lean_ctor_get(v_expr_304_, 3);
            crate::leanh::lean_inc_ref(v_lhs_333_);
            v_rhs_334_ = crate::leanh::lean_ctor_get(v_expr_304_, 4);
            crate::leanh::lean_inc_ref(v_rhs_334_);
            crate::leanh::lean_dec_ref_known(v_expr_304_, 5);
            v___x_335_ = crate::leanh::lean_apply_6(
                v_h__5_309_,
                v_w_303_,
                v_l_331_,
                v_r_332_,
                v_lhs_333_,
                v_rhs_334_,
                crate::leanh::lean_box(0),
            );
            return v___x_335_;
        }
        6 => {
            let mut v_w_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_314_);
            crate::leanh::lean_dec(v_h__9_313_);
            crate::leanh::lean_dec(v_h__8_312_);
            crate::leanh::lean_dec(v_h__7_311_);
            crate::leanh::lean_dec(v_h__5_309_);
            crate::leanh::lean_dec(v_h__4_308_);
            crate::leanh::lean_dec(v_h__3_307_);
            crate::leanh::lean_dec(v_h__2_306_);
            crate::leanh::lean_dec(v_h__1_305_);
            v_w_336_ = crate::leanh::lean_ctor_get(v_expr_304_, 0);
            crate::leanh::lean_inc(v_w_336_);
            v_n_337_ = crate::leanh::lean_ctor_get(v_expr_304_, 2);
            crate::leanh::lean_inc(v_n_337_);
            v_expr_338_ = crate::leanh::lean_ctor_get(v_expr_304_, 3);
            crate::leanh::lean_inc_ref(v_expr_338_);
            crate::leanh::lean_dec_ref_known(v_expr_304_, 4);
            v___x_339_ = crate::leanh::lean_apply_5(
                v_h__6_310_,
                v_w_303_,
                v_w_336_,
                v_n_337_,
                v_expr_338_,
                crate::leanh::lean_box(0),
            );
            return v___x_339_;
        }
        7 => {
            let mut v_n_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_314_);
            crate::leanh::lean_dec(v_h__9_313_);
            crate::leanh::lean_dec(v_h__7_311_);
            crate::leanh::lean_dec(v_h__6_310_);
            crate::leanh::lean_dec(v_h__5_309_);
            crate::leanh::lean_dec(v_h__4_308_);
            crate::leanh::lean_dec(v_h__3_307_);
            crate::leanh::lean_dec(v_h__2_306_);
            crate::leanh::lean_dec(v_h__1_305_);
            v_n_340_ = crate::leanh::lean_ctor_get(v_expr_304_, 1);
            crate::leanh::lean_inc(v_n_340_);
            v_lhs_341_ = crate::leanh::lean_ctor_get(v_expr_304_, 2);
            crate::leanh::lean_inc_ref(v_lhs_341_);
            v_rhs_342_ = crate::leanh::lean_ctor_get(v_expr_304_, 3);
            crate::leanh::lean_inc_ref(v_rhs_342_);
            crate::leanh::lean_dec_ref_known(v_expr_304_, 4);
            v___x_343_ =
                crate::leanh::lean_apply_4(v_h__8_312_, v_w_303_, v_n_340_, v_lhs_341_, v_rhs_342_);
            return v___x_343_;
        }
        8 => {
            let mut v_n_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_314_);
            crate::leanh::lean_dec(v_h__8_312_);
            crate::leanh::lean_dec(v_h__7_311_);
            crate::leanh::lean_dec(v_h__6_310_);
            crate::leanh::lean_dec(v_h__5_309_);
            crate::leanh::lean_dec(v_h__4_308_);
            crate::leanh::lean_dec(v_h__3_307_);
            crate::leanh::lean_dec(v_h__2_306_);
            crate::leanh::lean_dec(v_h__1_305_);
            v_n_344_ = crate::leanh::lean_ctor_get(v_expr_304_, 1);
            crate::leanh::lean_inc(v_n_344_);
            v_lhs_345_ = crate::leanh::lean_ctor_get(v_expr_304_, 2);
            crate::leanh::lean_inc_ref(v_lhs_345_);
            v_rhs_346_ = crate::leanh::lean_ctor_get(v_expr_304_, 3);
            crate::leanh::lean_inc_ref(v_rhs_346_);
            crate::leanh::lean_dec_ref_known(v_expr_304_, 4);
            v___x_347_ =
                crate::leanh::lean_apply_4(v_h__9_313_, v_w_303_, v_n_344_, v_lhs_345_, v_rhs_346_);
            return v___x_347_;
        }
        _ => {
            let mut v_n_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_313_);
            crate::leanh::lean_dec(v_h__8_312_);
            crate::leanh::lean_dec(v_h__7_311_);
            crate::leanh::lean_dec(v_h__6_310_);
            crate::leanh::lean_dec(v_h__5_309_);
            crate::leanh::lean_dec(v_h__4_308_);
            crate::leanh::lean_dec(v_h__3_307_);
            crate::leanh::lean_dec(v_h__2_306_);
            crate::leanh::lean_dec(v_h__1_305_);
            v_n_348_ = crate::leanh::lean_ctor_get(v_expr_304_, 1);
            crate::leanh::lean_inc(v_n_348_);
            v_lhs_349_ = crate::leanh::lean_ctor_get(v_expr_304_, 2);
            crate::leanh::lean_inc_ref(v_lhs_349_);
            v_rhs_350_ = crate::leanh::lean_ctor_get(v_expr_304_, 3);
            crate::leanh::lean_inc_ref(v_rhs_350_);
            crate::leanh::lean_dec_ref_known(v_expr_304_, 4);
            v___x_351_ = crate::leanh::lean_apply_4(
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
    mut v_motive_352_: *mut crate::leanh::LeanObject,
    mut v_w_353_: *mut crate::leanh::LeanObject,
    mut v_expr_354_: *mut crate::leanh::LeanObject,
    mut v_h__1_355_: *mut crate::leanh::LeanObject,
    mut v_h__2_356_: *mut crate::leanh::LeanObject,
    mut v_h__3_357_: *mut crate::leanh::LeanObject,
    mut v_h__4_358_: *mut crate::leanh::LeanObject,
    mut v_h__5_359_: *mut crate::leanh::LeanObject,
    mut v_h__6_360_: *mut crate::leanh::LeanObject,
    mut v_h__7_361_: *mut crate::leanh::LeanObject,
    mut v_h__8_362_: *mut crate::leanh::LeanObject,
    mut v_h__9_363_: *mut crate::leanh::LeanObject,
    mut v_h__10_364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_expr_354_) {
        0 => {
            let mut v_idx_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_364_);
            crate::leanh::lean_dec(v_h__9_363_);
            crate::leanh::lean_dec(v_h__8_362_);
            crate::leanh::lean_dec(v_h__7_361_);
            crate::leanh::lean_dec(v_h__6_360_);
            crate::leanh::lean_dec(v_h__5_359_);
            crate::leanh::lean_dec(v_h__4_358_);
            crate::leanh::lean_dec(v_h__3_357_);
            crate::leanh::lean_dec(v_h__2_356_);
            v_idx_365_ = crate::leanh::lean_ctor_get(v_expr_354_, 1);
            crate::leanh::lean_inc(v_idx_365_);
            crate::leanh::lean_dec_ref_known(v_expr_354_, 2);
            v___x_366_ = crate::leanh::lean_apply_2(v_h__1_355_, v_w_353_, v_idx_365_);
            return v___x_366_;
        }
        1 => {
            let mut v_val_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_364_);
            crate::leanh::lean_dec(v_h__9_363_);
            crate::leanh::lean_dec(v_h__8_362_);
            crate::leanh::lean_dec(v_h__7_361_);
            crate::leanh::lean_dec(v_h__6_360_);
            crate::leanh::lean_dec(v_h__5_359_);
            crate::leanh::lean_dec(v_h__4_358_);
            crate::leanh::lean_dec(v_h__3_357_);
            crate::leanh::lean_dec(v_h__1_355_);
            v_val_367_ = crate::leanh::lean_ctor_get(v_expr_354_, 1);
            crate::leanh::lean_inc(v_val_367_);
            crate::leanh::lean_dec_ref_known(v_expr_354_, 2);
            v___x_368_ = crate::leanh::lean_apply_2(v_h__2_356_, v_w_353_, v_val_367_);
            return v___x_368_;
        }
        2 => {
            let mut v_w_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_start_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_364_);
            crate::leanh::lean_dec(v_h__9_363_);
            crate::leanh::lean_dec(v_h__8_362_);
            crate::leanh::lean_dec(v_h__6_360_);
            crate::leanh::lean_dec(v_h__5_359_);
            crate::leanh::lean_dec(v_h__4_358_);
            crate::leanh::lean_dec(v_h__3_357_);
            crate::leanh::lean_dec(v_h__2_356_);
            crate::leanh::lean_dec(v_h__1_355_);
            v_w_369_ = crate::leanh::lean_ctor_get(v_expr_354_, 0);
            crate::leanh::lean_inc(v_w_369_);
            v_start_370_ = crate::leanh::lean_ctor_get(v_expr_354_, 1);
            crate::leanh::lean_inc(v_start_370_);
            v_expr_371_ = crate::leanh::lean_ctor_get(v_expr_354_, 3);
            crate::leanh::lean_inc_ref(v_expr_371_);
            crate::leanh::lean_dec_ref_known(v_expr_354_, 4);
            v___x_372_ = crate::leanh::lean_apply_4(
                v_h__7_361_,
                v_w_353_,
                v_w_369_,
                v_start_370_,
                v_expr_371_,
            );
            return v___x_372_;
        }
        3 => {
            let mut v_lhs_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_op_374_: u8 = 0;
            let mut v_rhs_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_364_);
            crate::leanh::lean_dec(v_h__9_363_);
            crate::leanh::lean_dec(v_h__8_362_);
            crate::leanh::lean_dec(v_h__7_361_);
            crate::leanh::lean_dec(v_h__6_360_);
            crate::leanh::lean_dec(v_h__5_359_);
            crate::leanh::lean_dec(v_h__4_358_);
            crate::leanh::lean_dec(v_h__2_356_);
            crate::leanh::lean_dec(v_h__1_355_);
            v_lhs_373_ = crate::leanh::lean_ctor_get(v_expr_354_, 1);
            crate::leanh::lean_inc_ref(v_lhs_373_);
            v_op_374_ = crate::leanh::lean_ctor_get_uint8(
                v_expr_354_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
            );
            v_rhs_375_ = crate::leanh::lean_ctor_get(v_expr_354_, 2);
            crate::leanh::lean_inc_ref(v_rhs_375_);
            crate::leanh::lean_dec_ref_known(v_expr_354_, 3);
            v___x_376_ = crate::leanh::lean_box((v_op_374_) as usize);
            v___x_377_ = crate::leanh::lean_apply_4(
                v_h__3_357_,
                v_w_353_,
                v_lhs_373_,
                v___x_376_,
                v_rhs_375_,
            );
            return v___x_377_;
        }
        4 => {
            let mut v_op_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_operand_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_364_);
            crate::leanh::lean_dec(v_h__9_363_);
            crate::leanh::lean_dec(v_h__8_362_);
            crate::leanh::lean_dec(v_h__7_361_);
            crate::leanh::lean_dec(v_h__6_360_);
            crate::leanh::lean_dec(v_h__5_359_);
            crate::leanh::lean_dec(v_h__3_357_);
            crate::leanh::lean_dec(v_h__2_356_);
            crate::leanh::lean_dec(v_h__1_355_);
            v_op_378_ = crate::leanh::lean_ctor_get(v_expr_354_, 1);
            crate::leanh::lean_inc(v_op_378_);
            v_operand_379_ = crate::leanh::lean_ctor_get(v_expr_354_, 2);
            crate::leanh::lean_inc_ref(v_operand_379_);
            crate::leanh::lean_dec_ref_known(v_expr_354_, 3);
            v___x_380_ =
                crate::leanh::lean_apply_3(v_h__4_358_, v_w_353_, v_op_378_, v_operand_379_);
            return v___x_380_;
        }
        5 => {
            let mut v_l_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_364_);
            crate::leanh::lean_dec(v_h__9_363_);
            crate::leanh::lean_dec(v_h__8_362_);
            crate::leanh::lean_dec(v_h__7_361_);
            crate::leanh::lean_dec(v_h__6_360_);
            crate::leanh::lean_dec(v_h__4_358_);
            crate::leanh::lean_dec(v_h__3_357_);
            crate::leanh::lean_dec(v_h__2_356_);
            crate::leanh::lean_dec(v_h__1_355_);
            v_l_381_ = crate::leanh::lean_ctor_get(v_expr_354_, 0);
            crate::leanh::lean_inc(v_l_381_);
            v_r_382_ = crate::leanh::lean_ctor_get(v_expr_354_, 1);
            crate::leanh::lean_inc(v_r_382_);
            v_lhs_383_ = crate::leanh::lean_ctor_get(v_expr_354_, 3);
            crate::leanh::lean_inc_ref(v_lhs_383_);
            v_rhs_384_ = crate::leanh::lean_ctor_get(v_expr_354_, 4);
            crate::leanh::lean_inc_ref(v_rhs_384_);
            crate::leanh::lean_dec_ref_known(v_expr_354_, 5);
            v___x_385_ = crate::leanh::lean_apply_6(
                v_h__5_359_,
                v_w_353_,
                v_l_381_,
                v_r_382_,
                v_lhs_383_,
                v_rhs_384_,
                crate::leanh::lean_box(0),
            );
            return v___x_385_;
        }
        6 => {
            let mut v_w_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_364_);
            crate::leanh::lean_dec(v_h__9_363_);
            crate::leanh::lean_dec(v_h__8_362_);
            crate::leanh::lean_dec(v_h__7_361_);
            crate::leanh::lean_dec(v_h__5_359_);
            crate::leanh::lean_dec(v_h__4_358_);
            crate::leanh::lean_dec(v_h__3_357_);
            crate::leanh::lean_dec(v_h__2_356_);
            crate::leanh::lean_dec(v_h__1_355_);
            v_w_386_ = crate::leanh::lean_ctor_get(v_expr_354_, 0);
            crate::leanh::lean_inc(v_w_386_);
            v_n_387_ = crate::leanh::lean_ctor_get(v_expr_354_, 2);
            crate::leanh::lean_inc(v_n_387_);
            v_expr_388_ = crate::leanh::lean_ctor_get(v_expr_354_, 3);
            crate::leanh::lean_inc_ref(v_expr_388_);
            crate::leanh::lean_dec_ref_known(v_expr_354_, 4);
            v___x_389_ = crate::leanh::lean_apply_5(
                v_h__6_360_,
                v_w_353_,
                v_w_386_,
                v_n_387_,
                v_expr_388_,
                crate::leanh::lean_box(0),
            );
            return v___x_389_;
        }
        7 => {
            let mut v_n_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_364_);
            crate::leanh::lean_dec(v_h__9_363_);
            crate::leanh::lean_dec(v_h__7_361_);
            crate::leanh::lean_dec(v_h__6_360_);
            crate::leanh::lean_dec(v_h__5_359_);
            crate::leanh::lean_dec(v_h__4_358_);
            crate::leanh::lean_dec(v_h__3_357_);
            crate::leanh::lean_dec(v_h__2_356_);
            crate::leanh::lean_dec(v_h__1_355_);
            v_n_390_ = crate::leanh::lean_ctor_get(v_expr_354_, 1);
            crate::leanh::lean_inc(v_n_390_);
            v_lhs_391_ = crate::leanh::lean_ctor_get(v_expr_354_, 2);
            crate::leanh::lean_inc_ref(v_lhs_391_);
            v_rhs_392_ = crate::leanh::lean_ctor_get(v_expr_354_, 3);
            crate::leanh::lean_inc_ref(v_rhs_392_);
            crate::leanh::lean_dec_ref_known(v_expr_354_, 4);
            v___x_393_ =
                crate::leanh::lean_apply_4(v_h__8_362_, v_w_353_, v_n_390_, v_lhs_391_, v_rhs_392_);
            return v___x_393_;
        }
        8 => {
            let mut v_n_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__10_364_);
            crate::leanh::lean_dec(v_h__8_362_);
            crate::leanh::lean_dec(v_h__7_361_);
            crate::leanh::lean_dec(v_h__6_360_);
            crate::leanh::lean_dec(v_h__5_359_);
            crate::leanh::lean_dec(v_h__4_358_);
            crate::leanh::lean_dec(v_h__3_357_);
            crate::leanh::lean_dec(v_h__2_356_);
            crate::leanh::lean_dec(v_h__1_355_);
            v_n_394_ = crate::leanh::lean_ctor_get(v_expr_354_, 1);
            crate::leanh::lean_inc(v_n_394_);
            v_lhs_395_ = crate::leanh::lean_ctor_get(v_expr_354_, 2);
            crate::leanh::lean_inc_ref(v_lhs_395_);
            v_rhs_396_ = crate::leanh::lean_ctor_get(v_expr_354_, 3);
            crate::leanh::lean_inc_ref(v_rhs_396_);
            crate::leanh::lean_dec_ref_known(v_expr_354_, 4);
            v___x_397_ =
                crate::leanh::lean_apply_4(v_h__9_363_, v_w_353_, v_n_394_, v_lhs_395_, v_rhs_396_);
            return v___x_397_;
        }
        _ => {
            let mut v_n_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_363_);
            crate::leanh::lean_dec(v_h__8_362_);
            crate::leanh::lean_dec(v_h__7_361_);
            crate::leanh::lean_dec(v_h__6_360_);
            crate::leanh::lean_dec(v_h__5_359_);
            crate::leanh::lean_dec(v_h__4_358_);
            crate::leanh::lean_dec(v_h__3_357_);
            crate::leanh::lean_dec(v_h__2_356_);
            crate::leanh::lean_dec(v_h__1_355_);
            v_n_398_ = crate::leanh::lean_ctor_get(v_expr_354_, 1);
            crate::leanh::lean_inc(v_n_398_);
            v_lhs_399_ = crate::leanh::lean_ctor_get(v_expr_354_, 2);
            crate::leanh::lean_inc_ref(v_lhs_399_);
            v_rhs_400_ = crate::leanh::lean_ctor_get(v_expr_354_, 3);
            crate::leanh::lean_inc_ref(v_rhs_400_);
            crate::leanh::lean_dec_ref_known(v_expr_354_, 4);
            v___x_401_ = crate::leanh::lean_apply_4(
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
    mut v_op_402_: *mut crate::leanh::LeanObject,
    mut v_h__1_403_: *mut crate::leanh::LeanObject,
    mut v_h__2_404_: *mut crate::leanh::LeanObject,
    mut v_h__3_405_: *mut crate::leanh::LeanObject,
    mut v_h__4_406_: *mut crate::leanh::LeanObject,
    mut v_h__5_407_: *mut crate::leanh::LeanObject,
    mut v_h__6_408_: *mut crate::leanh::LeanObject,
    mut v_h__7_409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_op_402_) {
        0 => {
            let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_409_);
            crate::leanh::lean_dec(v_h__6_408_);
            crate::leanh::lean_dec(v_h__5_407_);
            crate::leanh::lean_dec(v_h__4_406_);
            crate::leanh::lean_dec(v_h__3_405_);
            crate::leanh::lean_dec(v_h__2_404_);
            v___x_410_ = crate::leanh::lean_box(0);
            v___x_411_ = crate::leanh::lean_apply_1(v_h__1_403_, v___x_410_);
            return v___x_411_;
        }
        1 => {
            let mut v_n_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_409_);
            crate::leanh::lean_dec(v_h__6_408_);
            crate::leanh::lean_dec(v_h__5_407_);
            crate::leanh::lean_dec(v_h__4_406_);
            crate::leanh::lean_dec(v_h__3_405_);
            crate::leanh::lean_dec(v_h__1_403_);
            v_n_412_ = crate::leanh::lean_ctor_get(v_op_402_, 0);
            crate::leanh::lean_inc(v_n_412_);
            crate::leanh::lean_dec_ref_known(v_op_402_, 1);
            v___x_413_ = crate::leanh::lean_apply_1(v_h__2_404_, v_n_412_);
            return v___x_413_;
        }
        2 => {
            let mut v_n_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_409_);
            crate::leanh::lean_dec(v_h__6_408_);
            crate::leanh::lean_dec(v_h__5_407_);
            crate::leanh::lean_dec(v_h__4_406_);
            crate::leanh::lean_dec(v_h__2_404_);
            crate::leanh::lean_dec(v_h__1_403_);
            v_n_414_ = crate::leanh::lean_ctor_get(v_op_402_, 0);
            crate::leanh::lean_inc(v_n_414_);
            crate::leanh::lean_dec_ref_known(v_op_402_, 1);
            v___x_415_ = crate::leanh::lean_apply_1(v_h__3_405_, v_n_414_);
            return v___x_415_;
        }
        3 => {
            let mut v_n_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_409_);
            crate::leanh::lean_dec(v_h__6_408_);
            crate::leanh::lean_dec(v_h__5_407_);
            crate::leanh::lean_dec(v_h__3_405_);
            crate::leanh::lean_dec(v_h__2_404_);
            crate::leanh::lean_dec(v_h__1_403_);
            v_n_416_ = crate::leanh::lean_ctor_get(v_op_402_, 0);
            crate::leanh::lean_inc(v_n_416_);
            crate::leanh::lean_dec_ref_known(v_op_402_, 1);
            v___x_417_ = crate::leanh::lean_apply_1(v_h__4_406_, v_n_416_);
            return v___x_417_;
        }
        4 => {
            let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_409_);
            crate::leanh::lean_dec(v_h__6_408_);
            crate::leanh::lean_dec(v_h__4_406_);
            crate::leanh::lean_dec(v_h__3_405_);
            crate::leanh::lean_dec(v_h__2_404_);
            crate::leanh::lean_dec(v_h__1_403_);
            v___x_418_ = crate::leanh::lean_box(0);
            v___x_419_ = crate::leanh::lean_apply_1(v_h__5_407_, v___x_418_);
            return v___x_419_;
        }
        5 => {
            let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_409_);
            crate::leanh::lean_dec(v_h__5_407_);
            crate::leanh::lean_dec(v_h__4_406_);
            crate::leanh::lean_dec(v_h__3_405_);
            crate::leanh::lean_dec(v_h__2_404_);
            crate::leanh::lean_dec(v_h__1_403_);
            v___x_420_ = crate::leanh::lean_box(0);
            v___x_421_ = crate::leanh::lean_apply_1(v_h__6_408_, v___x_420_);
            return v___x_421_;
        }
        _ => {
            let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_408_);
            crate::leanh::lean_dec(v_h__5_407_);
            crate::leanh::lean_dec(v_h__4_406_);
            crate::leanh::lean_dec(v_h__3_405_);
            crate::leanh::lean_dec(v_h__2_404_);
            crate::leanh::lean_dec(v_h__1_403_);
            v___x_422_ = crate::leanh::lean_box(0);
            v___x_423_ = crate::leanh::lean_apply_1(v_h__7_409_, v___x_422_);
            return v___x_423_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__15_splitter(
    mut v_motive_424_: *mut crate::leanh::LeanObject,
    mut v_op_425_: *mut crate::leanh::LeanObject,
    mut v_h__1_426_: *mut crate::leanh::LeanObject,
    mut v_h__2_427_: *mut crate::leanh::LeanObject,
    mut v_h__3_428_: *mut crate::leanh::LeanObject,
    mut v_h__4_429_: *mut crate::leanh::LeanObject,
    mut v_h__5_430_: *mut crate::leanh::LeanObject,
    mut v_h__6_431_: *mut crate::leanh::LeanObject,
    mut v_h__7_432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_op_425_) {
        0 => {
            let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_432_);
            crate::leanh::lean_dec(v_h__6_431_);
            crate::leanh::lean_dec(v_h__5_430_);
            crate::leanh::lean_dec(v_h__4_429_);
            crate::leanh::lean_dec(v_h__3_428_);
            crate::leanh::lean_dec(v_h__2_427_);
            v___x_433_ = crate::leanh::lean_box(0);
            v___x_434_ = crate::leanh::lean_apply_1(v_h__1_426_, v___x_433_);
            return v___x_434_;
        }
        1 => {
            let mut v_n_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_432_);
            crate::leanh::lean_dec(v_h__6_431_);
            crate::leanh::lean_dec(v_h__5_430_);
            crate::leanh::lean_dec(v_h__4_429_);
            crate::leanh::lean_dec(v_h__3_428_);
            crate::leanh::lean_dec(v_h__1_426_);
            v_n_435_ = crate::leanh::lean_ctor_get(v_op_425_, 0);
            crate::leanh::lean_inc(v_n_435_);
            crate::leanh::lean_dec_ref_known(v_op_425_, 1);
            v___x_436_ = crate::leanh::lean_apply_1(v_h__2_427_, v_n_435_);
            return v___x_436_;
        }
        2 => {
            let mut v_n_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_432_);
            crate::leanh::lean_dec(v_h__6_431_);
            crate::leanh::lean_dec(v_h__5_430_);
            crate::leanh::lean_dec(v_h__4_429_);
            crate::leanh::lean_dec(v_h__2_427_);
            crate::leanh::lean_dec(v_h__1_426_);
            v_n_437_ = crate::leanh::lean_ctor_get(v_op_425_, 0);
            crate::leanh::lean_inc(v_n_437_);
            crate::leanh::lean_dec_ref_known(v_op_425_, 1);
            v___x_438_ = crate::leanh::lean_apply_1(v_h__3_428_, v_n_437_);
            return v___x_438_;
        }
        3 => {
            let mut v_n_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_432_);
            crate::leanh::lean_dec(v_h__6_431_);
            crate::leanh::lean_dec(v_h__5_430_);
            crate::leanh::lean_dec(v_h__3_428_);
            crate::leanh::lean_dec(v_h__2_427_);
            crate::leanh::lean_dec(v_h__1_426_);
            v_n_439_ = crate::leanh::lean_ctor_get(v_op_425_, 0);
            crate::leanh::lean_inc(v_n_439_);
            crate::leanh::lean_dec_ref_known(v_op_425_, 1);
            v___x_440_ = crate::leanh::lean_apply_1(v_h__4_429_, v_n_439_);
            return v___x_440_;
        }
        4 => {
            let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_432_);
            crate::leanh::lean_dec(v_h__6_431_);
            crate::leanh::lean_dec(v_h__4_429_);
            crate::leanh::lean_dec(v_h__3_428_);
            crate::leanh::lean_dec(v_h__2_427_);
            crate::leanh::lean_dec(v_h__1_426_);
            v___x_441_ = crate::leanh::lean_box(0);
            v___x_442_ = crate::leanh::lean_apply_1(v_h__5_430_, v___x_441_);
            return v___x_442_;
        }
        5 => {
            let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_432_);
            crate::leanh::lean_dec(v_h__5_430_);
            crate::leanh::lean_dec(v_h__4_429_);
            crate::leanh::lean_dec(v_h__3_428_);
            crate::leanh::lean_dec(v_h__2_427_);
            crate::leanh::lean_dec(v_h__1_426_);
            v___x_443_ = crate::leanh::lean_box(0);
            v___x_444_ = crate::leanh::lean_apply_1(v_h__6_431_, v___x_443_);
            return v___x_444_;
        }
        _ => {
            let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_431_);
            crate::leanh::lean_dec(v_h__5_430_);
            crate::leanh::lean_dec(v_h__4_429_);
            crate::leanh::lean_dec(v_h__3_428_);
            crate::leanh::lean_dec(v_h__2_427_);
            crate::leanh::lean_dec(v_h__1_426_);
            v___x_445_ = crate::leanh::lean_box(0);
            v___x_446_ = crate::leanh::lean_apply_1(v_h__7_432_, v___x_445_);
            return v___x_446_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg(
    mut v_op_447_: u8,
    mut v_h__1_448_: *mut crate::leanh::LeanObject,
    mut v_h__2_449_: *mut crate::leanh::LeanObject,
    mut v_h__3_450_: *mut crate::leanh::LeanObject,
    mut v_h__4_451_: *mut crate::leanh::LeanObject,
    mut v_h__5_452_: *mut crate::leanh::LeanObject,
    mut v_h__6_453_: *mut crate::leanh::LeanObject,
    mut v_h__7_454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_op_447_ {
        0 => {
            let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_454_);
            crate::leanh::lean_dec(v_h__6_453_);
            crate::leanh::lean_dec(v_h__5_452_);
            crate::leanh::lean_dec(v_h__4_451_);
            crate::leanh::lean_dec(v_h__3_450_);
            crate::leanh::lean_dec(v_h__2_449_);
            v___x_455_ = crate::leanh::lean_box(0);
            v___x_456_ = crate::leanh::lean_apply_1(v_h__1_448_, v___x_455_);
            return v___x_456_;
        }
        1 => {
            let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_454_);
            crate::leanh::lean_dec(v_h__6_453_);
            crate::leanh::lean_dec(v_h__5_452_);
            crate::leanh::lean_dec(v_h__4_451_);
            crate::leanh::lean_dec(v_h__3_450_);
            crate::leanh::lean_dec(v_h__1_448_);
            v___x_457_ = crate::leanh::lean_box(0);
            v___x_458_ = crate::leanh::lean_apply_1(v_h__2_449_, v___x_457_);
            return v___x_458_;
        }
        2 => {
            let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_454_);
            crate::leanh::lean_dec(v_h__6_453_);
            crate::leanh::lean_dec(v_h__5_452_);
            crate::leanh::lean_dec(v_h__4_451_);
            crate::leanh::lean_dec(v_h__2_449_);
            crate::leanh::lean_dec(v_h__1_448_);
            v___x_459_ = crate::leanh::lean_box(0);
            v___x_460_ = crate::leanh::lean_apply_1(v_h__3_450_, v___x_459_);
            return v___x_460_;
        }
        3 => {
            let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_454_);
            crate::leanh::lean_dec(v_h__6_453_);
            crate::leanh::lean_dec(v_h__5_452_);
            crate::leanh::lean_dec(v_h__3_450_);
            crate::leanh::lean_dec(v_h__2_449_);
            crate::leanh::lean_dec(v_h__1_448_);
            v___x_461_ = crate::leanh::lean_box(0);
            v___x_462_ = crate::leanh::lean_apply_1(v_h__4_451_, v___x_461_);
            return v___x_462_;
        }
        4 => {
            let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_454_);
            crate::leanh::lean_dec(v_h__6_453_);
            crate::leanh::lean_dec(v_h__4_451_);
            crate::leanh::lean_dec(v_h__3_450_);
            crate::leanh::lean_dec(v_h__2_449_);
            crate::leanh::lean_dec(v_h__1_448_);
            v___x_463_ = crate::leanh::lean_box(0);
            v___x_464_ = crate::leanh::lean_apply_1(v_h__5_452_, v___x_463_);
            return v___x_464_;
        }
        5 => {
            let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_454_);
            crate::leanh::lean_dec(v_h__5_452_);
            crate::leanh::lean_dec(v_h__4_451_);
            crate::leanh::lean_dec(v_h__3_450_);
            crate::leanh::lean_dec(v_h__2_449_);
            crate::leanh::lean_dec(v_h__1_448_);
            v___x_465_ = crate::leanh::lean_box(0);
            v___x_466_ = crate::leanh::lean_apply_1(v_h__6_453_, v___x_465_);
            return v___x_466_;
        }
        _ => {
            let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_453_);
            crate::leanh::lean_dec(v_h__5_452_);
            crate::leanh::lean_dec(v_h__4_451_);
            crate::leanh::lean_dec(v_h__3_450_);
            crate::leanh::lean_dec(v_h__2_449_);
            crate::leanh::lean_dec(v_h__1_448_);
            v___x_467_ = crate::leanh::lean_box(0);
            v___x_468_ = crate::leanh::lean_apply_1(v_h__7_454_, v___x_467_);
            return v___x_468_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg___boxed(
    mut v_op_469_: *mut crate::leanh::LeanObject,
    mut v_h__1_470_: *mut crate::leanh::LeanObject,
    mut v_h__2_471_: *mut crate::leanh::LeanObject,
    mut v_h__3_472_: *mut crate::leanh::LeanObject,
    mut v_h__4_473_: *mut crate::leanh::LeanObject,
    mut v_h__5_474_: *mut crate::leanh::LeanObject,
    mut v_h__6_475_: *mut crate::leanh::LeanObject,
    mut v_h__7_476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_op_76__boxed_477_: u8 = 0;
    let mut v_res_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_op_76__boxed_477_ = (crate::leanh::lean_unbox(v_op_469_) as u8);
    v_res_478_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg(v_op_76__boxed_477_, v_h__1_470_, v_h__2_471_, v_h__3_472_, v_h__4_473_, v_h__5_474_, v_h__6_475_, v_h__7_476_);
    return v_res_478_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter(
    mut v_motive_479_: *mut crate::leanh::LeanObject,
    mut v_op_480_: u8,
    mut v_h__1_481_: *mut crate::leanh::LeanObject,
    mut v_h__2_482_: *mut crate::leanh::LeanObject,
    mut v_h__3_483_: *mut crate::leanh::LeanObject,
    mut v_h__4_484_: *mut crate::leanh::LeanObject,
    mut v_h__5_485_: *mut crate::leanh::LeanObject,
    mut v_h__6_486_: *mut crate::leanh::LeanObject,
    mut v_h__7_487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_op_480_ {
        0 => {
            let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_487_);
            crate::leanh::lean_dec(v_h__6_486_);
            crate::leanh::lean_dec(v_h__5_485_);
            crate::leanh::lean_dec(v_h__4_484_);
            crate::leanh::lean_dec(v_h__3_483_);
            crate::leanh::lean_dec(v_h__2_482_);
            v___x_488_ = crate::leanh::lean_box(0);
            v___x_489_ = crate::leanh::lean_apply_1(v_h__1_481_, v___x_488_);
            return v___x_489_;
        }
        1 => {
            let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_487_);
            crate::leanh::lean_dec(v_h__6_486_);
            crate::leanh::lean_dec(v_h__5_485_);
            crate::leanh::lean_dec(v_h__4_484_);
            crate::leanh::lean_dec(v_h__3_483_);
            crate::leanh::lean_dec(v_h__1_481_);
            v___x_490_ = crate::leanh::lean_box(0);
            v___x_491_ = crate::leanh::lean_apply_1(v_h__2_482_, v___x_490_);
            return v___x_491_;
        }
        2 => {
            let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_487_);
            crate::leanh::lean_dec(v_h__6_486_);
            crate::leanh::lean_dec(v_h__5_485_);
            crate::leanh::lean_dec(v_h__4_484_);
            crate::leanh::lean_dec(v_h__2_482_);
            crate::leanh::lean_dec(v_h__1_481_);
            v___x_492_ = crate::leanh::lean_box(0);
            v___x_493_ = crate::leanh::lean_apply_1(v_h__3_483_, v___x_492_);
            return v___x_493_;
        }
        3 => {
            let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_487_);
            crate::leanh::lean_dec(v_h__6_486_);
            crate::leanh::lean_dec(v_h__5_485_);
            crate::leanh::lean_dec(v_h__3_483_);
            crate::leanh::lean_dec(v_h__2_482_);
            crate::leanh::lean_dec(v_h__1_481_);
            v___x_494_ = crate::leanh::lean_box(0);
            v___x_495_ = crate::leanh::lean_apply_1(v_h__4_484_, v___x_494_);
            return v___x_495_;
        }
        4 => {
            let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_487_);
            crate::leanh::lean_dec(v_h__6_486_);
            crate::leanh::lean_dec(v_h__4_484_);
            crate::leanh::lean_dec(v_h__3_483_);
            crate::leanh::lean_dec(v_h__2_482_);
            crate::leanh::lean_dec(v_h__1_481_);
            v___x_496_ = crate::leanh::lean_box(0);
            v___x_497_ = crate::leanh::lean_apply_1(v_h__5_485_, v___x_496_);
            return v___x_497_;
        }
        5 => {
            let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_487_);
            crate::leanh::lean_dec(v_h__5_485_);
            crate::leanh::lean_dec(v_h__4_484_);
            crate::leanh::lean_dec(v_h__3_483_);
            crate::leanh::lean_dec(v_h__2_482_);
            crate::leanh::lean_dec(v_h__1_481_);
            v___x_498_ = crate::leanh::lean_box(0);
            v___x_499_ = crate::leanh::lean_apply_1(v_h__6_486_, v___x_498_);
            return v___x_499_;
        }
        _ => {
            let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_486_);
            crate::leanh::lean_dec(v_h__5_485_);
            crate::leanh::lean_dec(v_h__4_484_);
            crate::leanh::lean_dec(v_h__3_483_);
            crate::leanh::lean_dec(v_h__2_482_);
            crate::leanh::lean_dec(v_h__1_481_);
            v___x_500_ = crate::leanh::lean_box(0);
            v___x_501_ = crate::leanh::lean_apply_1(v_h__7_487_, v___x_500_);
            return v___x_501_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___boxed(
    mut v_motive_502_: *mut crate::leanh::LeanObject,
    mut v_op_503_: *mut crate::leanh::LeanObject,
    mut v_h__1_504_: *mut crate::leanh::LeanObject,
    mut v_h__2_505_: *mut crate::leanh::LeanObject,
    mut v_h__3_506_: *mut crate::leanh::LeanObject,
    mut v_h__4_507_: *mut crate::leanh::LeanObject,
    mut v_h__5_508_: *mut crate::leanh::LeanObject,
    mut v_h__6_509_: *mut crate::leanh::LeanObject,
    mut v_h__7_510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_op_107__boxed_511_: u8 = 0;
    let mut v_res_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_op_107__boxed_511_ = (crate::leanh::lean_unbox(v_op_503_) as u8);
    v_res_512_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter(v_motive_502_, v_op_107__boxed_511_, v_h__1_504_, v_h__2_505_, v_h__3_506_, v_h__4_507_, v_h__5_508_, v_h__6_509_, v_h__7_510_);
    return v_res_512_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Var(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_ShiftRight(
            builtin,
        );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Append(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Replicate(
            builtin,
        );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Extract(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateLeft(
            builtin,
        );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateRight(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Mul(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Reverse(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Clz(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Cpop(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Var(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_ShiftRight(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Append(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Replicate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Extract(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateLeft(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateRight(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Mul(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Reverse(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Clz(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Cpop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(builtin);
}
