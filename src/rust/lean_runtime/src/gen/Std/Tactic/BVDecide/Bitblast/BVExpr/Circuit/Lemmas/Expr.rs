// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Expr
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Var Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ShiftRight Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Append Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Replicate Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Extract Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.RotateLeft Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.RotateRight Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Mul Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Umod Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Reverse Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Clz Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr Init.ByCases Init.Data.Nat.Linear Init.Omega
use crate::leanh::{LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject, LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject, LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_5, lean_apply_6, lean_box, lean_ctor_get, lean_ctor_get_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag, lean_unbox};
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
    mut v_x_257_: *mut LeanObject,
    mut v_h__1_258_: *mut LeanObject,
    mut v_h__2_259_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_257_) == 0 {
        let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_258_);
        v___x_260_ = lean_apply_1(v_h__2_259_, lean_box(0));
        return v___x_260_;
    } else {
        let mut v_val_261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_259_);
        v_val_261_ = lean_ctor_get(v_x_257_, 0);
        lean_inc(v_val_261_);
        lean_dec_ref_known(v_x_257_, 1);
        v___x_262_ = lean_apply_2(v_h__1_258_, v_val_261_, lean_box(0));
        return v___x_262_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter(
    mut v_w_263_: *mut LeanObject,
    mut v_expr_264_: *mut LeanObject,
    mut v_motive_265_: *mut LeanObject,
    mut v_x_266_: *mut LeanObject,
    mut v_h__1_267_: *mut LeanObject,
    mut v_h__2_268_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_266_) == 0 {
        let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_267_);
        v___x_269_ = lean_apply_1(v_h__2_268_, lean_box(0));
        return v___x_269_;
    } else {
        let mut v_val_270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_268_);
        v_val_270_ = lean_ctor_get(v_x_266_, 0);
        lean_inc(v_val_270_);
        lean_dec_ref_known(v_x_266_, 1);
        v___x_271_ = lean_apply_2(v_h__1_267_, v_val_270_, lean_box(0));
        return v___x_271_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter___boxed(
    mut v_w_272_: *mut LeanObject,
    mut v_expr_273_: *mut LeanObject,
    mut v_motive_274_: *mut LeanObject,
    mut v_x_275_: *mut LeanObject,
    mut v_h__1_276_: *mut LeanObject,
    mut v_h__2_277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_278_: *mut LeanObject = core::ptr::null_mut();
    v_res_278_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter(v_w_272_, v_expr_273_, v_motive_274_, v_x_275_, v_h__1_276_, v_h__2_277_);
    lean_dec_ref(v_expr_273_);
    lean_dec(v_w_272_);
    return v_res_278_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter___redArg(
    mut v_x_279_: *mut LeanObject,
    mut v_h__1_280_: *mut LeanObject,
    mut v_h__2_281_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_279_) == 0 {
        let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_280_);
        v___x_282_ = lean_box(0);
        v___x_283_ = lean_apply_1(v_h__2_281_, v___x_282_);
        return v___x_283_;
    } else {
        let mut v_val_284_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_281_);
        v_val_284_ = lean_ctor_get(v_x_279_, 0);
        lean_inc(v_val_284_);
        lean_dec_ref_known(v_x_279_, 1);
        v___x_285_ = lean_apply_1(v_h__1_280_, v_val_284_);
        return v___x_285_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter(
    mut v_w_286_: *mut LeanObject,
    mut v_aig_287_: *mut LeanObject,
    mut v_motive_288_: *mut LeanObject,
    mut v_x_289_: *mut LeanObject,
    mut v_h__1_290_: *mut LeanObject,
    mut v_h__2_291_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_289_) == 0 {
        let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_290_);
        v___x_292_ = lean_box(0);
        v___x_293_ = lean_apply_1(v_h__2_291_, v___x_292_);
        return v___x_293_;
    } else {
        let mut v_val_294_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_291_);
        v_val_294_ = lean_ctor_get(v_x_289_, 0);
        lean_inc(v_val_294_);
        lean_dec_ref_known(v_x_289_, 1);
        v___x_295_ = lean_apply_1(v_h__1_290_, v_val_294_);
        return v___x_295_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter___boxed(
    mut v_w_296_: *mut LeanObject,
    mut v_aig_297_: *mut LeanObject,
    mut v_motive_298_: *mut LeanObject,
    mut v_x_299_: *mut LeanObject,
    mut v_h__1_300_: *mut LeanObject,
    mut v_h__2_301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_302_: *mut LeanObject = core::ptr::null_mut();
    v_res_302_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter(v_w_296_, v_aig_297_, v_motive_298_, v_x_299_, v_h__1_300_, v_h__2_301_);
    lean_dec_ref(v_aig_297_);
    lean_dec(v_w_296_);
    return v_res_302_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__17_splitter___redArg(
    mut v_w_303_: *mut LeanObject,
    mut v_expr_304_: *mut LeanObject,
    mut v_h__1_305_: *mut LeanObject,
    mut v_h__2_306_: *mut LeanObject,
    mut v_h__3_307_: *mut LeanObject,
    mut v_h__4_308_: *mut LeanObject,
    mut v_h__5_309_: *mut LeanObject,
    mut v_h__6_310_: *mut LeanObject,
    mut v_h__7_311_: *mut LeanObject,
    mut v_h__8_312_: *mut LeanObject,
    mut v_h__9_313_: *mut LeanObject,
    mut v_h__10_314_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_expr_304_) {
        0 => {
            let mut v_idx_315_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__10_314_);
            lean_dec(v_h__9_313_);
            lean_dec(v_h__8_312_);
            lean_dec(v_h__7_311_);
            lean_dec(v_h__6_310_);
            lean_dec(v_h__5_309_);
            lean_dec(v_h__4_308_);
            lean_dec(v_h__3_307_);
            lean_dec(v_h__2_306_);
            v_idx_315_ = lean_ctor_get(v_expr_304_, 1);
            lean_inc(v_idx_315_);
            lean_dec_ref_known(v_expr_304_, 2);
            v___x_316_ = lean_apply_2(v_h__1_305_, v_w_303_, v_idx_315_);
            return v___x_316_;
        }
        1 => {
            let mut v_val_317_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__10_314_);
            lean_dec(v_h__9_313_);
            lean_dec(v_h__8_312_);
            lean_dec(v_h__7_311_);
            lean_dec(v_h__6_310_);
            lean_dec(v_h__5_309_);
            lean_dec(v_h__4_308_);
            lean_dec(v_h__3_307_);
            lean_dec(v_h__1_305_);
            v_val_317_ = lean_ctor_get(v_expr_304_, 1);
            lean_inc(v_val_317_);
            lean_dec_ref_known(v_expr_304_, 2);
            v___x_318_ = lean_apply_2(v_h__2_306_, v_w_303_, v_val_317_);
            return v___x_318_;
        }
        2 => {
            let mut v_w_319_: *mut LeanObject = core::ptr::null_mut();
            let mut v_start_320_: *mut LeanObject = core::ptr::null_mut();
            let mut v_expr_321_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__10_314_);
            lean_dec(v_h__9_313_);
            lean_dec(v_h__8_312_);
            lean_dec(v_h__6_310_);
            lean_dec(v_h__5_309_);
            lean_dec(v_h__4_308_);
            lean_dec(v_h__3_307_);
            lean_dec(v_h__2_306_);
            lean_dec(v_h__1_305_);
            v_w_319_ = lean_ctor_get(v_expr_304_, 0);
            lean_inc(v_w_319_);
            v_start_320_ = lean_ctor_get(v_expr_304_, 1);
            lean_inc(v_start_320_);
            v_expr_321_ = lean_ctor_get(v_expr_304_, 3);
            lean_inc_ref(v_expr_321_);
            lean_dec_ref_known(v_expr_304_, 4);
            v___x_322_ = lean_apply_4(v_h__7_311_, v_w_303_, v_w_319_, v_start_320_, v_expr_321_);
            return v___x_322_;
        }
        3 => {
            let mut v_lhs_323_: *mut LeanObject = core::ptr::null_mut();
            let mut v_op_324_: u8 = 0;
            let mut v_rhs_325_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__10_314_);
            lean_dec(v_h__9_313_);
            lean_dec(v_h__8_312_);
            lean_dec(v_h__7_311_);
            lean_dec(v_h__6_310_);
            lean_dec(v_h__5_309_);
            lean_dec(v_h__4_308_);
            lean_dec(v_h__2_306_);
            lean_dec(v_h__1_305_);
            v_lhs_323_ = lean_ctor_get(v_expr_304_, 1);
            lean_inc_ref(v_lhs_323_);
            v_op_324_ = lean_ctor_get_uint8(
                v_expr_304_,
                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
            );
            v_rhs_325_ = lean_ctor_get(v_expr_304_, 2);
            lean_inc_ref(v_rhs_325_);
            lean_dec_ref_known(v_expr_304_, 3);
            v___x_326_ = lean_box((v_op_324_) as usize);
            v___x_327_ = lean_apply_4(v_h__3_307_, v_w_303_, v_lhs_323_, v___x_326_, v_rhs_325_);
            return v___x_327_;
        }
        4 => {
            let mut v_op_328_: *mut LeanObject = core::ptr::null_mut();
            let mut v_operand_329_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__10_314_);
            lean_dec(v_h__9_313_);
            lean_dec(v_h__8_312_);
            lean_dec(v_h__7_311_);
            lean_dec(v_h__6_310_);
            lean_dec(v_h__5_309_);
            lean_dec(v_h__3_307_);
            lean_dec(v_h__2_306_);
            lean_dec(v_h__1_305_);
            v_op_328_ = lean_ctor_get(v_expr_304_, 1);
            lean_inc(v_op_328_);
            v_operand_329_ = lean_ctor_get(v_expr_304_, 2);
            lean_inc_ref(v_operand_329_);
            lean_dec_ref_known(v_expr_304_, 3);
            v___x_330_ = lean_apply_3(v_h__4_308_, v_w_303_, v_op_328_, v_operand_329_);
            return v___x_330_;
        }
        5 => {
            let mut v_l_331_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_332_: *mut LeanObject = core::ptr::null_mut();
            let mut v_lhs_333_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rhs_334_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__10_314_);
            lean_dec(v_h__9_313_);
            lean_dec(v_h__8_312_);
            lean_dec(v_h__7_311_);
            lean_dec(v_h__6_310_);
            lean_dec(v_h__4_308_);
            lean_dec(v_h__3_307_);
            lean_dec(v_h__2_306_);
            lean_dec(v_h__1_305_);
            v_l_331_ = lean_ctor_get(v_expr_304_, 0);
            lean_inc(v_l_331_);
            v_r_332_ = lean_ctor_get(v_expr_304_, 1);
            lean_inc(v_r_332_);
            v_lhs_333_ = lean_ctor_get(v_expr_304_, 3);
            lean_inc_ref(v_lhs_333_);
            v_rhs_334_ = lean_ctor_get(v_expr_304_, 4);
            lean_inc_ref(v_rhs_334_);
            lean_dec_ref_known(v_expr_304_, 5);
            v___x_335_ = lean_apply_6(
                v_h__5_309_,
                v_w_303_,
                v_l_331_,
                v_r_332_,
                v_lhs_333_,
                v_rhs_334_,
                lean_box(0),
            );
            return v___x_335_;
        }
        6 => {
            let mut v_w_336_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_337_: *mut LeanObject = core::ptr::null_mut();
            let mut v_expr_338_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__10_314_);
            lean_dec(v_h__9_313_);
            lean_dec(v_h__8_312_);
            lean_dec(v_h__7_311_);
            lean_dec(v_h__5_309_);
            lean_dec(v_h__4_308_);
            lean_dec(v_h__3_307_);
            lean_dec(v_h__2_306_);
            lean_dec(v_h__1_305_);
            v_w_336_ = lean_ctor_get(v_expr_304_, 0);
            lean_inc(v_w_336_);
            v_n_337_ = lean_ctor_get(v_expr_304_, 2);
            lean_inc(v_n_337_);
            v_expr_338_ = lean_ctor_get(v_expr_304_, 3);
            lean_inc_ref(v_expr_338_);
            lean_dec_ref_known(v_expr_304_, 4);
            v___x_339_ = lean_apply_5(
                v_h__6_310_,
                v_w_303_,
                v_w_336_,
                v_n_337_,
                v_expr_338_,
                lean_box(0),
            );
            return v___x_339_;
        }
        7 => {
            let mut v_n_340_: *mut LeanObject = core::ptr::null_mut();
            let mut v_lhs_341_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rhs_342_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__10_314_);
            lean_dec(v_h__9_313_);
            lean_dec(v_h__7_311_);
            lean_dec(v_h__6_310_);
            lean_dec(v_h__5_309_);
            lean_dec(v_h__4_308_);
            lean_dec(v_h__3_307_);
            lean_dec(v_h__2_306_);
            lean_dec(v_h__1_305_);
            v_n_340_ = lean_ctor_get(v_expr_304_, 1);
            lean_inc(v_n_340_);
            v_lhs_341_ = lean_ctor_get(v_expr_304_, 2);
            lean_inc_ref(v_lhs_341_);
            v_rhs_342_ = lean_ctor_get(v_expr_304_, 3);
            lean_inc_ref(v_rhs_342_);
            lean_dec_ref_known(v_expr_304_, 4);
            v___x_343_ = lean_apply_4(v_h__8_312_, v_w_303_, v_n_340_, v_lhs_341_, v_rhs_342_);
            return v___x_343_;
        }
        8 => {
            let mut v_n_344_: *mut LeanObject = core::ptr::null_mut();
            let mut v_lhs_345_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rhs_346_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__10_314_);
            lean_dec(v_h__8_312_);
            lean_dec(v_h__7_311_);
            lean_dec(v_h__6_310_);
            lean_dec(v_h__5_309_);
            lean_dec(v_h__4_308_);
            lean_dec(v_h__3_307_);
            lean_dec(v_h__2_306_);
            lean_dec(v_h__1_305_);
            v_n_344_ = lean_ctor_get(v_expr_304_, 1);
            lean_inc(v_n_344_);
            v_lhs_345_ = lean_ctor_get(v_expr_304_, 2);
            lean_inc_ref(v_lhs_345_);
            v_rhs_346_ = lean_ctor_get(v_expr_304_, 3);
            lean_inc_ref(v_rhs_346_);
            lean_dec_ref_known(v_expr_304_, 4);
            v___x_347_ = lean_apply_4(v_h__9_313_, v_w_303_, v_n_344_, v_lhs_345_, v_rhs_346_);
            return v___x_347_;
        }
        _ => {
            let mut v_n_348_: *mut LeanObject = core::ptr::null_mut();
            let mut v_lhs_349_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rhs_350_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_313_);
            lean_dec(v_h__8_312_);
            lean_dec(v_h__7_311_);
            lean_dec(v_h__6_310_);
            lean_dec(v_h__5_309_);
            lean_dec(v_h__4_308_);
            lean_dec(v_h__3_307_);
            lean_dec(v_h__2_306_);
            lean_dec(v_h__1_305_);
            v_n_348_ = lean_ctor_get(v_expr_304_, 1);
            lean_inc(v_n_348_);
            v_lhs_349_ = lean_ctor_get(v_expr_304_, 2);
            lean_inc_ref(v_lhs_349_);
            v_rhs_350_ = lean_ctor_get(v_expr_304_, 3);
            lean_inc_ref(v_rhs_350_);
            lean_dec_ref_known(v_expr_304_, 4);
            v___x_351_ = lean_apply_4(v_h__10_314_, v_w_303_, v_n_348_, v_lhs_349_, v_rhs_350_);
            return v___x_351_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__17_splitter(
    mut v_motive_352_: *mut LeanObject,
    mut v_w_353_: *mut LeanObject,
    mut v_expr_354_: *mut LeanObject,
    mut v_h__1_355_: *mut LeanObject,
    mut v_h__2_356_: *mut LeanObject,
    mut v_h__3_357_: *mut LeanObject,
    mut v_h__4_358_: *mut LeanObject,
    mut v_h__5_359_: *mut LeanObject,
    mut v_h__6_360_: *mut LeanObject,
    mut v_h__7_361_: *mut LeanObject,
    mut v_h__8_362_: *mut LeanObject,
    mut v_h__9_363_: *mut LeanObject,
    mut v_h__10_364_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_expr_354_) {
        0 => {
            let mut v_idx_365_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__10_364_);
            lean_dec(v_h__9_363_);
            lean_dec(v_h__8_362_);
            lean_dec(v_h__7_361_);
            lean_dec(v_h__6_360_);
            lean_dec(v_h__5_359_);
            lean_dec(v_h__4_358_);
            lean_dec(v_h__3_357_);
            lean_dec(v_h__2_356_);
            v_idx_365_ = lean_ctor_get(v_expr_354_, 1);
            lean_inc(v_idx_365_);
            lean_dec_ref_known(v_expr_354_, 2);
            v___x_366_ = lean_apply_2(v_h__1_355_, v_w_353_, v_idx_365_);
            return v___x_366_;
        }
        1 => {
            let mut v_val_367_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__10_364_);
            lean_dec(v_h__9_363_);
            lean_dec(v_h__8_362_);
            lean_dec(v_h__7_361_);
            lean_dec(v_h__6_360_);
            lean_dec(v_h__5_359_);
            lean_dec(v_h__4_358_);
            lean_dec(v_h__3_357_);
            lean_dec(v_h__1_355_);
            v_val_367_ = lean_ctor_get(v_expr_354_, 1);
            lean_inc(v_val_367_);
            lean_dec_ref_known(v_expr_354_, 2);
            v___x_368_ = lean_apply_2(v_h__2_356_, v_w_353_, v_val_367_);
            return v___x_368_;
        }
        2 => {
            let mut v_w_369_: *mut LeanObject = core::ptr::null_mut();
            let mut v_start_370_: *mut LeanObject = core::ptr::null_mut();
            let mut v_expr_371_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__10_364_);
            lean_dec(v_h__9_363_);
            lean_dec(v_h__8_362_);
            lean_dec(v_h__6_360_);
            lean_dec(v_h__5_359_);
            lean_dec(v_h__4_358_);
            lean_dec(v_h__3_357_);
            lean_dec(v_h__2_356_);
            lean_dec(v_h__1_355_);
            v_w_369_ = lean_ctor_get(v_expr_354_, 0);
            lean_inc(v_w_369_);
            v_start_370_ = lean_ctor_get(v_expr_354_, 1);
            lean_inc(v_start_370_);
            v_expr_371_ = lean_ctor_get(v_expr_354_, 3);
            lean_inc_ref(v_expr_371_);
            lean_dec_ref_known(v_expr_354_, 4);
            v___x_372_ = lean_apply_4(v_h__7_361_, v_w_353_, v_w_369_, v_start_370_, v_expr_371_);
            return v___x_372_;
        }
        3 => {
            let mut v_lhs_373_: *mut LeanObject = core::ptr::null_mut();
            let mut v_op_374_: u8 = 0;
            let mut v_rhs_375_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__10_364_);
            lean_dec(v_h__9_363_);
            lean_dec(v_h__8_362_);
            lean_dec(v_h__7_361_);
            lean_dec(v_h__6_360_);
            lean_dec(v_h__5_359_);
            lean_dec(v_h__4_358_);
            lean_dec(v_h__2_356_);
            lean_dec(v_h__1_355_);
            v_lhs_373_ = lean_ctor_get(v_expr_354_, 1);
            lean_inc_ref(v_lhs_373_);
            v_op_374_ = lean_ctor_get_uint8(
                v_expr_354_,
                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
            );
            v_rhs_375_ = lean_ctor_get(v_expr_354_, 2);
            lean_inc_ref(v_rhs_375_);
            lean_dec_ref_known(v_expr_354_, 3);
            v___x_376_ = lean_box((v_op_374_) as usize);
            v___x_377_ = lean_apply_4(v_h__3_357_, v_w_353_, v_lhs_373_, v___x_376_, v_rhs_375_);
            return v___x_377_;
        }
        4 => {
            let mut v_op_378_: *mut LeanObject = core::ptr::null_mut();
            let mut v_operand_379_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__10_364_);
            lean_dec(v_h__9_363_);
            lean_dec(v_h__8_362_);
            lean_dec(v_h__7_361_);
            lean_dec(v_h__6_360_);
            lean_dec(v_h__5_359_);
            lean_dec(v_h__3_357_);
            lean_dec(v_h__2_356_);
            lean_dec(v_h__1_355_);
            v_op_378_ = lean_ctor_get(v_expr_354_, 1);
            lean_inc(v_op_378_);
            v_operand_379_ = lean_ctor_get(v_expr_354_, 2);
            lean_inc_ref(v_operand_379_);
            lean_dec_ref_known(v_expr_354_, 3);
            v___x_380_ = lean_apply_3(v_h__4_358_, v_w_353_, v_op_378_, v_operand_379_);
            return v___x_380_;
        }
        5 => {
            let mut v_l_381_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_382_: *mut LeanObject = core::ptr::null_mut();
            let mut v_lhs_383_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rhs_384_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__10_364_);
            lean_dec(v_h__9_363_);
            lean_dec(v_h__8_362_);
            lean_dec(v_h__7_361_);
            lean_dec(v_h__6_360_);
            lean_dec(v_h__4_358_);
            lean_dec(v_h__3_357_);
            lean_dec(v_h__2_356_);
            lean_dec(v_h__1_355_);
            v_l_381_ = lean_ctor_get(v_expr_354_, 0);
            lean_inc(v_l_381_);
            v_r_382_ = lean_ctor_get(v_expr_354_, 1);
            lean_inc(v_r_382_);
            v_lhs_383_ = lean_ctor_get(v_expr_354_, 3);
            lean_inc_ref(v_lhs_383_);
            v_rhs_384_ = lean_ctor_get(v_expr_354_, 4);
            lean_inc_ref(v_rhs_384_);
            lean_dec_ref_known(v_expr_354_, 5);
            v___x_385_ = lean_apply_6(
                v_h__5_359_,
                v_w_353_,
                v_l_381_,
                v_r_382_,
                v_lhs_383_,
                v_rhs_384_,
                lean_box(0),
            );
            return v___x_385_;
        }
        6 => {
            let mut v_w_386_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_387_: *mut LeanObject = core::ptr::null_mut();
            let mut v_expr_388_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__10_364_);
            lean_dec(v_h__9_363_);
            lean_dec(v_h__8_362_);
            lean_dec(v_h__7_361_);
            lean_dec(v_h__5_359_);
            lean_dec(v_h__4_358_);
            lean_dec(v_h__3_357_);
            lean_dec(v_h__2_356_);
            lean_dec(v_h__1_355_);
            v_w_386_ = lean_ctor_get(v_expr_354_, 0);
            lean_inc(v_w_386_);
            v_n_387_ = lean_ctor_get(v_expr_354_, 2);
            lean_inc(v_n_387_);
            v_expr_388_ = lean_ctor_get(v_expr_354_, 3);
            lean_inc_ref(v_expr_388_);
            lean_dec_ref_known(v_expr_354_, 4);
            v___x_389_ = lean_apply_5(
                v_h__6_360_,
                v_w_353_,
                v_w_386_,
                v_n_387_,
                v_expr_388_,
                lean_box(0),
            );
            return v___x_389_;
        }
        7 => {
            let mut v_n_390_: *mut LeanObject = core::ptr::null_mut();
            let mut v_lhs_391_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rhs_392_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__10_364_);
            lean_dec(v_h__9_363_);
            lean_dec(v_h__7_361_);
            lean_dec(v_h__6_360_);
            lean_dec(v_h__5_359_);
            lean_dec(v_h__4_358_);
            lean_dec(v_h__3_357_);
            lean_dec(v_h__2_356_);
            lean_dec(v_h__1_355_);
            v_n_390_ = lean_ctor_get(v_expr_354_, 1);
            lean_inc(v_n_390_);
            v_lhs_391_ = lean_ctor_get(v_expr_354_, 2);
            lean_inc_ref(v_lhs_391_);
            v_rhs_392_ = lean_ctor_get(v_expr_354_, 3);
            lean_inc_ref(v_rhs_392_);
            lean_dec_ref_known(v_expr_354_, 4);
            v___x_393_ = lean_apply_4(v_h__8_362_, v_w_353_, v_n_390_, v_lhs_391_, v_rhs_392_);
            return v___x_393_;
        }
        8 => {
            let mut v_n_394_: *mut LeanObject = core::ptr::null_mut();
            let mut v_lhs_395_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rhs_396_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__10_364_);
            lean_dec(v_h__8_362_);
            lean_dec(v_h__7_361_);
            lean_dec(v_h__6_360_);
            lean_dec(v_h__5_359_);
            lean_dec(v_h__4_358_);
            lean_dec(v_h__3_357_);
            lean_dec(v_h__2_356_);
            lean_dec(v_h__1_355_);
            v_n_394_ = lean_ctor_get(v_expr_354_, 1);
            lean_inc(v_n_394_);
            v_lhs_395_ = lean_ctor_get(v_expr_354_, 2);
            lean_inc_ref(v_lhs_395_);
            v_rhs_396_ = lean_ctor_get(v_expr_354_, 3);
            lean_inc_ref(v_rhs_396_);
            lean_dec_ref_known(v_expr_354_, 4);
            v___x_397_ = lean_apply_4(v_h__9_363_, v_w_353_, v_n_394_, v_lhs_395_, v_rhs_396_);
            return v___x_397_;
        }
        _ => {
            let mut v_n_398_: *mut LeanObject = core::ptr::null_mut();
            let mut v_lhs_399_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rhs_400_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_363_);
            lean_dec(v_h__8_362_);
            lean_dec(v_h__7_361_);
            lean_dec(v_h__6_360_);
            lean_dec(v_h__5_359_);
            lean_dec(v_h__4_358_);
            lean_dec(v_h__3_357_);
            lean_dec(v_h__2_356_);
            lean_dec(v_h__1_355_);
            v_n_398_ = lean_ctor_get(v_expr_354_, 1);
            lean_inc(v_n_398_);
            v_lhs_399_ = lean_ctor_get(v_expr_354_, 2);
            lean_inc_ref(v_lhs_399_);
            v_rhs_400_ = lean_ctor_get(v_expr_354_, 3);
            lean_inc_ref(v_rhs_400_);
            lean_dec_ref_known(v_expr_354_, 4);
            v___x_401_ = lean_apply_4(v_h__10_364_, v_w_353_, v_n_398_, v_lhs_399_, v_rhs_400_);
            return v___x_401_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__15_splitter___redArg(
    mut v_op_402_: *mut LeanObject,
    mut v_h__1_403_: *mut LeanObject,
    mut v_h__2_404_: *mut LeanObject,
    mut v_h__3_405_: *mut LeanObject,
    mut v_h__4_406_: *mut LeanObject,
    mut v_h__5_407_: *mut LeanObject,
    mut v_h__6_408_: *mut LeanObject,
    mut v_h__7_409_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_op_402_) {
        0 => {
            let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_409_);
            lean_dec(v_h__6_408_);
            lean_dec(v_h__5_407_);
            lean_dec(v_h__4_406_);
            lean_dec(v_h__3_405_);
            lean_dec(v_h__2_404_);
            v___x_410_ = lean_box(0);
            v___x_411_ = lean_apply_1(v_h__1_403_, v___x_410_);
            return v___x_411_;
        }
        1 => {
            let mut v_n_412_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_409_);
            lean_dec(v_h__6_408_);
            lean_dec(v_h__5_407_);
            lean_dec(v_h__4_406_);
            lean_dec(v_h__3_405_);
            lean_dec(v_h__1_403_);
            v_n_412_ = lean_ctor_get(v_op_402_, 0);
            lean_inc(v_n_412_);
            lean_dec_ref_known(v_op_402_, 1);
            v___x_413_ = lean_apply_1(v_h__2_404_, v_n_412_);
            return v___x_413_;
        }
        2 => {
            let mut v_n_414_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_409_);
            lean_dec(v_h__6_408_);
            lean_dec(v_h__5_407_);
            lean_dec(v_h__4_406_);
            lean_dec(v_h__2_404_);
            lean_dec(v_h__1_403_);
            v_n_414_ = lean_ctor_get(v_op_402_, 0);
            lean_inc(v_n_414_);
            lean_dec_ref_known(v_op_402_, 1);
            v___x_415_ = lean_apply_1(v_h__3_405_, v_n_414_);
            return v___x_415_;
        }
        3 => {
            let mut v_n_416_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_409_);
            lean_dec(v_h__6_408_);
            lean_dec(v_h__5_407_);
            lean_dec(v_h__3_405_);
            lean_dec(v_h__2_404_);
            lean_dec(v_h__1_403_);
            v_n_416_ = lean_ctor_get(v_op_402_, 0);
            lean_inc(v_n_416_);
            lean_dec_ref_known(v_op_402_, 1);
            v___x_417_ = lean_apply_1(v_h__4_406_, v_n_416_);
            return v___x_417_;
        }
        4 => {
            let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_409_);
            lean_dec(v_h__6_408_);
            lean_dec(v_h__4_406_);
            lean_dec(v_h__3_405_);
            lean_dec(v_h__2_404_);
            lean_dec(v_h__1_403_);
            v___x_418_ = lean_box(0);
            v___x_419_ = lean_apply_1(v_h__5_407_, v___x_418_);
            return v___x_419_;
        }
        5 => {
            let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_409_);
            lean_dec(v_h__5_407_);
            lean_dec(v_h__4_406_);
            lean_dec(v_h__3_405_);
            lean_dec(v_h__2_404_);
            lean_dec(v_h__1_403_);
            v___x_420_ = lean_box(0);
            v___x_421_ = lean_apply_1(v_h__6_408_, v___x_420_);
            return v___x_421_;
        }
        _ => {
            let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__6_408_);
            lean_dec(v_h__5_407_);
            lean_dec(v_h__4_406_);
            lean_dec(v_h__3_405_);
            lean_dec(v_h__2_404_);
            lean_dec(v_h__1_403_);
            v___x_422_ = lean_box(0);
            v___x_423_ = lean_apply_1(v_h__7_409_, v___x_422_);
            return v___x_423_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__15_splitter(
    mut v_motive_424_: *mut LeanObject,
    mut v_op_425_: *mut LeanObject,
    mut v_h__1_426_: *mut LeanObject,
    mut v_h__2_427_: *mut LeanObject,
    mut v_h__3_428_: *mut LeanObject,
    mut v_h__4_429_: *mut LeanObject,
    mut v_h__5_430_: *mut LeanObject,
    mut v_h__6_431_: *mut LeanObject,
    mut v_h__7_432_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_op_425_) {
        0 => {
            let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_432_);
            lean_dec(v_h__6_431_);
            lean_dec(v_h__5_430_);
            lean_dec(v_h__4_429_);
            lean_dec(v_h__3_428_);
            lean_dec(v_h__2_427_);
            v___x_433_ = lean_box(0);
            v___x_434_ = lean_apply_1(v_h__1_426_, v___x_433_);
            return v___x_434_;
        }
        1 => {
            let mut v_n_435_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_432_);
            lean_dec(v_h__6_431_);
            lean_dec(v_h__5_430_);
            lean_dec(v_h__4_429_);
            lean_dec(v_h__3_428_);
            lean_dec(v_h__1_426_);
            v_n_435_ = lean_ctor_get(v_op_425_, 0);
            lean_inc(v_n_435_);
            lean_dec_ref_known(v_op_425_, 1);
            v___x_436_ = lean_apply_1(v_h__2_427_, v_n_435_);
            return v___x_436_;
        }
        2 => {
            let mut v_n_437_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_432_);
            lean_dec(v_h__6_431_);
            lean_dec(v_h__5_430_);
            lean_dec(v_h__4_429_);
            lean_dec(v_h__2_427_);
            lean_dec(v_h__1_426_);
            v_n_437_ = lean_ctor_get(v_op_425_, 0);
            lean_inc(v_n_437_);
            lean_dec_ref_known(v_op_425_, 1);
            v___x_438_ = lean_apply_1(v_h__3_428_, v_n_437_);
            return v___x_438_;
        }
        3 => {
            let mut v_n_439_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_432_);
            lean_dec(v_h__6_431_);
            lean_dec(v_h__5_430_);
            lean_dec(v_h__3_428_);
            lean_dec(v_h__2_427_);
            lean_dec(v_h__1_426_);
            v_n_439_ = lean_ctor_get(v_op_425_, 0);
            lean_inc(v_n_439_);
            lean_dec_ref_known(v_op_425_, 1);
            v___x_440_ = lean_apply_1(v_h__4_429_, v_n_439_);
            return v___x_440_;
        }
        4 => {
            let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_432_);
            lean_dec(v_h__6_431_);
            lean_dec(v_h__4_429_);
            lean_dec(v_h__3_428_);
            lean_dec(v_h__2_427_);
            lean_dec(v_h__1_426_);
            v___x_441_ = lean_box(0);
            v___x_442_ = lean_apply_1(v_h__5_430_, v___x_441_);
            return v___x_442_;
        }
        5 => {
            let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_432_);
            lean_dec(v_h__5_430_);
            lean_dec(v_h__4_429_);
            lean_dec(v_h__3_428_);
            lean_dec(v_h__2_427_);
            lean_dec(v_h__1_426_);
            v___x_443_ = lean_box(0);
            v___x_444_ = lean_apply_1(v_h__6_431_, v___x_443_);
            return v___x_444_;
        }
        _ => {
            let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__6_431_);
            lean_dec(v_h__5_430_);
            lean_dec(v_h__4_429_);
            lean_dec(v_h__3_428_);
            lean_dec(v_h__2_427_);
            lean_dec(v_h__1_426_);
            v___x_445_ = lean_box(0);
            v___x_446_ = lean_apply_1(v_h__7_432_, v___x_445_);
            return v___x_446_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg(
    mut v_op_447_: u8,
    mut v_h__1_448_: *mut LeanObject,
    mut v_h__2_449_: *mut LeanObject,
    mut v_h__3_450_: *mut LeanObject,
    mut v_h__4_451_: *mut LeanObject,
    mut v_h__5_452_: *mut LeanObject,
    mut v_h__6_453_: *mut LeanObject,
    mut v_h__7_454_: *mut LeanObject,
) -> *mut LeanObject {
    match v_op_447_ {
        0 => {
            let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_454_);
            lean_dec(v_h__6_453_);
            lean_dec(v_h__5_452_);
            lean_dec(v_h__4_451_);
            lean_dec(v_h__3_450_);
            lean_dec(v_h__2_449_);
            v___x_455_ = lean_box(0);
            v___x_456_ = lean_apply_1(v_h__1_448_, v___x_455_);
            return v___x_456_;
        }
        1 => {
            let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_454_);
            lean_dec(v_h__6_453_);
            lean_dec(v_h__5_452_);
            lean_dec(v_h__4_451_);
            lean_dec(v_h__3_450_);
            lean_dec(v_h__1_448_);
            v___x_457_ = lean_box(0);
            v___x_458_ = lean_apply_1(v_h__2_449_, v___x_457_);
            return v___x_458_;
        }
        2 => {
            let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_454_);
            lean_dec(v_h__6_453_);
            lean_dec(v_h__5_452_);
            lean_dec(v_h__4_451_);
            lean_dec(v_h__2_449_);
            lean_dec(v_h__1_448_);
            v___x_459_ = lean_box(0);
            v___x_460_ = lean_apply_1(v_h__3_450_, v___x_459_);
            return v___x_460_;
        }
        3 => {
            let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_454_);
            lean_dec(v_h__6_453_);
            lean_dec(v_h__5_452_);
            lean_dec(v_h__3_450_);
            lean_dec(v_h__2_449_);
            lean_dec(v_h__1_448_);
            v___x_461_ = lean_box(0);
            v___x_462_ = lean_apply_1(v_h__4_451_, v___x_461_);
            return v___x_462_;
        }
        4 => {
            let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_454_);
            lean_dec(v_h__6_453_);
            lean_dec(v_h__4_451_);
            lean_dec(v_h__3_450_);
            lean_dec(v_h__2_449_);
            lean_dec(v_h__1_448_);
            v___x_463_ = lean_box(0);
            v___x_464_ = lean_apply_1(v_h__5_452_, v___x_463_);
            return v___x_464_;
        }
        5 => {
            let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_454_);
            lean_dec(v_h__5_452_);
            lean_dec(v_h__4_451_);
            lean_dec(v_h__3_450_);
            lean_dec(v_h__2_449_);
            lean_dec(v_h__1_448_);
            v___x_465_ = lean_box(0);
            v___x_466_ = lean_apply_1(v_h__6_453_, v___x_465_);
            return v___x_466_;
        }
        _ => {
            let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__6_453_);
            lean_dec(v_h__5_452_);
            lean_dec(v_h__4_451_);
            lean_dec(v_h__3_450_);
            lean_dec(v_h__2_449_);
            lean_dec(v_h__1_448_);
            v___x_467_ = lean_box(0);
            v___x_468_ = lean_apply_1(v_h__7_454_, v___x_467_);
            return v___x_468_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg___boxed(
    mut v_op_469_: *mut LeanObject,
    mut v_h__1_470_: *mut LeanObject,
    mut v_h__2_471_: *mut LeanObject,
    mut v_h__3_472_: *mut LeanObject,
    mut v_h__4_473_: *mut LeanObject,
    mut v_h__5_474_: *mut LeanObject,
    mut v_h__6_475_: *mut LeanObject,
    mut v_h__7_476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_op_76__boxed_477_: u8 = 0;
    let mut v_res_478_: *mut LeanObject = core::ptr::null_mut();
    v_op_76__boxed_477_ = (lean_unbox(v_op_469_) as u8);
    v_res_478_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg(v_op_76__boxed_477_, v_h__1_470_, v_h__2_471_, v_h__3_472_, v_h__4_473_, v_h__5_474_, v_h__6_475_, v_h__7_476_);
    return v_res_478_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter(
    mut v_motive_479_: *mut LeanObject,
    mut v_op_480_: u8,
    mut v_h__1_481_: *mut LeanObject,
    mut v_h__2_482_: *mut LeanObject,
    mut v_h__3_483_: *mut LeanObject,
    mut v_h__4_484_: *mut LeanObject,
    mut v_h__5_485_: *mut LeanObject,
    mut v_h__6_486_: *mut LeanObject,
    mut v_h__7_487_: *mut LeanObject,
) -> *mut LeanObject {
    match v_op_480_ {
        0 => {
            let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_487_);
            lean_dec(v_h__6_486_);
            lean_dec(v_h__5_485_);
            lean_dec(v_h__4_484_);
            lean_dec(v_h__3_483_);
            lean_dec(v_h__2_482_);
            v___x_488_ = lean_box(0);
            v___x_489_ = lean_apply_1(v_h__1_481_, v___x_488_);
            return v___x_489_;
        }
        1 => {
            let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_487_);
            lean_dec(v_h__6_486_);
            lean_dec(v_h__5_485_);
            lean_dec(v_h__4_484_);
            lean_dec(v_h__3_483_);
            lean_dec(v_h__1_481_);
            v___x_490_ = lean_box(0);
            v___x_491_ = lean_apply_1(v_h__2_482_, v___x_490_);
            return v___x_491_;
        }
        2 => {
            let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_487_);
            lean_dec(v_h__6_486_);
            lean_dec(v_h__5_485_);
            lean_dec(v_h__4_484_);
            lean_dec(v_h__2_482_);
            lean_dec(v_h__1_481_);
            v___x_492_ = lean_box(0);
            v___x_493_ = lean_apply_1(v_h__3_483_, v___x_492_);
            return v___x_493_;
        }
        3 => {
            let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_487_);
            lean_dec(v_h__6_486_);
            lean_dec(v_h__5_485_);
            lean_dec(v_h__3_483_);
            lean_dec(v_h__2_482_);
            lean_dec(v_h__1_481_);
            v___x_494_ = lean_box(0);
            v___x_495_ = lean_apply_1(v_h__4_484_, v___x_494_);
            return v___x_495_;
        }
        4 => {
            let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_487_);
            lean_dec(v_h__6_486_);
            lean_dec(v_h__4_484_);
            lean_dec(v_h__3_483_);
            lean_dec(v_h__2_482_);
            lean_dec(v_h__1_481_);
            v___x_496_ = lean_box(0);
            v___x_497_ = lean_apply_1(v_h__5_485_, v___x_496_);
            return v___x_497_;
        }
        5 => {
            let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_487_);
            lean_dec(v_h__5_485_);
            lean_dec(v_h__4_484_);
            lean_dec(v_h__3_483_);
            lean_dec(v_h__2_482_);
            lean_dec(v_h__1_481_);
            v___x_498_ = lean_box(0);
            v___x_499_ = lean_apply_1(v_h__6_486_, v___x_498_);
            return v___x_499_;
        }
        _ => {
            let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__6_486_);
            lean_dec(v_h__5_485_);
            lean_dec(v_h__4_484_);
            lean_dec(v_h__3_483_);
            lean_dec(v_h__2_482_);
            lean_dec(v_h__1_481_);
            v___x_500_ = lean_box(0);
            v___x_501_ = lean_apply_1(v_h__7_487_, v___x_500_);
            return v___x_501_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___boxed(
    mut v_motive_502_: *mut LeanObject,
    mut v_op_503_: *mut LeanObject,
    mut v_h__1_504_: *mut LeanObject,
    mut v_h__2_505_: *mut LeanObject,
    mut v_h__3_506_: *mut LeanObject,
    mut v_h__4_507_: *mut LeanObject,
    mut v_h__5_508_: *mut LeanObject,
    mut v_h__6_509_: *mut LeanObject,
    mut v_h__7_510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_op_107__boxed_511_: u8 = 0;
    let mut v_res_512_: *mut LeanObject = core::ptr::null_mut();
    v_op_107__boxed_511_ = (lean_unbox(v_op_503_) as u8);
    v_res_512_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter(v_motive_502_, v_op_107__boxed_511_, v_h__1_504_, v_h__2_505_, v_h__3_506_, v_h__4_507_, v_h__5_508_, v_h__6_509_, v_h__7_510_);
    return v_res_512_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Var(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_ShiftRight(
            builtin,
        );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Append(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Replicate(
            builtin,
        );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Extract(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateLeft(
            builtin,
        );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateRight(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Mul(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Reverse(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Clz(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Cpop(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Var(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_ShiftRight(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Append(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Replicate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Extract(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateLeft(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateRight(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Mul(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Reverse(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Clz(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Cpop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(builtin);
}
