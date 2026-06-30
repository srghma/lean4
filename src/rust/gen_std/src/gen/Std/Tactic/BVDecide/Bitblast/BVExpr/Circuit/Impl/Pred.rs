// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Pred
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.GetLsbD Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_land, lean_nat_lor, lean_nat_mul, lean_nat_shiftr,
    lean_uint64_mix_hash, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Data::Bool::l_Bool_toNat;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::Basic::{
    l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg, l_Std_Sat_AIG_instHashableFanin_hash,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::{
    l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed,
    l_Std_Tactic_BVDecide_instHashableBVBit_hash,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Expr::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr,
    l_Std_Tactic_BVDecide_BVExpr_bitblast,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::GetLsbD::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD,
};
pub static l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 8) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,0 as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 8) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,1 as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5___lam__0 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__2___redArg(
    mut v_target_1249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_w_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: u8 = 0;
    v_w_1250_ = leanh::lean_ctor_get(v_target_1249_, 0);
    v_vec_1251_ = leanh::lean_ctor_get(v_target_1249_, 1);
    v_idx_1252_ = leanh::lean_ctor_get(v_target_1249_, 2);
    v___x_1253_ = lean_nat_dec_lt(v_idx_1252_, v_w_1250_);
    if v___x_1253_ == 0 {
        let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1254_ = leanh::lean_unsigned_to_nat(0);
        v___x_1255_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_1255_, 0, v___x_1254_);
        leanh::lean_ctor_set_uint8(
            v___x_1255_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v___x_1253_,
        );
        return v___x_1255_;
    } else {
        let mut v_ref_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1261_: u8 = 0;
        v_ref_1256_ = lean_array_fget_borrowed(v_vec_1251_, v_idx_1252_);
        v___x_1257_ = leanh::lean_unsigned_to_nat(1);
        v___x_1258_ = lean_nat_shiftr(v_ref_1256_, v___x_1257_);
        v___x_1259_ = lean_nat_land(v___x_1257_, v_ref_1256_);
        v___x_1260_ = leanh::lean_unsigned_to_nat(0);
        v___x_1261_ = lean_nat_dec_eq(v___x_1259_, v___x_1260_);
        leanh::lean_dec(v___x_1259_);
        if v___x_1261_ == 0 {
            let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1262_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
            leanh::lean_ctor_set(v___x_1262_, 0, v___x_1258_);
            leanh::lean_ctor_set_uint8(
                v___x_1262_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                v___x_1253_,
            );
            return v___x_1262_;
        } else {
            let mut v___x_1263_: u8 = 0;
            let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1263_ = 0;
            v___x_1264_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
            leanh::lean_ctor_set(v___x_1264_, 0, v___x_1258_);
            leanh::lean_ctor_set_uint8(
                v___x_1264_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                v___x_1263_,
            );
            return v___x_1264_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__2___redArg___boxed(
    mut v_target_1265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1266_ = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__2___redArg(v_target_1265_);
    leanh::lean_dec_ref(v_target_1265_);
    return v_res_1266_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__2(
    mut v_aig_1267_: *mut leanh::LeanObject,
    mut v_target_1268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__2___redArg(v_target_1268_);
    return v___x_1269_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__2___boxed(
    mut v_aig_1270_: *mut leanh::LeanObject,
    mut v_target_1271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1272_ = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__2(v_aig_1270_, v_target_1271_);
    leanh::lean_dec_ref(v_target_1271_);
    leanh::lean_dec_ref(v_aig_1270_);
    return v_res_1272_;
}
pub unsafe fn l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8_spec__12(
    mut v_x_1273_: *mut leanh::LeanObject,
) -> u64 {
    match leanh::lean_obj_tag(v_x_1273_) {
        0 => {
            let mut v___x_1274_: u64 = 0;
            v___x_1274_ = 0u64;
            return v___x_1274_;
        }
        1 => {
            let mut v_idx_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1276_: u64 = 0;
            let mut v___x_1277_: u64 = 0;
            let mut v___x_1278_: u64 = 0;
            v_idx_1275_ = leanh::lean_ctor_get(v_x_1273_, 0);
            v___x_1276_ = 1u64;
            v___x_1277_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_idx_1275_);
            v___x_1278_ = lean_uint64_mix_hash(v___x_1276_, v___x_1277_);
            return v___x_1278_;
        }
        _ => {
            let mut v_l_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1281_: u64 = 0;
            let mut v___x_1282_: u64 = 0;
            let mut v___x_1283_: u64 = 0;
            let mut v___x_1284_: u64 = 0;
            let mut v___x_1285_: u64 = 0;
            v_l_1279_ = leanh::lean_ctor_get(v_x_1273_, 0);
            v_r_1280_ = leanh::lean_ctor_get(v_x_1273_, 1);
            v___x_1281_ = 2u64;
            v___x_1282_ = l_Std_Sat_AIG_instHashableFanin_hash(v_l_1279_);
            v___x_1283_ = lean_uint64_mix_hash(v___x_1281_, v___x_1282_);
            v___x_1284_ = l_Std_Sat_AIG_instHashableFanin_hash(v_r_1280_);
            v___x_1285_ = lean_uint64_mix_hash(v___x_1283_, v___x_1284_);
            return v___x_1285_;
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8_spec__12___boxed(
    mut v_x_1286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1287_: u64 = 0;
    let mut v_r_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1287_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8_spec__12(v_x_1286_);
    leanh::lean_dec(v_x_1286_);
    v_r_1288_ = leanh::lean_box_uint64(v_res_1287_);
    return v_r_1288_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8_spec__13___redArg(
    mut v_a_1289_: *mut leanh::LeanObject,
    mut v_x_1290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: u8 = 0;
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1290_) == 0 {
                    leanh::lean_dec(v_a_1289_);
                    v___x_1291_ = leanh::lean_box(0);
                    return v___x_1291_;
                } else {
                    v_key_1292_ = leanh::lean_ctor_get(v_x_1290_, 0);
                    leanh::lean_inc(v_key_1292_);
                    v_value_1293_ = leanh::lean_ctor_get(v_x_1290_, 1);
                    leanh::lean_inc(v_value_1293_);
                    v_tail_1294_ = leanh::lean_ctor_get(v_x_1290_, 2);
                    leanh::lean_inc(v_tail_1294_);
                    leanh::lean_dec_ref_known(v_x_1290_, 3);
                    v___x_1295_ = leanh::lean_alloc_closure(
                        l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed
                            as *mut core::ffi::c_void,
                        2,
                        0,
                    );
                    leanh::lean_inc(v_a_1289_);
                    v___x_1296_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(
                        v___x_1295_,
                        v_key_1292_,
                        v_a_1289_,
                    );
                    if v___x_1296_ == 0 {
                        leanh::lean_dec(v_value_1293_);
                        v_x_1290_ = v_tail_1294_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1294_);
                        leanh::lean_dec(v_a_1289_);
                        v___x_1298_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1298_, 0, v_value_1293_);
                        return v___x_1298_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8___redArg(
    mut v_m_1299_: *mut leanh::LeanObject,
    mut v_a_1300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: u64 = 0;
    let mut v___x_1304_: u64 = 0;
    let mut v___x_1305_: u64 = 0;
    let mut v_fold_1306_: u64 = 0;
    let mut v___x_1307_: u64 = 0;
    let mut v___x_1308_: u64 = 0;
    let mut v___x_1309_: u64 = 0;
    let mut v___x_1310_: usize = 0;
    let mut v___x_1311_: usize = 0;
    let mut v___x_1312_: usize = 0;
    let mut v___x_1313_: usize = 0;
    let mut v___x_1314_: usize = 0;
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1301_ = leanh::lean_ctor_get(v_m_1299_, 1);
    v___x_1302_ = lean_array_get_size(v_buckets_1301_);
    v___x_1303_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8_spec__12(v_a_1300_);
    v___x_1304_ = 32u64;
    v___x_1305_ = lean_uint64_shift_right(v___x_1303_, v___x_1304_);
    v_fold_1306_ = lean_uint64_xor(v___x_1303_, v___x_1305_);
    v___x_1307_ = 16u64;
    v___x_1308_ = lean_uint64_shift_right(v_fold_1306_, v___x_1307_);
    v___x_1309_ = lean_uint64_xor(v_fold_1306_, v___x_1308_);
    v___x_1310_ = lean_uint64_to_usize(v___x_1309_);
    v___x_1311_ = lean_usize_of_nat(v___x_1302_);
    v___x_1312_ = 1usize;
    v___x_1313_ = lean_usize_sub(v___x_1311_, v___x_1312_);
    v___x_1314_ = lean_usize_land(v___x_1310_, v___x_1313_);
    v___x_1315_ = lean_array_uget_borrowed(v_buckets_1301_, v___x_1314_);
    leanh::lean_inc(v___x_1315_);
    v___x_1316_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8_spec__13___redArg(v_a_1300_, v___x_1315_);
    return v___x_1316_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8___redArg___boxed(
    mut v_m_1317_: *mut leanh::LeanObject,
    mut v_a_1318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1319_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8___redArg(v_m_1317_, v_a_1318_);
    leanh::lean_dec_ref(v_m_1317_);
    return v_res_1319_;
}
pub unsafe fn l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__9(
    mut v_aig_1320_: *mut leanh::LeanObject,
    mut v_ref_1321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_gate_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1323_: u8 = 0;
    let mut v_decls_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_gate_1322_ = leanh::lean_ctor_get(v_ref_1321_, 0);
    v_invert_1323_ = leanh::lean_ctor_get_uint8(
        v_ref_1321_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
    );
    v_decls_1324_ = leanh::lean_ctor_get(v_aig_1320_, 0);
    v_decl_1325_ = lean_array_fget_borrowed(v_decls_1324_, v_gate_1322_);
    if leanh::lean_obj_tag(v_decl_1325_) == 0 {
        let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1326_ = leanh::lean_box((v_invert_1323_) as usize);
        v___x_1327_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1327_, 0, v___x_1326_);
        return v___x_1327_;
    } else {
        let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1328_ = leanh::lean_box(0);
        return v___x_1328_;
    }
}
pub unsafe fn l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__9___boxed(
    mut v_aig_1329_: *mut leanh::LeanObject,
    mut v_ref_1330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1331_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__9(v_aig_1329_, v_ref_1330_);
    leanh::lean_dec_ref(v_ref_1330_);
    leanh::lean_dec_ref(v_aig_1329_);
    return v_res_1331_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__18___redArg(
    mut v_a_1332_: *mut leanh::LeanObject,
    mut v_b_1333_: *mut leanh::LeanObject,
    mut v_x_1334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1340_: u8 = 0;
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: u8 = 0;
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1334_) == 0 {
                    leanh::lean_dec(v_b_1333_);
                    leanh::lean_dec(v_a_1332_);
                    return v_x_1334_;
                } else {
                    v_key_1335_ = leanh::lean_ctor_get(v_x_1334_, 0);
                    v_value_1336_ = leanh::lean_ctor_get(v_x_1334_, 1);
                    v_tail_1337_ = leanh::lean_ctor_get(v_x_1334_, 2);
                    v_isSharedCheck_1350_ = (!leanh::lean_is_exclusive(v_x_1334_)) as u8;
                    if v_isSharedCheck_1350_ == 0 {
                        v___x_1339_ = v_x_1334_;
                        v_isShared_1340_ = v_isSharedCheck_1350_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1337_);
                        leanh::lean_inc(v_value_1336_);
                        leanh::lean_inc(v_key_1335_);
                        leanh::lean_dec(v_x_1334_);
                        v___x_1339_ = leanh::lean_box(0);
                        v_isShared_1340_ = v_isSharedCheck_1350_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1341_ = leanh::lean_alloc_closure(
                    l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed as *mut core::ffi::c_void,
                    2,
                    0,
                );
                leanh::lean_inc(v_a_1332_);
                leanh::lean_inc(v_key_1335_);
                v___x_1342_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(
                    v___x_1341_,
                    v_key_1335_,
                    v_a_1332_,
                );
                if v___x_1342_ == 0 {
                    v___x_1343_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__18___redArg(v_a_1332_, v_b_1333_, v_tail_1337_);
                    if v_isShared_1340_ == 0 {
                        leanh::lean_ctor_set(v___x_1339_, 2, v___x_1343_);
                        v___x_1345_ = v___x_1339_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1346_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_key_1335_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_value_1336_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 2, v___x_1343_);
                        v___x_1345_ = v_reuseFailAlloc_1346_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_1336_);
                    leanh::lean_dec(v_key_1335_);
                    if v_isShared_1340_ == 0 {
                        leanh::lean_ctor_set(v___x_1339_, 1, v_b_1333_);
                        leanh::lean_ctor_set(v___x_1339_, 0, v_a_1332_);
                        v___x_1348_ = v___x_1339_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1349_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1332_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_b_1333_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_tail_1337_);
                        v___x_1348_ = v_reuseFailAlloc_1349_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1345_;
            }
            3 => {
                return v___x_1348_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__16___redArg(
    mut v_a_1351_: *mut leanh::LeanObject,
    mut v_x_1352_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1353_: u8 = 0;
    let mut v_key_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1352_) == 0 {
                    leanh::lean_dec(v_a_1351_);
                    v___x_1353_ = 0;
                    return v___x_1353_;
                } else {
                    v_key_1354_ = leanh::lean_ctor_get(v_x_1352_, 0);
                    leanh::lean_inc(v_key_1354_);
                    v_tail_1355_ = leanh::lean_ctor_get(v_x_1352_, 2);
                    leanh::lean_inc(v_tail_1355_);
                    leanh::lean_dec_ref_known(v_x_1352_, 3);
                    v___x_1356_ = leanh::lean_alloc_closure(
                        l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed
                            as *mut core::ffi::c_void,
                        2,
                        0,
                    );
                    leanh::lean_inc(v_a_1351_);
                    v___x_1357_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(
                        v___x_1356_,
                        v_key_1354_,
                        v_a_1351_,
                    );
                    if v___x_1357_ == 0 {
                        v_x_1352_ = v_tail_1355_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1355_);
                        leanh::lean_dec(v_a_1351_);
                        return v___x_1357_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__16___redArg___boxed(
    mut v_a_1359_: *mut leanh::LeanObject,
    mut v_x_1360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1361_: u8 = 0;
    let mut v_r_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1361_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__16___redArg(v_a_1359_, v_x_1360_);
    v_r_1362_ = leanh::lean_box((v_res_1361_) as usize);
    return v_r_1362_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17_spec__21_spec__24___redArg(
    mut v_x_1363_: *mut leanh::LeanObject,
    mut v_x_1364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1370_: u8 = 0;
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: u64 = 0;
    let mut v___x_1373_: u64 = 0;
    let mut v___x_1374_: u64 = 0;
    let mut v_fold_1375_: u64 = 0;
    let mut v___x_1376_: u64 = 0;
    let mut v___x_1377_: u64 = 0;
    let mut v___x_1378_: u64 = 0;
    let mut v___x_1379_: usize = 0;
    let mut v___x_1380_: usize = 0;
    let mut v___x_1381_: usize = 0;
    let mut v___x_1382_: usize = 0;
    let mut v___x_1383_: usize = 0;
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1390_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1364_) == 0 {
                    return v_x_1363_;
                } else {
                    v_key_1365_ = leanh::lean_ctor_get(v_x_1364_, 0);
                    v_value_1366_ = leanh::lean_ctor_get(v_x_1364_, 1);
                    v_tail_1367_ = leanh::lean_ctor_get(v_x_1364_, 2);
                    v_isSharedCheck_1390_ = (!leanh::lean_is_exclusive(v_x_1364_)) as u8;
                    if v_isSharedCheck_1390_ == 0 {
                        v___x_1369_ = v_x_1364_;
                        v_isShared_1370_ = v_isSharedCheck_1390_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1367_);
                        leanh::lean_inc(v_value_1366_);
                        leanh::lean_inc(v_key_1365_);
                        leanh::lean_dec(v_x_1364_);
                        v___x_1369_ = leanh::lean_box(0);
                        v_isShared_1370_ = v_isSharedCheck_1390_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1371_ = lean_array_get_size(v_x_1363_);
                v___x_1372_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8_spec__12(v_key_1365_);
                v___x_1373_ = 32u64;
                v___x_1374_ = lean_uint64_shift_right(v___x_1372_, v___x_1373_);
                v_fold_1375_ = lean_uint64_xor(v___x_1372_, v___x_1374_);
                v___x_1376_ = 16u64;
                v___x_1377_ = lean_uint64_shift_right(v_fold_1375_, v___x_1376_);
                v___x_1378_ = lean_uint64_xor(v_fold_1375_, v___x_1377_);
                v___x_1379_ = lean_uint64_to_usize(v___x_1378_);
                v___x_1380_ = lean_usize_of_nat(v___x_1371_);
                v___x_1381_ = 1usize;
                v___x_1382_ = lean_usize_sub(v___x_1380_, v___x_1381_);
                v___x_1383_ = lean_usize_land(v___x_1379_, v___x_1382_);
                v___x_1384_ = lean_array_uget_borrowed(v_x_1363_, v___x_1383_);
                leanh::lean_inc(v___x_1384_);
                if v_isShared_1370_ == 0 {
                    leanh::lean_ctor_set(v___x_1369_, 2, v___x_1384_);
                    v___x_1386_ = v___x_1369_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1389_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_key_1365_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_value_1366_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 2, v___x_1384_);
                    v___x_1386_ = v_reuseFailAlloc_1389_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1387_ = lean_array_uset(v_x_1363_, v___x_1383_, v___x_1386_);
                v_x_1363_ = v___x_1387_;
                v_x_1364_ = v_tail_1367_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17_spec__21___redArg(
    mut v_i_1391_: *mut leanh::LeanObject,
    mut v_source_1392_: *mut leanh::LeanObject,
    mut v_target_1393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: u8 = 0;
    let mut v_es_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1394_ = lean_array_get_size(v_source_1392_);
                v___x_1395_ = lean_nat_dec_lt(v_i_1391_, v___x_1394_);
                if v___x_1395_ == 0 {
                    leanh::lean_dec_ref(v_source_1392_);
                    leanh::lean_dec(v_i_1391_);
                    return v_target_1393_;
                } else {
                    v_es_1396_ = lean_array_fget(v_source_1392_, v_i_1391_);
                    v___x_1397_ = leanh::lean_box(0);
                    v_source_1398_ = lean_array_fset(v_source_1392_, v_i_1391_, v___x_1397_);
                    v_target_1399_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17_spec__21_spec__24___redArg(v_target_1393_, v_es_1396_);
                    v___x_1400_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1401_ = lean_nat_add(v_i_1391_, v___x_1400_);
                    leanh::lean_dec(v_i_1391_);
                    v_i_1391_ = v___x_1401_;
                    v_source_1392_ = v_source_1398_;
                    v_target_1393_ = v_target_1399_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17___redArg(
    mut v_data_1403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = lean_array_get_size(v_data_1403_);
    v___x_1405_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1406_ = lean_nat_mul(v___x_1404_, v___x_1405_);
    v___x_1407_ = leanh::lean_unsigned_to_nat(0);
    v___x_1408_ = leanh::lean_box(0);
    v___x_1409_ = lean_mk_array(v_nbuckets_1406_, v___x_1408_);
    v___x_1410_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17_spec__21___redArg(v___x_1407_, v_data_1403_, v___x_1409_);
    return v___x_1410_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10___redArg(
    mut v_m_1411_: *mut leanh::LeanObject,
    mut v_a_1412_: *mut leanh::LeanObject,
    mut v_b_1413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1418_: u8 = 0;
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: u64 = 0;
    let mut v___x_1421_: u64 = 0;
    let mut v___x_1422_: u64 = 0;
    let mut v_fold_1423_: u64 = 0;
    let mut v___x_1424_: u64 = 0;
    let mut v___x_1425_: u64 = 0;
    let mut v___x_1426_: u64 = 0;
    let mut v___x_1427_: usize = 0;
    let mut v___x_1428_: usize = 0;
    let mut v___x_1429_: usize = 0;
    let mut v___x_1430_: usize = 0;
    let mut v___x_1431_: usize = 0;
    let mut v_bkt_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: u8 = 0;
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: u8 = 0;
    let mut v_val_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1458_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1414_ = leanh::lean_ctor_get(v_m_1411_, 0);
                v_buckets_1415_ = leanh::lean_ctor_get(v_m_1411_, 1);
                v_isSharedCheck_1458_ = (!leanh::lean_is_exclusive(v_m_1411_)) as u8;
                if v_isSharedCheck_1458_ == 0 {
                    v___x_1417_ = v_m_1411_;
                    v_isShared_1418_ = v_isSharedCheck_1458_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1415_);
                    leanh::lean_inc(v_size_1414_);
                    leanh::lean_dec(v_m_1411_);
                    v___x_1417_ = leanh::lean_box(0);
                    v_isShared_1418_ = v_isSharedCheck_1458_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1419_ = lean_array_get_size(v_buckets_1415_);
                v___x_1420_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8_spec__12(v_a_1412_);
                v___x_1421_ = 32u64;
                v___x_1422_ = lean_uint64_shift_right(v___x_1420_, v___x_1421_);
                v_fold_1423_ = lean_uint64_xor(v___x_1420_, v___x_1422_);
                v___x_1424_ = 16u64;
                v___x_1425_ = lean_uint64_shift_right(v_fold_1423_, v___x_1424_);
                v___x_1426_ = lean_uint64_xor(v_fold_1423_, v___x_1425_);
                v___x_1427_ = lean_uint64_to_usize(v___x_1426_);
                v___x_1428_ = lean_usize_of_nat(v___x_1419_);
                v___x_1429_ = 1usize;
                v___x_1430_ = lean_usize_sub(v___x_1428_, v___x_1429_);
                v___x_1431_ = lean_usize_land(v___x_1427_, v___x_1430_);
                v_bkt_1432_ = lean_array_uget_borrowed(v_buckets_1415_, v___x_1431_);
                leanh::lean_inc(v_bkt_1432_);
                leanh::lean_inc(v_a_1412_);
                v___x_1433_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__16___redArg(v_a_1412_, v_bkt_1432_);
                if v___x_1433_ == 0 {
                    v___x_1434_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1435_ = lean_nat_add(v_size_1414_, v___x_1434_);
                    leanh::lean_dec(v_size_1414_);
                    leanh::lean_inc(v_bkt_1432_);
                    v___x_1436_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1436_, 0, v_a_1412_);
                    leanh::lean_ctor_set(v___x_1436_, 1, v_b_1413_);
                    leanh::lean_ctor_set(v___x_1436_, 2, v_bkt_1432_);
                    v_buckets_x27_1437_ =
                        lean_array_uset(v_buckets_1415_, v___x_1431_, v___x_1436_);
                    v___x_1438_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1439_ = lean_nat_mul(v_size_x27_1435_, v___x_1438_);
                    v___x_1440_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1441_ = lean_nat_div(v___x_1439_, v___x_1440_);
                    leanh::lean_dec(v___x_1439_);
                    v___x_1442_ = lean_array_get_size(v_buckets_x27_1437_);
                    v___x_1443_ = lean_nat_dec_le(v___x_1441_, v___x_1442_);
                    leanh::lean_dec(v___x_1441_);
                    if v___x_1443_ == 0 {
                        v_val_1444_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17___redArg(v_buckets_x27_1437_);
                        if v_isShared_1418_ == 0 {
                            leanh::lean_ctor_set(v___x_1417_, 1, v_val_1444_);
                            leanh::lean_ctor_set(v___x_1417_, 0, v_size_x27_1435_);
                            v___x_1446_ = v___x_1417_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1447_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1447_,
                                0,
                                v_size_x27_1435_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_val_1444_);
                            v___x_1446_ = v_reuseFailAlloc_1447_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1418_ == 0 {
                            leanh::lean_ctor_set(v___x_1417_, 1, v_buckets_x27_1437_);
                            leanh::lean_ctor_set(v___x_1417_, 0, v_size_x27_1435_);
                            v___x_1449_ = v___x_1417_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1450_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1450_,
                                0,
                                v_size_x27_1435_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1450_,
                                1,
                                v_buckets_x27_1437_,
                            );
                            v___x_1449_ = v_reuseFailAlloc_1450_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_1432_);
                    v___x_1451_ = leanh::lean_box(0);
                    v_buckets_x27_1452_ =
                        lean_array_uset(v_buckets_1415_, v___x_1431_, v___x_1451_);
                    v___x_1453_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__18___redArg(v_a_1412_, v_b_1413_, v_bkt_1432_);
                    v___x_1454_ = lean_array_uset(v_buckets_x27_1452_, v___x_1431_, v___x_1453_);
                    if v_isShared_1418_ == 0 {
                        leanh::lean_ctor_set(v___x_1417_, 1, v___x_1454_);
                        v___x_1456_ = v___x_1417_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1457_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_size_1414_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1457_, 1, v___x_1454_);
                        v___x_1456_ = v_reuseFailAlloc_1457_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1446_;
            }
            3 => {
                return v___x_1449_;
            }
            4 => {
                return v___x_1456_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6(
    mut v_aig_1462_: *mut leanh::LeanObject,
    mut v_input_1463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1468_: u8 = 0;
    let mut v_decls_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1473_: u8 = 0;
    let mut v_gate_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1475_: u8 = 0;
    let mut v_gate_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1477_: u8 = 0;
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1491_: u8 = 0;
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1496_: u8 = 0;
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsVal_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhsVal_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1509_: u8 = 0;
    let mut v_val_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: u8 = 0;
    let mut v_val_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: u8 = 0;
    let mut v_val_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: u8 = 0;
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: u8 = 0;
    let mut v_g_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1529_: u8 = 0;
    let mut v_unused_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1534_: u8 = 0;
    let mut v_val_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: u8 = 0;
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1544_: u8 = 0;
    let mut v_unused_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1547_: u8 = 0;
    let mut v_isSharedCheck_1548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_1464_ = leanh::lean_ctor_get(v_input_1463_, 0);
                v_rhs_1465_ = leanh::lean_ctor_get(v_input_1463_, 1);
                v_isSharedCheck_1548_ = (!leanh::lean_is_exclusive(v_input_1463_)) as u8;
                if v_isSharedCheck_1548_ == 0 {
                    v___x_1467_ = v_input_1463_;
                    v_isShared_1468_ = v_isSharedCheck_1548_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rhs_1465_);
                    leanh::lean_inc(v_lhs_1464_);
                    leanh::lean_dec(v_input_1463_);
                    v___x_1467_ = leanh::lean_box(0);
                    v_isShared_1468_ = v_isSharedCheck_1548_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_decls_1469_ = leanh::lean_ctor_get(v_aig_1462_, 0);
                v_cache_1470_ = leanh::lean_ctor_get(v_aig_1462_, 1);
                v_isSharedCheck_1547_ = (!leanh::lean_is_exclusive(v_aig_1462_)) as u8;
                if v_isSharedCheck_1547_ == 0 {
                    v___x_1472_ = v_aig_1462_;
                    v_isShared_1473_ = v_isSharedCheck_1547_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_cache_1470_);
                    leanh::lean_inc(v_decls_1469_);
                    leanh::lean_dec(v_aig_1462_);
                    v___x_1472_ = leanh::lean_box(0);
                    v_isShared_1473_ = v_isSharedCheck_1547_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_1474_ = leanh::lean_ctor_get(v_lhs_1464_, 0);
                leanh::lean_inc(v_gate_1474_);
                v_invert_1475_ = leanh::lean_ctor_get_uint8(
                    v_lhs_1464_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_gate_1476_ = leanh::lean_ctor_get(v_rhs_1465_, 0);
                v_invert_1477_ = leanh::lean_ctor_get_uint8(
                    v_rhs_1465_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v___x_1478_ = leanh::lean_unsigned_to_nat(2);
                v___x_1479_ = lean_nat_mul(v_gate_1474_, v___x_1478_);
                v___x_1480_ = l_Bool_toNat(v_invert_1475_);
                v___x_1481_ = lean_nat_lor(v___x_1479_, v___x_1480_);
                leanh::lean_dec(v___x_1480_);
                leanh::lean_dec(v___x_1479_);
                v___x_1482_ = lean_nat_mul(v_gate_1476_, v___x_1478_);
                v___x_1483_ = l_Bool_toNat(v_invert_1477_);
                v___x_1484_ = lean_nat_lor(v___x_1482_, v___x_1483_);
                leanh::lean_dec(v___x_1483_);
                leanh::lean_dec(v___x_1482_);
                if v_isShared_1468_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1467_, 2);
                    leanh::lean_ctor_set(v___x_1467_, 1, v___x_1484_);
                    leanh::lean_ctor_set(v___x_1467_, 0, v___x_1481_);
                    v_decl_1486_ = v___x_1467_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1546_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1481_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___x_1484_);
                    v_decl_1486_ = v_reuseFailAlloc_1546_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v_decl_1486_);
                v___x_1487_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8___redArg(v_cache_1470_, v_decl_1486_);
                if leanh::lean_obj_tag(v___x_1487_) == 0 {
                    leanh::lean_inc(v_gate_1476_);
                    leanh::lean_inc_ref(v_cache_1470_);
                    leanh::lean_inc_ref(v_decls_1469_);
                    if v_isShared_1473_ == 0 {
                        v___x_1489_ = v___x_1472_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1531_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_decls_1469_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_cache_1470_);
                        v___x_1489_ = v_reuseFailAlloc_1531_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_decl_1486_);
                    leanh::lean_dec(v_gate_1474_);
                    leanh::lean_dec_ref(v_lhs_1464_);
                    v_isSharedCheck_1544_ = (!leanh::lean_is_exclusive(v_rhs_1465_)) as u8;
                    if v_isSharedCheck_1544_ == 0 {
                        v_unused_1545_ = leanh::lean_ctor_get(v_rhs_1465_, 0);
                        leanh::lean_dec(v_unused_1545_);
                        v___x_1533_ = v_rhs_1465_;
                        v_isShared_1534_ = v_isSharedCheck_1544_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_dec(v_rhs_1465_);
                        v___x_1533_ = leanh::lean_box(0);
                        v_isShared_1534_ = v_isSharedCheck_1544_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                v_lhsVal_1505_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__9(v___x_1489_, v_lhs_1464_);
                leanh::lean_dec_ref(v_lhs_1464_);
                v_rhsVal_1506_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__9(v___x_1489_, v_rhs_1465_);
                v_isSharedCheck_1529_ = (!leanh::lean_is_exclusive(v_rhs_1465_)) as u8;
                if v_isSharedCheck_1529_ == 0 {
                    v_unused_1530_ = leanh::lean_ctor_get(v_rhs_1465_, 0);
                    leanh::lean_dec(v_unused_1530_);
                    v___x_1508_ = v_rhs_1465_;
                    v_isShared_1509_ = v_isSharedCheck_1529_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_dec(v_rhs_1465_);
                    v___x_1508_ = leanh::lean_box(0);
                    v_isShared_1509_ = v_isSharedCheck_1529_;
                    state = 9;
                    continue;
                }
            }
            5 => {
                v___x_1492_ = leanh::lean_unsigned_to_nat(0);
                v_ref_1493_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v_ref_1493_, 0, v___x_1492_);
                leanh::lean_ctor_set_uint8(
                    v_ref_1493_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___y_1491_,
                );
                v___x_1494_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1494_, 0, v___x_1489_);
                leanh::lean_ctor_set(v___x_1494_, 1, v_ref_1493_);
                return v___x_1494_;
            }
            6 => {
                if v___y_1496_ == 0 {
                    leanh::lean_dec(v_gate_1474_);
                    v___y_1491_ = v___y_1496_;
                    state = 5;
                    continue;
                } else {
                    v___x_1497_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1497_, 0, v_gate_1474_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1497_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_invert_1475_,
                    );
                    v___x_1498_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1498_, 0, v___x_1489_);
                    leanh::lean_ctor_set(v___x_1498_, 1, v___x_1497_);
                    return v___x_1498_;
                }
            }
            7 => {
                v___x_1500_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1500_, 0, v_gate_1476_);
                leanh::lean_ctor_set_uint8(
                    v___x_1500_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_invert_1477_,
                );
                v___x_1501_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1501_, 0, v___x_1489_);
                leanh::lean_ctor_set(v___x_1501_, 1, v___x_1500_);
                return v___x_1501_;
            }
            8 => {
                v_ref_1503_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6___closed__0;
                v___x_1504_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1504_, 0, v___x_1489_);
                leanh::lean_ctor_set(v___x_1504_, 1, v_ref_1503_);
                return v___x_1504_;
            }
            9 => {
                if leanh::lean_obj_tag(v_lhsVal_1505_) == 1 {
                    leanh::lean_del_object(v___x_1508_);
                    leanh::lean_dec_ref(v_decl_1486_);
                    leanh::lean_dec(v_gate_1474_);
                    leanh::lean_dec_ref(v_cache_1470_);
                    leanh::lean_dec_ref(v_decls_1469_);
                    v_val_1510_ = leanh::lean_ctor_get(v_lhsVal_1505_, 0);
                    leanh::lean_inc(v_val_1510_);
                    leanh::lean_dec_ref_known(v_lhsVal_1505_, 1);
                    v___x_1511_ = (leanh::lean_unbox(v_val_1510_) as u8);
                    leanh::lean_dec(v_val_1510_);
                    if v___x_1511_ == 0 {
                        leanh::lean_dec(v_rhsVal_1506_);
                        leanh::lean_dec(v_gate_1476_);
                        state = 8;
                        continue;
                    } else {
                        if leanh::lean_obj_tag(v_rhsVal_1506_) == 1 {
                            v_val_1512_ = leanh::lean_ctor_get(v_rhsVal_1506_, 0);
                            leanh::lean_inc(v_val_1512_);
                            leanh::lean_dec_ref_known(v_rhsVal_1506_, 1);
                            v___x_1513_ = (leanh::lean_unbox(v_val_1512_) as u8);
                            leanh::lean_dec(v_val_1512_);
                            if v___x_1513_ == 0 {
                                leanh::lean_dec(v_gate_1476_);
                                state = 8;
                                continue;
                            } else {
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_rhsVal_1506_);
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_lhsVal_1505_);
                    if leanh::lean_obj_tag(v_rhsVal_1506_) == 1 {
                        leanh::lean_dec_ref(v_decl_1486_);
                        leanh::lean_dec(v_gate_1476_);
                        leanh::lean_dec_ref(v_cache_1470_);
                        leanh::lean_dec_ref(v_decls_1469_);
                        v_val_1514_ = leanh::lean_ctor_get(v_rhsVal_1506_, 0);
                        leanh::lean_inc(v_val_1514_);
                        leanh::lean_dec_ref_known(v_rhsVal_1506_, 1);
                        v___x_1515_ = (leanh::lean_unbox(v_val_1514_) as u8);
                        leanh::lean_dec(v_val_1514_);
                        if v___x_1515_ == 0 {
                            leanh::lean_del_object(v___x_1508_);
                            leanh::lean_dec(v_gate_1474_);
                            state = 8;
                            continue;
                        } else {
                            if v_isShared_1509_ == 0 {
                                leanh::lean_ctor_set(v___x_1508_, 0, v_gate_1474_);
                                v___x_1517_ = v___x_1508_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_1519_ =
                                    leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1519_,
                                    0,
                                    v_gate_1474_,
                                );
                                v___x_1517_ = v_reuseFailAlloc_1519_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_rhsVal_1506_);
                        v___x_1520_ = lean_nat_dec_eq(v_gate_1474_, v_gate_1476_);
                        leanh::lean_dec(v_gate_1476_);
                        if v___x_1520_ == 0 {
                            leanh::lean_dec_ref(v___x_1489_);
                            leanh::lean_dec(v_gate_1474_);
                            v_g_1521_ = lean_array_get_size(v_decls_1469_);
                            leanh::lean_inc_ref(v_decl_1486_);
                            v_cache_1522_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10___redArg(v_cache_1470_, v_decl_1486_, v_g_1521_);
                            v_decls_1523_ = lean_array_push(v_decls_1469_, v_decl_1486_);
                            v___x_1524_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1524_, 0, v_decls_1523_);
                            leanh::lean_ctor_set(v___x_1524_, 1, v_cache_1522_);
                            if v_isShared_1509_ == 0 {
                                leanh::lean_ctor_set(v___x_1508_, 0, v_g_1521_);
                                v___x_1526_ = v___x_1508_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_1528_ =
                                    leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_g_1521_);
                                v___x_1526_ = v_reuseFailAlloc_1528_;
                                state = 11;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1508_);
                            leanh::lean_dec_ref(v_decl_1486_);
                            leanh::lean_dec_ref(v_cache_1470_);
                            leanh::lean_dec_ref(v_decls_1469_);
                            if v_invert_1475_ == 0 {
                                if v_invert_1477_ == 0 {
                                    v___y_1496_ = v___x_1520_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_gate_1474_);
                                    v___y_1491_ = v_invert_1475_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v___y_1496_ = v_invert_1477_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            10 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1517_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_invert_1475_,
                );
                v___x_1518_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1518_, 0, v___x_1489_);
                leanh::lean_ctor_set(v___x_1518_, 1, v___x_1517_);
                return v___x_1518_;
            }
            11 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1526_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1520_,
                );
                v___x_1527_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1527_, 0, v___x_1524_);
                leanh::lean_ctor_set(v___x_1527_, 1, v___x_1526_);
                return v___x_1527_;
            }
            12 => {
                v_val_1535_ = leanh::lean_ctor_get(v___x_1487_, 0);
                leanh::lean_inc(v_val_1535_);
                leanh::lean_dec_ref_known(v___x_1487_, 1);
                if v_isShared_1473_ == 0 {
                    v___x_1537_ = v___x_1472_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1543_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_decls_1469_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_cache_1470_);
                    v___x_1537_ = v_reuseFailAlloc_1543_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_1538_ = 0;
                if v_isShared_1534_ == 0 {
                    leanh::lean_ctor_set(v___x_1533_, 0, v_val_1535_);
                    v___x_1540_ = v___x_1533_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1542_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_val_1535_);
                    v___x_1540_ = v_reuseFailAlloc_1542_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1540_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1538_,
                );
                v___x_1541_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1541_, 0, v___x_1537_);
                leanh::lean_ctor_set(v___x_1541_, 1, v___x_1540_);
                return v___x_1541_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(
    mut v_aig_1549_: *mut leanh::LeanObject,
    mut v_input_1550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1555_: u8 = 0;
    let mut v_gate_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: u8 = 0;
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1567_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_1551_ = leanh::lean_ctor_get(v_input_1550_, 0);
                v_rhs_1552_ = leanh::lean_ctor_get(v_input_1550_, 1);
                v_isSharedCheck_1567_ = (!leanh::lean_is_exclusive(v_input_1550_)) as u8;
                if v_isSharedCheck_1567_ == 0 {
                    v___x_1554_ = v_input_1550_;
                    v_isShared_1555_ = v_isSharedCheck_1567_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rhs_1552_);
                    leanh::lean_inc(v_lhs_1551_);
                    leanh::lean_dec(v_input_1550_);
                    v___x_1554_ = leanh::lean_box(0);
                    v_isShared_1555_ = v_isSharedCheck_1567_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_1556_ = leanh::lean_ctor_get(v_lhs_1551_, 0);
                v_gate_1557_ = leanh::lean_ctor_get(v_rhs_1552_, 0);
                v___x_1558_ = lean_nat_dec_lt(v_gate_1556_, v_gate_1557_);
                if v___x_1558_ == 0 {
                    if v_isShared_1555_ == 0 {
                        leanh::lean_ctor_set(v___x_1554_, 1, v_lhs_1551_);
                        leanh::lean_ctor_set(v___x_1554_, 0, v_rhs_1552_);
                        v___x_1560_ = v___x_1554_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1562_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_rhs_1552_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_lhs_1551_);
                        v___x_1560_ = v_reuseFailAlloc_1562_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1555_ == 0 {
                        v___x_1564_ = v___x_1554_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1566_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_lhs_1551_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_rhs_1552_);
                        v___x_1564_ = v_reuseFailAlloc_1566_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1561_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6(v_aig_1549_, v___x_1560_);
                return v___x_1561_;
            }
            3 => {
                v___x_1565_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6(v_aig_1549_, v___x_1564_);
                return v___x_1565_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3_spec__8___redArg(
    mut v_aig_1568_: *mut leanh::LeanObject,
    mut v_acc_1569_: *mut leanh::LeanObject,
    mut v_idx_1570_: *mut leanh::LeanObject,
    mut v_len_1571_: *mut leanh::LeanObject,
    mut v_input_1572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: u8 = 0;
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: u8 = 0;
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: u8 = 0;
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1582_ = lean_nat_dec_lt(v_idx_1570_, v_len_1571_);
                if v___x_1582_ == 0 {
                    leanh::lean_dec(v_idx_1570_);
                    v___x_1583_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1583_, 0, v_aig_1568_);
                    leanh::lean_ctor_set(v___x_1583_, 1, v_acc_1569_);
                    return v___x_1583_;
                } else {
                    v_ref_1584_ = lean_array_fget_borrowed(v_input_1572_, v_idx_1570_);
                    v___x_1585_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1586_ = lean_nat_shiftr(v_ref_1584_, v___x_1585_);
                    v___x_1587_ = lean_nat_land(v___x_1585_, v_ref_1584_);
                    v___x_1588_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1589_ = lean_nat_dec_eq(v___x_1587_, v___x_1588_);
                    leanh::lean_dec(v___x_1587_);
                    if v___x_1589_ == 0 {
                        v___x_1590_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_1590_, 0, v___x_1586_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1590_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_1582_,
                        );
                        v___y_1574_ = v___x_1590_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1591_ = 0;
                        v___x_1592_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_1592_, 0, v___x_1586_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1592_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_1591_,
                        );
                        v___y_1574_ = v___x_1592_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1575_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1575_, 0, v_acc_1569_);
                leanh::lean_ctor_set(v___x_1575_, 1, v___y_1574_);
                v_res_1576_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(v_aig_1568_, v___x_1575_);
                v_aig_1577_ = leanh::lean_ctor_get(v_res_1576_, 0);
                leanh::lean_inc_ref(v_aig_1577_);
                v_ref_1578_ = leanh::lean_ctor_get(v_res_1576_, 1);
                leanh::lean_inc_ref(v_ref_1578_);
                leanh::lean_dec_ref(v_res_1576_);
                v___x_1579_ = leanh::lean_unsigned_to_nat(1);
                v___x_1580_ = lean_nat_add(v_idx_1570_, v___x_1579_);
                leanh::lean_dec(v_idx_1570_);
                v_aig_1568_ = v_aig_1577_;
                v_acc_1569_ = v_ref_1578_;
                v_idx_1570_ = v___x_1580_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3_spec__8___redArg___boxed(
    mut v_aig_1593_: *mut leanh::LeanObject,
    mut v_acc_1594_: *mut leanh::LeanObject,
    mut v_idx_1595_: *mut leanh::LeanObject,
    mut v_len_1596_: *mut leanh::LeanObject,
    mut v_input_1597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3_spec__8___redArg(v_aig_1593_, v_acc_1594_, v_idx_1595_, v_len_1596_, v_input_1597_);
    leanh::lean_dec_ref(v_input_1597_);
    leanh::lean_dec(v_len_1596_);
    return v_res_1598_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg(
    mut v_len_1602_: *mut leanh::LeanObject,
    mut v_aig_1603_: *mut leanh::LeanObject,
    mut v_vec_1604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1605_ = leanh::lean_unsigned_to_nat(0);
    v_acc_1606_ = l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg___closed__0;
    v___x_1607_ = l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3_spec__8___redArg(v_aig_1603_, v_acc_1606_, v___x_1605_, v_len_1602_, v_vec_1604_);
    return v___x_1607_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg___boxed(
    mut v_len_1608_: *mut leanh::LeanObject,
    mut v_aig_1609_: *mut leanh::LeanObject,
    mut v_vec_1610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1611_ = l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg(v_len_1608_, v_aig_1609_, v_vec_1610_);
    leanh::lean_dec_ref(v_vec_1610_);
    leanh::lean_dec(v_len_1608_);
    return v_res_1611_;
}
pub unsafe fn l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__0(
    mut v_aig_1612_: *mut leanh::LeanObject,
    mut v_input_1613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1624_: u8 = 0;
    let mut v_gate_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1628_: u8 = 0;
    let mut v___x_1629_: u8 = 0;
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1633_: u8 = 0;
    let mut v_gate_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1637_: u8 = 0;
    let mut v___x_1638_: u8 = 0;
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1642_: u8 = 0;
    let mut v___y_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1647_: u8 = 0;
    let mut v___y_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1652_: u8 = 0;
    let mut v_aig_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1658_: u8 = 0;
    let mut v___x_1659_: u8 = 0;
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1663_: u8 = 0;
    let mut v_aig_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1669_: u8 = 0;
    let mut v___x_1670_: u8 = 0;
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1674_: u8 = 0;
    let mut v_lhs_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1679_: u8 = 0;
    let mut v_gate_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1681_: u8 = 0;
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1684_: u8 = 0;
    let mut v_gate_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1686_: u8 = 0;
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1689_: u8 = 0;
    let mut v___y_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: u8 = 0;
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: u8 = 0;
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: u8 = 0;
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: u8 = 0;
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1718_: u8 = 0;
    let mut v_isSharedCheck_1719_: u8 = 0;
    let mut v_isSharedCheck_1720_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_1675_ = leanh::lean_ctor_get(v_input_1613_, 0);
                v_rhs_1676_ = leanh::lean_ctor_get(v_input_1613_, 1);
                v_isSharedCheck_1720_ = (!leanh::lean_is_exclusive(v_input_1613_)) as u8;
                if v_isSharedCheck_1720_ == 0 {
                    v___x_1678_ = v_input_1613_;
                    v_isShared_1679_ = v_isSharedCheck_1720_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_rhs_1676_);
                    leanh::lean_inc(v_lhs_1675_);
                    leanh::lean_dec(v_input_1613_);
                    v___x_1678_ = leanh::lean_box(0);
                    v_isShared_1679_ = v_isSharedCheck_1720_;
                    state = 12;
                    continue;
                }
            }
            1 => {
                v___x_1618_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1618_, 0, v___y_1615_);
                leanh::lean_ctor_set(v___x_1618_, 1, v___y_1617_);
                v___x_1619_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(v___y_1616_, v___x_1618_);
                return v___x_1619_;
            }
            2 => {
                v_invert_1624_ = leanh::lean_ctor_get_uint8(
                    v___y_1621_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1624_ == 0 {
                    v_gate_1625_ = leanh::lean_ctor_get(v___y_1621_, 0);
                    v_isSharedCheck_1633_ = (!leanh::lean_is_exclusive(v___y_1621_)) as u8;
                    if v_isSharedCheck_1633_ == 0 {
                        v___x_1627_ = v___y_1621_;
                        v_isShared_1628_ = v_isSharedCheck_1633_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_1625_);
                        leanh::lean_dec(v___y_1621_);
                        v___x_1627_ = leanh::lean_box(0);
                        v_isShared_1628_ = v_isSharedCheck_1633_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_gate_1634_ = leanh::lean_ctor_get(v___y_1621_, 0);
                    v_isSharedCheck_1642_ = (!leanh::lean_is_exclusive(v___y_1621_)) as u8;
                    if v_isSharedCheck_1642_ == 0 {
                        v___x_1636_ = v___y_1621_;
                        v_isShared_1637_ = v_isSharedCheck_1642_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_1634_);
                        leanh::lean_dec(v___y_1621_);
                        v___x_1636_ = leanh::lean_box(0);
                        v_isShared_1637_ = v_isSharedCheck_1642_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1629_ = 1;
                if v_isShared_1628_ == 0 {
                    v___x_1631_ = v___x_1627_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1632_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_gate_1625_);
                    v___x_1631_ = v_reuseFailAlloc_1632_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1631_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1629_,
                );
                v___y_1615_ = v___y_1623_;
                v___y_1616_ = v___y_1622_;
                v___y_1617_ = v___x_1631_;
                state = 1;
                continue;
            }
            5 => {
                v___x_1638_ = 0;
                if v_isShared_1637_ == 0 {
                    v___x_1640_ = v___x_1636_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1641_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_gate_1634_);
                    v___x_1640_ = v_reuseFailAlloc_1641_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1640_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1638_,
                );
                v___y_1615_ = v___y_1623_;
                v___y_1616_ = v___y_1622_;
                v___y_1617_ = v___x_1640_;
                state = 1;
                continue;
            }
            7 => {
                v___x_1649_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1649_, 0, v___y_1644_);
                leanh::lean_ctor_set_uint8(
                    v___x_1649_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___y_1647_,
                );
                v___x_1650_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1650_, 0, v___y_1648_);
                leanh::lean_ctor_set(v___x_1650_, 1, v___x_1649_);
                v_res_1651_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(v___y_1646_, v___x_1650_);
                v_invert_1652_ = leanh::lean_ctor_get_uint8(
                    v___y_1645_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1652_ == 0 {
                    v_aig_1653_ = leanh::lean_ctor_get(v_res_1651_, 0);
                    leanh::lean_inc_ref(v_aig_1653_);
                    v_ref_1654_ = leanh::lean_ctor_get(v_res_1651_, 1);
                    leanh::lean_inc_ref(v_ref_1654_);
                    leanh::lean_dec_ref(v_res_1651_);
                    v_gate_1655_ = leanh::lean_ctor_get(v___y_1645_, 0);
                    v_isSharedCheck_1663_ = (!leanh::lean_is_exclusive(v___y_1645_)) as u8;
                    if v_isSharedCheck_1663_ == 0 {
                        v___x_1657_ = v___y_1645_;
                        v_isShared_1658_ = v_isSharedCheck_1663_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_1655_);
                        leanh::lean_dec(v___y_1645_);
                        v___x_1657_ = leanh::lean_box(0);
                        v_isShared_1658_ = v_isSharedCheck_1663_;
                        state = 8;
                        continue;
                    }
                } else {
                    v_aig_1664_ = leanh::lean_ctor_get(v_res_1651_, 0);
                    leanh::lean_inc_ref(v_aig_1664_);
                    v_ref_1665_ = leanh::lean_ctor_get(v_res_1651_, 1);
                    leanh::lean_inc_ref(v_ref_1665_);
                    leanh::lean_dec_ref(v_res_1651_);
                    v_gate_1666_ = leanh::lean_ctor_get(v___y_1645_, 0);
                    v_isSharedCheck_1674_ = (!leanh::lean_is_exclusive(v___y_1645_)) as u8;
                    if v_isSharedCheck_1674_ == 0 {
                        v___x_1668_ = v___y_1645_;
                        v_isShared_1669_ = v_isSharedCheck_1674_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_1666_);
                        leanh::lean_dec(v___y_1645_);
                        v___x_1668_ = leanh::lean_box(0);
                        v_isShared_1669_ = v_isSharedCheck_1674_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_1659_ = 1;
                if v_isShared_1658_ == 0 {
                    v___x_1661_ = v___x_1657_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1662_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_gate_1655_);
                    v___x_1661_ = v_reuseFailAlloc_1662_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1661_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1659_,
                );
                v___y_1621_ = v_ref_1654_;
                v___y_1622_ = v_aig_1653_;
                v___y_1623_ = v___x_1661_;
                state = 2;
                continue;
            }
            10 => {
                v___x_1670_ = 0;
                if v_isShared_1669_ == 0 {
                    v___x_1672_ = v___x_1668_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1673_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_gate_1666_);
                    v___x_1672_ = v_reuseFailAlloc_1673_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1672_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1670_,
                );
                v___y_1621_ = v_ref_1665_;
                v___y_1622_ = v_aig_1664_;
                v___y_1623_ = v___x_1672_;
                state = 2;
                continue;
            }
            12 => {
                v_gate_1680_ = leanh::lean_ctor_get(v_lhs_1675_, 0);
                v_invert_1681_ = leanh::lean_ctor_get_uint8(
                    v_lhs_1675_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1719_ = (!leanh::lean_is_exclusive(v_lhs_1675_)) as u8;
                if v_isSharedCheck_1719_ == 0 {
                    v___x_1683_ = v_lhs_1675_;
                    v_isShared_1684_ = v_isSharedCheck_1719_;
                    state = 13;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_1680_);
                    leanh::lean_dec(v_lhs_1675_);
                    v___x_1683_ = leanh::lean_box(0);
                    v_isShared_1684_ = v_isSharedCheck_1719_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_gate_1685_ = leanh::lean_ctor_get(v_rhs_1676_, 0);
                v_invert_1686_ = leanh::lean_ctor_get_uint8(
                    v_rhs_1676_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1718_ = (!leanh::lean_is_exclusive(v_rhs_1676_)) as u8;
                if v_isSharedCheck_1718_ == 0 {
                    v___x_1688_ = v_rhs_1676_;
                    v_isShared_1689_ = v_isSharedCheck_1718_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_1685_);
                    leanh::lean_dec(v_rhs_1676_);
                    v___x_1688_ = leanh::lean_box(0);
                    v_isShared_1689_ = v_isSharedCheck_1718_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                leanh::lean_inc(v_gate_1680_);
                if v_isShared_1684_ == 0 {
                    v___x_1706_ = v___x_1683_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1717_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_gate_1680_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1717_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_invert_1681_,
                    );
                    v___x_1706_ = v_reuseFailAlloc_1717_;
                    state = 18;
                    continue;
                }
            }
            15 => {
                v_res_1692_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(v_aig_1612_, v___y_1691_);
                if v_invert_1681_ == 0 {
                    v_aig_1693_ = leanh::lean_ctor_get(v_res_1692_, 0);
                    leanh::lean_inc_ref(v_aig_1693_);
                    v_ref_1694_ = leanh::lean_ctor_get(v_res_1692_, 1);
                    leanh::lean_inc_ref(v_ref_1694_);
                    leanh::lean_dec_ref(v_res_1692_);
                    v___x_1695_ = 1;
                    if v_isShared_1689_ == 0 {
                        leanh::lean_ctor_set(v___x_1688_, 0, v_gate_1680_);
                        v___x_1697_ = v___x_1688_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_1698_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_gate_1680_);
                        v___x_1697_ = v_reuseFailAlloc_1698_;
                        state = 16;
                        continue;
                    }
                } else {
                    v_aig_1699_ = leanh::lean_ctor_get(v_res_1692_, 0);
                    leanh::lean_inc_ref(v_aig_1699_);
                    v_ref_1700_ = leanh::lean_ctor_get(v_res_1692_, 1);
                    leanh::lean_inc_ref(v_ref_1700_);
                    leanh::lean_dec_ref(v_res_1692_);
                    v___x_1701_ = 0;
                    if v_isShared_1689_ == 0 {
                        leanh::lean_ctor_set(v___x_1688_, 0, v_gate_1680_);
                        v___x_1703_ = v___x_1688_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_1704_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_gate_1680_);
                        v___x_1703_ = v_reuseFailAlloc_1704_;
                        state = 17;
                        continue;
                    }
                }
            }
            16 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1697_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1695_,
                );
                v___y_1644_ = v_gate_1685_;
                v___y_1645_ = v_ref_1694_;
                v___y_1646_ = v_aig_1693_;
                v___y_1647_ = v_invert_1686_;
                v___y_1648_ = v___x_1697_;
                state = 7;
                continue;
            }
            17 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1703_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1701_,
                );
                v___y_1644_ = v_gate_1685_;
                v___y_1645_ = v_ref_1700_;
                v___y_1646_ = v_aig_1699_;
                v___y_1647_ = v_invert_1686_;
                v___y_1648_ = v___x_1703_;
                state = 7;
                continue;
            }
            18 => {
                if v_invert_1686_ == 0 {
                    v___x_1707_ = 1;
                    leanh::lean_inc(v_gate_1685_);
                    v___x_1708_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1708_, 0, v_gate_1685_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1708_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1707_,
                    );
                    if v_isShared_1679_ == 0 {
                        leanh::lean_ctor_set(v___x_1678_, 1, v___x_1708_);
                        leanh::lean_ctor_set(v___x_1678_, 0, v___x_1706_);
                        v___x_1710_ = v___x_1678_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_1711_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1706_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1711_, 1, v___x_1708_);
                        v___x_1710_ = v_reuseFailAlloc_1711_;
                        state = 19;
                        continue;
                    }
                } else {
                    v___x_1712_ = 0;
                    leanh::lean_inc(v_gate_1685_);
                    v___x_1713_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1713_, 0, v_gate_1685_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1713_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1712_,
                    );
                    if v_isShared_1679_ == 0 {
                        leanh::lean_ctor_set(v___x_1678_, 1, v___x_1713_);
                        leanh::lean_ctor_set(v___x_1678_, 0, v___x_1706_);
                        v___x_1715_ = v___x_1678_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_1716_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1706_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 1, v___x_1713_);
                        v___x_1715_ = v_reuseFailAlloc_1716_;
                        state = 20;
                        continue;
                    }
                }
            }
            19 => {
                v___y_1691_ = v___x_1710_;
                state = 15;
                continue;
            }
            20 => {
                v___y_1691_ = v___x_1715_;
                state = 15;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__4___redArg(
    mut v_len_1721_: *mut leanh::LeanObject,
    mut v_aig_1722_: *mut leanh::LeanObject,
    mut v_idx_1723_: *mut leanh::LeanObject,
    mut v_s_1724_: *mut leanh::LeanObject,
    mut v_lhs_1725_: *mut leanh::LeanObject,
    mut v_rhs_1726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1735_: u8 = 0;
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: u8 = 0;
    let mut v___y_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: u8 = 0;
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: u8 = 0;
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: u8 = 0;
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: u8 = 0;
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1744_ = lean_nat_dec_lt(v_idx_1723_, v_len_1721_);
                if v___x_1744_ == 0 {
                    leanh::lean_dec(v_idx_1723_);
                    v___x_1756_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1756_, 0, v_aig_1722_);
                    leanh::lean_ctor_set(v___x_1756_, 1, v_s_1724_);
                    return v___x_1756_;
                } else {
                    v_ref_1757_ = lean_array_fget_borrowed(v_lhs_1725_, v_idx_1723_);
                    v___x_1758_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1759_ = lean_nat_shiftr(v_ref_1757_, v___x_1758_);
                    v___x_1760_ = lean_nat_land(v___x_1758_, v_ref_1757_);
                    v___x_1761_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1762_ = lean_nat_dec_eq(v___x_1760_, v___x_1761_);
                    leanh::lean_dec(v___x_1760_);
                    if v___x_1762_ == 0 {
                        v___x_1763_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_1763_, 0, v___x_1759_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1763_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_1744_,
                        );
                        v___y_1746_ = v___x_1763_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1764_ = 0;
                        v___x_1765_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_1765_, 0, v___x_1759_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1765_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_1764_,
                        );
                        v___y_1746_ = v___x_1765_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1730_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1730_, 0, v___y_1728_);
                leanh::lean_ctor_set(v___x_1730_, 1, v___y_1729_);
                v_res_1731_ = l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__0(v_aig_1722_, v___x_1730_);
                v_ref_1732_ = leanh::lean_ctor_get(v_res_1731_, 1);
                leanh::lean_inc_ref(v_ref_1732_);
                v_aig_1733_ = leanh::lean_ctor_get(v_res_1731_, 0);
                leanh::lean_inc_ref(v_aig_1733_);
                leanh::lean_dec_ref(v_res_1731_);
                v_gate_1734_ = leanh::lean_ctor_get(v_ref_1732_, 0);
                leanh::lean_inc(v_gate_1734_);
                v_invert_1735_ = leanh::lean_ctor_get_uint8(
                    v_ref_1732_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_dec_ref(v_ref_1732_);
                v___x_1736_ = leanh::lean_unsigned_to_nat(1);
                v___x_1737_ = lean_nat_add(v_idx_1723_, v___x_1736_);
                leanh::lean_dec(v_idx_1723_);
                v___x_1738_ = leanh::lean_unsigned_to_nat(2);
                v___x_1739_ = lean_nat_mul(v_gate_1734_, v___x_1738_);
                leanh::lean_dec(v_gate_1734_);
                v___x_1740_ = l_Bool_toNat(v_invert_1735_);
                v___x_1741_ = lean_nat_lor(v___x_1739_, v___x_1740_);
                leanh::lean_dec(v___x_1740_);
                leanh::lean_dec(v___x_1739_);
                v_s_1742_ = lean_array_push(v_s_1724_, v___x_1741_);
                v_aig_1722_ = v_aig_1733_;
                v_idx_1723_ = v___x_1737_;
                v_s_1724_ = v_s_1742_;
                state = 0;
                continue;
            }
            2 => {
                v_ref_1747_ = lean_array_fget_borrowed(v_rhs_1726_, v_idx_1723_);
                v___x_1748_ = leanh::lean_unsigned_to_nat(1);
                v___x_1749_ = lean_nat_shiftr(v_ref_1747_, v___x_1748_);
                v___x_1750_ = lean_nat_land(v___x_1748_, v_ref_1747_);
                v___x_1751_ = leanh::lean_unsigned_to_nat(0);
                v___x_1752_ = lean_nat_dec_eq(v___x_1750_, v___x_1751_);
                leanh::lean_dec(v___x_1750_);
                if v___x_1752_ == 0 {
                    v___x_1753_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1753_, 0, v___x_1749_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1753_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1744_,
                    );
                    v___y_1728_ = v___y_1746_;
                    v___y_1729_ = v___x_1753_;
                    state = 1;
                    continue;
                } else {
                    v___x_1754_ = 0;
                    v___x_1755_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1755_, 0, v___x_1749_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1755_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1754_,
                    );
                    v___y_1728_ = v___y_1746_;
                    v___y_1729_ = v___x_1755_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_len_1766_: *mut leanh::LeanObject,
    mut v_aig_1767_: *mut leanh::LeanObject,
    mut v_idx_1768_: *mut leanh::LeanObject,
    mut v_s_1769_: *mut leanh::LeanObject,
    mut v_lhs_1770_: *mut leanh::LeanObject,
    mut v_rhs_1771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1772_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__4___redArg(v_len_1766_, v_aig_1767_, v_idx_1768_, v_s_1769_, v_lhs_1770_, v_rhs_1771_);
    leanh::lean_dec_ref(v_rhs_1771_);
    leanh::lean_dec_ref(v_lhs_1770_);
    leanh::lean_dec(v_len_1766_);
    return v_res_1772_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1___redArg(
    mut v_len_1773_: *mut leanh::LeanObject,
    mut v_aig_1774_: *mut leanh::LeanObject,
    mut v_input_1775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lhs_1776_ = leanh::lean_ctor_get(v_input_1775_, 0);
    v_rhs_1777_ = leanh::lean_ctor_get(v_input_1775_, 1);
    v___x_1778_ = leanh::lean_unsigned_to_nat(0);
    v___x_1779_ = lean_mk_empty_array_with_capacity(v_len_1773_);
    v___x_1780_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__4___redArg(v_len_1773_, v_aig_1774_, v___x_1778_, v___x_1779_, v_lhs_1776_, v_rhs_1777_);
    return v___x_1780_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1___redArg___boxed(
    mut v_len_1781_: *mut leanh::LeanObject,
    mut v_aig_1782_: *mut leanh::LeanObject,
    mut v_input_1783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1784_ = l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1___redArg(v_len_1781_, v_aig_1782_, v_input_1783_);
    leanh::lean_dec_ref(v_input_1783_);
    leanh::lean_dec(v_len_1781_);
    return v_res_1784_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0(
    mut v_w_1785_: *mut leanh::LeanObject,
    mut v_aig_1786_: *mut leanh::LeanObject,
    mut v_pair_1787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1788_ = l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1___redArg(v_w_1785_, v_aig_1786_, v_pair_1787_);
    v_aig_1789_ = leanh::lean_ctor_get(v_res_1788_, 0);
    leanh::lean_inc_ref(v_aig_1789_);
    v_vec_1790_ = leanh::lean_ctor_get(v_res_1788_, 1);
    leanh::lean_inc_ref(v_vec_1790_);
    leanh::lean_dec_ref(v_res_1788_);
    v___x_1791_ = l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg(v_w_1785_, v_aig_1789_, v_vec_1790_);
    leanh::lean_dec_ref(v_vec_1790_);
    return v___x_1791_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0___boxed(
    mut v_w_1792_: *mut leanh::LeanObject,
    mut v_aig_1793_: *mut leanh::LeanObject,
    mut v_pair_1794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1795_ =
        l_Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0(
            v_w_1792_,
            v_aig_1793_,
            v_pair_1794_,
        );
    leanh::lean_dec_ref(v_pair_1794_);
    leanh::lean_dec(v_w_1792_);
    return v_res_1795_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11_spec__15___redArg(
    mut v___x_1796_: *mut leanh::LeanObject,
    mut v_len_1797_: *mut leanh::LeanObject,
    mut v_aig_1798_: *mut leanh::LeanObject,
    mut v_idx_1799_: *mut leanh::LeanObject,
    mut v_s_1800_: *mut leanh::LeanObject,
    mut v_input_1801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1808_: u8 = 0;
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: u8 = 0;
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: u8 = 0;
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: u8 = 0;
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1817_ = lean_nat_dec_lt(v_idx_1799_, v_len_1797_);
                if v___x_1817_ == 0 {
                    leanh::lean_dec(v_idx_1799_);
                    leanh::lean_dec_ref(v___x_1796_);
                    v___x_1818_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1818_, 0, v_aig_1798_);
                    leanh::lean_ctor_set(v___x_1818_, 1, v_s_1800_);
                    return v___x_1818_;
                } else {
                    v_ref_1819_ = lean_array_fget_borrowed(v_input_1801_, v_idx_1799_);
                    v___x_1820_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1821_ = lean_nat_shiftr(v_ref_1819_, v___x_1820_);
                    v___x_1822_ = lean_nat_land(v___x_1820_, v_ref_1819_);
                    v___x_1823_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1824_ = lean_nat_dec_eq(v___x_1822_, v___x_1823_);
                    leanh::lean_dec(v___x_1822_);
                    if v___x_1824_ == 0 {
                        v___x_1825_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_1825_, 0, v___x_1821_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1825_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_1817_,
                        );
                        v___y_1803_ = v___x_1825_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1826_ = 0;
                        v___x_1827_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_1827_, 0, v___x_1821_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1827_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_1826_,
                        );
                        v___y_1803_ = v___x_1827_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___x_1796_);
                v_res_1804_ = leanh::lean_apply_2(v___x_1796_, v_aig_1798_, v___y_1803_);
                v_ref_1805_ = leanh::lean_ctor_get(v_res_1804_, 1);
                leanh::lean_inc_ref(v_ref_1805_);
                v_aig_1806_ = leanh::lean_ctor_get(v_res_1804_, 0);
                leanh::lean_inc_ref(v_aig_1806_);
                leanh::lean_dec_ref(v_res_1804_);
                v_gate_1807_ = leanh::lean_ctor_get(v_ref_1805_, 0);
                leanh::lean_inc(v_gate_1807_);
                v_invert_1808_ = leanh::lean_ctor_get_uint8(
                    v_ref_1805_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_dec_ref(v_ref_1805_);
                v___x_1809_ = leanh::lean_unsigned_to_nat(1);
                v___x_1810_ = lean_nat_add(v_idx_1799_, v___x_1809_);
                leanh::lean_dec(v_idx_1799_);
                v___x_1811_ = leanh::lean_unsigned_to_nat(2);
                v___x_1812_ = lean_nat_mul(v_gate_1807_, v___x_1811_);
                leanh::lean_dec(v_gate_1807_);
                v___x_1813_ = l_Bool_toNat(v_invert_1808_);
                v___x_1814_ = lean_nat_lor(v___x_1812_, v___x_1813_);
                leanh::lean_dec(v___x_1813_);
                leanh::lean_dec(v___x_1812_);
                v_s_1815_ = lean_array_push(v_s_1800_, v___x_1814_);
                v_aig_1798_ = v_aig_1806_;
                v_idx_1799_ = v___x_1810_;
                v_s_1800_ = v_s_1815_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11_spec__15___redArg___boxed(
    mut v___x_1828_: *mut leanh::LeanObject,
    mut v_len_1829_: *mut leanh::LeanObject,
    mut v_aig_1830_: *mut leanh::LeanObject,
    mut v_idx_1831_: *mut leanh::LeanObject,
    mut v_s_1832_: *mut leanh::LeanObject,
    mut v_input_1833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1834_ = l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11_spec__15___redArg(v___x_1828_, v_len_1829_, v_aig_1830_, v_idx_1831_, v_s_1832_, v_input_1833_);
    leanh::lean_dec_ref(v_input_1833_);
    leanh::lean_dec(v_len_1829_);
    return v_res_1834_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11(
    mut v_len_1835_: *mut leanh::LeanObject,
    mut v_aig_1836_: *mut leanh::LeanObject,
    mut v_target_1837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vec_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_func_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_vec_1838_ = leanh::lean_ctor_get(v_target_1837_, 0);
    leanh::lean_inc_ref(v_vec_1838_);
    v_func_1839_ = leanh::lean_ctor_get(v_target_1837_, 1);
    leanh::lean_inc_ref(v_func_1839_);
    leanh::lean_dec_ref(v_target_1837_);
    v___x_1840_ = leanh::lean_unsigned_to_nat(0);
    v___x_1841_ = lean_mk_empty_array_with_capacity(v_len_1835_);
    v___x_1842_ = l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11_spec__15___redArg(v_func_1839_, v_len_1835_, v_aig_1836_, v___x_1840_, v___x_1841_, v_vec_1838_);
    leanh::lean_dec_ref(v_vec_1838_);
    return v___x_1842_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11___boxed(
    mut v_len_1843_: *mut leanh::LeanObject,
    mut v_aig_1844_: *mut leanh::LeanObject,
    mut v_target_1845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1846_ = l_Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11(v_len_1843_, v_aig_1844_, v_target_1845_);
    leanh::lean_dec(v_len_1843_);
    return v_res_1846_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5___lam__0(
    mut v___y_1847_: *mut leanh::LeanObject,
    mut v___y_1848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_invert_1849_: u8 = 0;
    let mut v_gate_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___x_1854_: u8 = 0;
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1859_: u8 = 0;
    let mut v_gate_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1863_: u8 = 0;
    let mut v___x_1864_: u8 = 0;
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1869_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_invert_1849_ = leanh::lean_ctor_get_uint8(
                    v___y_1848_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1849_ == 0 {
                    v_gate_1850_ = leanh::lean_ctor_get(v___y_1848_, 0);
                    v_isSharedCheck_1859_ = (!leanh::lean_is_exclusive(v___y_1848_)) as u8;
                    if v_isSharedCheck_1859_ == 0 {
                        v___x_1852_ = v___y_1848_;
                        v_isShared_1853_ = v_isSharedCheck_1859_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_1850_);
                        leanh::lean_dec(v___y_1848_);
                        v___x_1852_ = leanh::lean_box(0);
                        v_isShared_1853_ = v_isSharedCheck_1859_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_gate_1860_ = leanh::lean_ctor_get(v___y_1848_, 0);
                    v_isSharedCheck_1869_ = (!leanh::lean_is_exclusive(v___y_1848_)) as u8;
                    if v_isSharedCheck_1869_ == 0 {
                        v___x_1862_ = v___y_1848_;
                        v_isShared_1863_ = v_isSharedCheck_1869_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_1860_);
                        leanh::lean_dec(v___y_1848_);
                        v___x_1862_ = leanh::lean_box(0);
                        v_isShared_1863_ = v_isSharedCheck_1869_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1854_ = 1;
                if v_isShared_1853_ == 0 {
                    v___x_1856_ = v___x_1852_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1858_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_gate_1850_);
                    v___x_1856_ = v_reuseFailAlloc_1858_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1856_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1854_,
                );
                v___x_1857_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1857_, 0, v___y_1847_);
                leanh::lean_ctor_set(v___x_1857_, 1, v___x_1856_);
                return v___x_1857_;
            }
            3 => {
                v___x_1864_ = 0;
                if v_isShared_1863_ == 0 {
                    v___x_1866_ = v___x_1862_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1868_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_gate_1860_);
                    v___x_1866_ = v_reuseFailAlloc_1868_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1866_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1864_,
                );
                v___x_1867_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1867_, 0, v___y_1847_);
                leanh::lean_ctor_set(v___x_1867_, 1, v___x_1866_);
                return v___x_1867_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5(
    mut v_w_1871_: *mut leanh::LeanObject,
    mut v_aig_1872_: *mut leanh::LeanObject,
    mut v_s_1873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1874_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5___closed__0;
    v___x_1875_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1875_, 0, v_s_1873_);
    leanh::lean_ctor_set(v___x_1875_, 1, v___f_1874_);
    v___x_1876_ = l_Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11(v_w_1871_, v_aig_1872_, v___x_1875_);
    return v___x_1876_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5___boxed(
    mut v_w_1877_: *mut leanh::LeanObject,
    mut v_aig_1878_: *mut leanh::LeanObject,
    mut v_s_1879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1880_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5(v_w_1877_, v_aig_1878_, v_s_1879_);
    leanh::lean_dec(v_w_1877_);
    return v_res_1880_;
}
pub unsafe fn l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6_spec__13_spec__18_spec__25(
    mut v_aig_1881_: *mut leanh::LeanObject,
    mut v_input_1882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1887_: u8 = 0;
    let mut v_aig_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1891_: u8 = 0;
    let mut v_gate_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1895_: u8 = 0;
    let mut v___x_1896_: u8 = 0;
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1903_: u8 = 0;
    let mut v_isSharedCheck_1904_: u8 = 0;
    let mut v_unused_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1909_: u8 = 0;
    let mut v_gate_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1913_: u8 = 0;
    let mut v___x_1914_: u8 = 0;
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1921_: u8 = 0;
    let mut v_isSharedCheck_1922_: u8 = 0;
    let mut v_unused_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1928_: u8 = 0;
    let mut v___y_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1931_: u8 = 0;
    let mut v_gate_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1935_: u8 = 0;
    let mut v___x_1936_: u8 = 0;
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1943_: u8 = 0;
    let mut v_gate_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1947_: u8 = 0;
    let mut v___x_1948_: u8 = 0;
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1955_: u8 = 0;
    let mut v_invert_1956_: u8 = 0;
    let mut v_gate_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1960_: u8 = 0;
    let mut v___x_1961_: u8 = 0;
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1965_: u8 = 0;
    let mut v_gate_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1970_: u8 = 0;
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1974_: u8 = 0;
    let mut v_isSharedCheck_1975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_1924_ = leanh::lean_ctor_get(v_input_1882_, 0);
                v_rhs_1925_ = leanh::lean_ctor_get(v_input_1882_, 1);
                v_isSharedCheck_1975_ = (!leanh::lean_is_exclusive(v_input_1882_)) as u8;
                if v_isSharedCheck_1975_ == 0 {
                    v___x_1927_ = v_input_1882_;
                    v_isShared_1928_ = v_isSharedCheck_1975_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc(v_rhs_1925_);
                    leanh::lean_inc(v_lhs_1924_);
                    leanh::lean_dec(v_input_1882_);
                    v___x_1927_ = leanh::lean_box(0);
                    v_isShared_1928_ = v_isSharedCheck_1975_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v_res_1885_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(v_aig_1881_, v___y_1884_);
                v_ref_1886_ = leanh::lean_ctor_get(v_res_1885_, 1);
                leanh::lean_inc_ref(v_ref_1886_);
                v_invert_1887_ = leanh::lean_ctor_get_uint8(
                    v_ref_1886_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1887_ == 0 {
                    v_aig_1888_ = leanh::lean_ctor_get(v_res_1885_, 0);
                    v_isSharedCheck_1904_ = (!leanh::lean_is_exclusive(v_res_1885_)) as u8;
                    if v_isSharedCheck_1904_ == 0 {
                        v_unused_1905_ = leanh::lean_ctor_get(v_res_1885_, 1);
                        leanh::lean_dec(v_unused_1905_);
                        v___x_1890_ = v_res_1885_;
                        v_isShared_1891_ = v_isSharedCheck_1904_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_aig_1888_);
                        leanh::lean_dec(v_res_1885_);
                        v___x_1890_ = leanh::lean_box(0);
                        v_isShared_1891_ = v_isSharedCheck_1904_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_aig_1906_ = leanh::lean_ctor_get(v_res_1885_, 0);
                    v_isSharedCheck_1922_ = (!leanh::lean_is_exclusive(v_res_1885_)) as u8;
                    if v_isSharedCheck_1922_ == 0 {
                        v_unused_1923_ = leanh::lean_ctor_get(v_res_1885_, 1);
                        leanh::lean_dec(v_unused_1923_);
                        v___x_1908_ = v_res_1885_;
                        v_isShared_1909_ = v_isSharedCheck_1922_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_aig_1906_);
                        leanh::lean_dec(v_res_1885_);
                        v___x_1908_ = leanh::lean_box(0);
                        v_isShared_1909_ = v_isSharedCheck_1922_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_gate_1892_ = leanh::lean_ctor_get(v_ref_1886_, 0);
                v_isSharedCheck_1903_ = (!leanh::lean_is_exclusive(v_ref_1886_)) as u8;
                if v_isSharedCheck_1903_ == 0 {
                    v___x_1894_ = v_ref_1886_;
                    v_isShared_1895_ = v_isSharedCheck_1903_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_1892_);
                    leanh::lean_dec(v_ref_1886_);
                    v___x_1894_ = leanh::lean_box(0);
                    v_isShared_1895_ = v_isSharedCheck_1903_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1896_ = 1;
                if v_isShared_1895_ == 0 {
                    v___x_1898_ = v___x_1894_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1902_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_gate_1892_);
                    v___x_1898_ = v_reuseFailAlloc_1902_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1898_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1896_,
                );
                if v_isShared_1891_ == 0 {
                    leanh::lean_ctor_set(v___x_1890_, 1, v___x_1898_);
                    v___x_1900_ = v___x_1890_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1901_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_aig_1888_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 1, v___x_1898_);
                    v___x_1900_ = v_reuseFailAlloc_1901_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1900_;
            }
            6 => {
                v_gate_1910_ = leanh::lean_ctor_get(v_ref_1886_, 0);
                v_isSharedCheck_1921_ = (!leanh::lean_is_exclusive(v_ref_1886_)) as u8;
                if v_isSharedCheck_1921_ == 0 {
                    v___x_1912_ = v_ref_1886_;
                    v_isShared_1913_ = v_isSharedCheck_1921_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_1910_);
                    leanh::lean_dec(v_ref_1886_);
                    v___x_1912_ = leanh::lean_box(0);
                    v_isShared_1913_ = v_isSharedCheck_1921_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1914_ = 0;
                if v_isShared_1913_ == 0 {
                    v___x_1916_ = v___x_1912_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1920_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_gate_1910_);
                    v___x_1916_ = v_reuseFailAlloc_1920_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1916_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1914_,
                );
                if v_isShared_1909_ == 0 {
                    leanh::lean_ctor_set(v___x_1908_, 1, v___x_1916_);
                    v___x_1918_ = v___x_1908_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1919_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_aig_1906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1919_, 1, v___x_1916_);
                    v___x_1918_ = v_reuseFailAlloc_1919_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1918_;
            }
            10 => {
                v_invert_1956_ = leanh::lean_ctor_get_uint8(
                    v_lhs_1924_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1956_ == 0 {
                    v_gate_1957_ = leanh::lean_ctor_get(v_lhs_1924_, 0);
                    v_isSharedCheck_1965_ = (!leanh::lean_is_exclusive(v_lhs_1924_)) as u8;
                    if v_isSharedCheck_1965_ == 0 {
                        v___x_1959_ = v_lhs_1924_;
                        v_isShared_1960_ = v_isSharedCheck_1965_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_1957_);
                        leanh::lean_dec(v_lhs_1924_);
                        v___x_1959_ = leanh::lean_box(0);
                        v_isShared_1960_ = v_isSharedCheck_1965_;
                        state = 18;
                        continue;
                    }
                } else {
                    v_gate_1966_ = leanh::lean_ctor_get(v_lhs_1924_, 0);
                    v_isSharedCheck_1974_ = (!leanh::lean_is_exclusive(v_lhs_1924_)) as u8;
                    if v_isSharedCheck_1974_ == 0 {
                        v___x_1968_ = v_lhs_1924_;
                        v_isShared_1969_ = v_isSharedCheck_1974_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_1966_);
                        leanh::lean_dec(v_lhs_1924_);
                        v___x_1968_ = leanh::lean_box(0);
                        v_isShared_1969_ = v_isSharedCheck_1974_;
                        state = 20;
                        continue;
                    }
                }
            }
            11 => {
                v_invert_1931_ = leanh::lean_ctor_get_uint8(
                    v_rhs_1925_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1931_ == 0 {
                    v_gate_1932_ = leanh::lean_ctor_get(v_rhs_1925_, 0);
                    v_isSharedCheck_1943_ = (!leanh::lean_is_exclusive(v_rhs_1925_)) as u8;
                    if v_isSharedCheck_1943_ == 0 {
                        v___x_1934_ = v_rhs_1925_;
                        v_isShared_1935_ = v_isSharedCheck_1943_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_1932_);
                        leanh::lean_dec(v_rhs_1925_);
                        v___x_1934_ = leanh::lean_box(0);
                        v_isShared_1935_ = v_isSharedCheck_1943_;
                        state = 12;
                        continue;
                    }
                } else {
                    v_gate_1944_ = leanh::lean_ctor_get(v_rhs_1925_, 0);
                    v_isSharedCheck_1955_ = (!leanh::lean_is_exclusive(v_rhs_1925_)) as u8;
                    if v_isSharedCheck_1955_ == 0 {
                        v___x_1946_ = v_rhs_1925_;
                        v_isShared_1947_ = v_isSharedCheck_1955_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_1944_);
                        leanh::lean_dec(v_rhs_1925_);
                        v___x_1946_ = leanh::lean_box(0);
                        v_isShared_1947_ = v_isSharedCheck_1955_;
                        state = 15;
                        continue;
                    }
                }
            }
            12 => {
                v___x_1936_ = 1;
                if v_isShared_1935_ == 0 {
                    v___x_1938_ = v___x_1934_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1942_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_gate_1932_);
                    v___x_1938_ = v_reuseFailAlloc_1942_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1938_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1936_,
                );
                if v_isShared_1928_ == 0 {
                    leanh::lean_ctor_set(v___x_1927_, 1, v___x_1938_);
                    leanh::lean_ctor_set(v___x_1927_, 0, v___y_1930_);
                    v___x_1940_ = v___x_1927_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1941_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___y_1930_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1941_, 1, v___x_1938_);
                    v___x_1940_ = v_reuseFailAlloc_1941_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___y_1884_ = v___x_1940_;
                state = 1;
                continue;
            }
            15 => {
                v___x_1948_ = 0;
                if v_isShared_1947_ == 0 {
                    v___x_1950_ = v___x_1946_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1954_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_gate_1944_);
                    v___x_1950_ = v_reuseFailAlloc_1954_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1950_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1948_,
                );
                if v_isShared_1928_ == 0 {
                    leanh::lean_ctor_set(v___x_1927_, 1, v___x_1950_);
                    leanh::lean_ctor_set(v___x_1927_, 0, v___y_1930_);
                    v___x_1952_ = v___x_1927_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1953_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___y_1930_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1953_, 1, v___x_1950_);
                    v___x_1952_ = v_reuseFailAlloc_1953_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___y_1884_ = v___x_1952_;
                state = 1;
                continue;
            }
            18 => {
                v___x_1961_ = 1;
                if v_isShared_1960_ == 0 {
                    v___x_1963_ = v___x_1959_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1964_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_gate_1957_);
                    v___x_1963_ = v_reuseFailAlloc_1964_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1963_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1961_,
                );
                v___y_1930_ = v___x_1963_;
                state = 11;
                continue;
            }
            20 => {
                v___x_1970_ = 0;
                if v_isShared_1969_ == 0 {
                    v___x_1972_ = v___x_1968_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1973_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_gate_1966_);
                    v___x_1972_ = v_reuseFailAlloc_1973_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1972_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1970_,
                );
                v___y_1930_ = v___x_1972_;
                state = 11;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6_spec__13_spec__18_spec__24(
    mut v_aig_1976_: *mut leanh::LeanObject,
    mut v_input_1977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1988_: u8 = 0;
    let mut v_gate_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1993_: u8 = 0;
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1997_: u8 = 0;
    let mut v_gate_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2001_: u8 = 0;
    let mut v___x_2002_: u8 = 0;
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2006_: u8 = 0;
    let mut v_res_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2013_: u8 = 0;
    let mut v_aig_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2019_: u8 = 0;
    let mut v___x_2020_: u8 = 0;
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2024_: u8 = 0;
    let mut v_aig_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2030_: u8 = 0;
    let mut v___x_2031_: u8 = 0;
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2035_: u8 = 0;
    let mut v_lhs_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2040_: u8 = 0;
    let mut v_gate_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2042_: u8 = 0;
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2045_: u8 = 0;
    let mut v_gate_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2047_: u8 = 0;
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2050_: u8 = 0;
    let mut v___y_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: u8 = 0;
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: u8 = 0;
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: u8 = 0;
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: u8 = 0;
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2075_: u8 = 0;
    let mut v_isSharedCheck_2076_: u8 = 0;
    let mut v_isSharedCheck_2077_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_input_1977_);
                v_res_2007_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(v_aig_1976_, v_input_1977_);
                v_aig_2008_ = leanh::lean_ctor_get(v_res_2007_, 0);
                leanh::lean_inc_ref(v_aig_2008_);
                v_ref_2009_ = leanh::lean_ctor_get(v_res_2007_, 1);
                leanh::lean_inc_ref(v_ref_2009_);
                leanh::lean_dec_ref(v_res_2007_);
                v_lhs_2036_ = leanh::lean_ctor_get(v_input_1977_, 0);
                v_rhs_2037_ = leanh::lean_ctor_get(v_input_1977_, 1);
                v_isSharedCheck_2077_ = (!leanh::lean_is_exclusive(v_input_1977_)) as u8;
                if v_isSharedCheck_2077_ == 0 {
                    v___x_2039_ = v_input_1977_;
                    v_isShared_2040_ = v_isSharedCheck_2077_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_rhs_2037_);
                    leanh::lean_inc(v_lhs_2036_);
                    leanh::lean_dec(v_input_1977_);
                    v___x_2039_ = leanh::lean_box(0);
                    v_isShared_2040_ = v_isSharedCheck_2077_;
                    state = 12;
                    continue;
                }
            }
            1 => {
                v___x_1982_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1982_, 0, v___y_1979_);
                leanh::lean_ctor_set(v___x_1982_, 1, v___y_1981_);
                v___x_1983_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(v___y_1980_, v___x_1982_);
                return v___x_1983_;
            }
            2 => {
                v_invert_1988_ = leanh::lean_ctor_get_uint8(
                    v___y_1986_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1988_ == 0 {
                    v_gate_1989_ = leanh::lean_ctor_get(v___y_1986_, 0);
                    v_isSharedCheck_1997_ = (!leanh::lean_is_exclusive(v___y_1986_)) as u8;
                    if v_isSharedCheck_1997_ == 0 {
                        v___x_1991_ = v___y_1986_;
                        v_isShared_1992_ = v_isSharedCheck_1997_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_1989_);
                        leanh::lean_dec(v___y_1986_);
                        v___x_1991_ = leanh::lean_box(0);
                        v_isShared_1992_ = v_isSharedCheck_1997_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_gate_1998_ = leanh::lean_ctor_get(v___y_1986_, 0);
                    v_isSharedCheck_2006_ = (!leanh::lean_is_exclusive(v___y_1986_)) as u8;
                    if v_isSharedCheck_2006_ == 0 {
                        v___x_2000_ = v___y_1986_;
                        v_isShared_2001_ = v_isSharedCheck_2006_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_1998_);
                        leanh::lean_dec(v___y_1986_);
                        v___x_2000_ = leanh::lean_box(0);
                        v_isShared_2001_ = v_isSharedCheck_2006_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1993_ = 1;
                if v_isShared_1992_ == 0 {
                    v___x_1995_ = v___x_1991_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1996_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_gate_1989_);
                    v___x_1995_ = v_reuseFailAlloc_1996_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1995_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1993_,
                );
                v___y_1979_ = v___y_1987_;
                v___y_1980_ = v___y_1985_;
                v___y_1981_ = v___x_1995_;
                state = 1;
                continue;
            }
            5 => {
                v___x_2002_ = 0;
                if v_isShared_2001_ == 0 {
                    v___x_2004_ = v___x_2000_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2005_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_gate_1998_);
                    v___x_2004_ = v_reuseFailAlloc_2005_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2004_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2002_,
                );
                v___y_1979_ = v___y_1987_;
                v___y_1980_ = v___y_1985_;
                v___y_1981_ = v___x_2004_;
                state = 1;
                continue;
            }
            7 => {
                v_res_2012_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(v_aig_2008_, v___y_2011_);
                v_invert_2013_ = leanh::lean_ctor_get_uint8(
                    v_ref_2009_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_2013_ == 0 {
                    v_aig_2014_ = leanh::lean_ctor_get(v_res_2012_, 0);
                    leanh::lean_inc_ref(v_aig_2014_);
                    v_ref_2015_ = leanh::lean_ctor_get(v_res_2012_, 1);
                    leanh::lean_inc_ref(v_ref_2015_);
                    leanh::lean_dec_ref(v_res_2012_);
                    v_gate_2016_ = leanh::lean_ctor_get(v_ref_2009_, 0);
                    v_isSharedCheck_2024_ = (!leanh::lean_is_exclusive(v_ref_2009_)) as u8;
                    if v_isSharedCheck_2024_ == 0 {
                        v___x_2018_ = v_ref_2009_;
                        v_isShared_2019_ = v_isSharedCheck_2024_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_2016_);
                        leanh::lean_dec(v_ref_2009_);
                        v___x_2018_ = leanh::lean_box(0);
                        v_isShared_2019_ = v_isSharedCheck_2024_;
                        state = 8;
                        continue;
                    }
                } else {
                    v_aig_2025_ = leanh::lean_ctor_get(v_res_2012_, 0);
                    leanh::lean_inc_ref(v_aig_2025_);
                    v_ref_2026_ = leanh::lean_ctor_get(v_res_2012_, 1);
                    leanh::lean_inc_ref(v_ref_2026_);
                    leanh::lean_dec_ref(v_res_2012_);
                    v_gate_2027_ = leanh::lean_ctor_get(v_ref_2009_, 0);
                    v_isSharedCheck_2035_ = (!leanh::lean_is_exclusive(v_ref_2009_)) as u8;
                    if v_isSharedCheck_2035_ == 0 {
                        v___x_2029_ = v_ref_2009_;
                        v_isShared_2030_ = v_isSharedCheck_2035_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_2027_);
                        leanh::lean_dec(v_ref_2009_);
                        v___x_2029_ = leanh::lean_box(0);
                        v_isShared_2030_ = v_isSharedCheck_2035_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_2020_ = 1;
                if v_isShared_2019_ == 0 {
                    v___x_2022_ = v___x_2018_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2023_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_gate_2016_);
                    v___x_2022_ = v_reuseFailAlloc_2023_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2022_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2020_,
                );
                v___y_1985_ = v_aig_2014_;
                v___y_1986_ = v_ref_2015_;
                v___y_1987_ = v___x_2022_;
                state = 2;
                continue;
            }
            10 => {
                v___x_2031_ = 0;
                if v_isShared_2030_ == 0 {
                    v___x_2033_ = v___x_2029_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2034_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_gate_2027_);
                    v___x_2033_ = v_reuseFailAlloc_2034_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2033_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2031_,
                );
                v___y_1985_ = v_aig_2025_;
                v___y_1986_ = v_ref_2026_;
                v___y_1987_ = v___x_2033_;
                state = 2;
                continue;
            }
            12 => {
                v_gate_2041_ = leanh::lean_ctor_get(v_lhs_2036_, 0);
                v_invert_2042_ = leanh::lean_ctor_get_uint8(
                    v_lhs_2036_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2076_ = (!leanh::lean_is_exclusive(v_lhs_2036_)) as u8;
                if v_isSharedCheck_2076_ == 0 {
                    v___x_2044_ = v_lhs_2036_;
                    v_isShared_2045_ = v_isSharedCheck_2076_;
                    state = 13;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2041_);
                    leanh::lean_dec(v_lhs_2036_);
                    v___x_2044_ = leanh::lean_box(0);
                    v_isShared_2045_ = v_isSharedCheck_2076_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_gate_2046_ = leanh::lean_ctor_get(v_rhs_2037_, 0);
                v_invert_2047_ = leanh::lean_ctor_get_uint8(
                    v_rhs_2037_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2075_ = (!leanh::lean_is_exclusive(v_rhs_2037_)) as u8;
                if v_isSharedCheck_2075_ == 0 {
                    v___x_2049_ = v_rhs_2037_;
                    v_isShared_2050_ = v_isSharedCheck_2075_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2046_);
                    leanh::lean_dec(v_rhs_2037_);
                    v___x_2049_ = leanh::lean_box(0);
                    v_isShared_2050_ = v_isSharedCheck_2075_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_invert_2042_ == 0 {
                    v___x_2067_ = 1;
                    if v_isShared_2045_ == 0 {
                        v___x_2069_ = v___x_2044_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_2070_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_gate_2041_);
                        v___x_2069_ = v_reuseFailAlloc_2070_;
                        state = 20;
                        continue;
                    }
                } else {
                    v___x_2071_ = 0;
                    if v_isShared_2045_ == 0 {
                        v___x_2073_ = v___x_2044_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_2074_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_gate_2041_);
                        v___x_2073_ = v_reuseFailAlloc_2074_;
                        state = 21;
                        continue;
                    }
                }
            }
            15 => {
                if v_invert_2047_ == 0 {
                    v___x_2053_ = 1;
                    if v_isShared_2050_ == 0 {
                        v___x_2055_ = v___x_2049_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_2059_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_gate_2046_);
                        v___x_2055_ = v_reuseFailAlloc_2059_;
                        state = 16;
                        continue;
                    }
                } else {
                    v___x_2060_ = 0;
                    if v_isShared_2050_ == 0 {
                        v___x_2062_ = v___x_2049_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_2066_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_gate_2046_);
                        v___x_2062_ = v_reuseFailAlloc_2066_;
                        state = 18;
                        continue;
                    }
                }
            }
            16 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2055_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2053_,
                );
                if v_isShared_2040_ == 0 {
                    leanh::lean_ctor_set(v___x_2039_, 1, v___x_2055_);
                    leanh::lean_ctor_set(v___x_2039_, 0, v___y_2052_);
                    v___x_2057_ = v___x_2039_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2058_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___y_2052_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2058_, 1, v___x_2055_);
                    v___x_2057_ = v_reuseFailAlloc_2058_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___y_2011_ = v___x_2057_;
                state = 7;
                continue;
            }
            18 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2062_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2060_,
                );
                if v_isShared_2040_ == 0 {
                    leanh::lean_ctor_set(v___x_2039_, 1, v___x_2062_);
                    leanh::lean_ctor_set(v___x_2039_, 0, v___y_2052_);
                    v___x_2064_ = v___x_2039_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2065_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___y_2052_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 1, v___x_2062_);
                    v___x_2064_ = v_reuseFailAlloc_2065_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___y_2011_ = v___x_2064_;
                state = 7;
                continue;
            }
            20 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2069_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2067_,
                );
                v___y_2052_ = v___x_2069_;
                state = 15;
                continue;
            }
            21 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2073_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2071_,
                );
                v___y_2052_ = v___x_2073_;
                state = 15;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6_spec__13_spec__18(
    mut v_aig_2078_: *mut leanh::LeanObject,
    mut v_input_2079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2089_: u8 = 0;
    let mut v_gate_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2091_: u8 = 0;
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2094_: u8 = 0;
    let mut v_gate_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2096_: u8 = 0;
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2099_: u8 = 0;
    let mut v_gate_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2101_: u8 = 0;
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2104_: u8 = 0;
    let mut v_cin_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v_lhs_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2126_: u8 = 0;
    let mut v_gate_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2128_: u8 = 0;
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2131_: u8 = 0;
    let mut v_lorRef_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2139_: u8 = 0;
    let mut v_isSharedCheck_2140_: u8 = 0;
    let mut v_reuseFailAlloc_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2144_: u8 = 0;
    let mut v_reuseFailAlloc_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2147_: u8 = 0;
    let mut v_isSharedCheck_2148_: u8 = 0;
    let mut v_isSharedCheck_2149_: u8 = 0;
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_2080_ = leanh::lean_ctor_get(v_input_2079_, 0);
                leanh::lean_inc_ref_n(v_lhs_2080_, 2);
                v_rhs_2081_ = leanh::lean_ctor_get(v_input_2079_, 1);
                leanh::lean_inc_ref_n(v_rhs_2081_, 2);
                v_cin_2082_ = leanh::lean_ctor_get(v_input_2079_, 2);
                leanh::lean_inc_ref(v_cin_2082_);
                leanh::lean_dec_ref(v_input_2079_);
                v___x_2083_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2083_, 0, v_lhs_2080_);
                leanh::lean_ctor_set(v___x_2083_, 1, v_rhs_2081_);
                v_res_2084_ = l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6_spec__13_spec__18_spec__24(v_aig_2078_, v___x_2083_);
                v_aig_2085_ = leanh::lean_ctor_get(v_res_2084_, 0);
                v_ref_2086_ = leanh::lean_ctor_get(v_res_2084_, 1);
                v_isSharedCheck_2150_ = (!leanh::lean_is_exclusive(v_res_2084_)) as u8;
                if v_isSharedCheck_2150_ == 0 {
                    v___x_2088_ = v_res_2084_;
                    v_isShared_2089_ = v_isSharedCheck_2150_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_ref_2086_);
                    leanh::lean_inc(v_aig_2085_);
                    leanh::lean_dec(v_res_2084_);
                    v___x_2088_ = leanh::lean_box(0);
                    v_isShared_2089_ = v_isSharedCheck_2150_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_2090_ = leanh::lean_ctor_get(v_lhs_2080_, 0);
                v_invert_2091_ = leanh::lean_ctor_get_uint8(
                    v_lhs_2080_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2149_ = (!leanh::lean_is_exclusive(v_lhs_2080_)) as u8;
                if v_isSharedCheck_2149_ == 0 {
                    v___x_2093_ = v_lhs_2080_;
                    v_isShared_2094_ = v_isSharedCheck_2149_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2090_);
                    leanh::lean_dec(v_lhs_2080_);
                    v___x_2093_ = leanh::lean_box(0);
                    v_isShared_2094_ = v_isSharedCheck_2149_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_2095_ = leanh::lean_ctor_get(v_rhs_2081_, 0);
                v_invert_2096_ = leanh::lean_ctor_get_uint8(
                    v_rhs_2081_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2148_ = (!leanh::lean_is_exclusive(v_rhs_2081_)) as u8;
                if v_isSharedCheck_2148_ == 0 {
                    v___x_2098_ = v_rhs_2081_;
                    v_isShared_2099_ = v_isSharedCheck_2148_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2095_);
                    leanh::lean_dec(v_rhs_2081_);
                    v___x_2098_ = leanh::lean_box(0);
                    v_isShared_2099_ = v_isSharedCheck_2148_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_gate_2100_ = leanh::lean_ctor_get(v_cin_2082_, 0);
                v_invert_2101_ = leanh::lean_ctor_get_uint8(
                    v_cin_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2147_ = (!leanh::lean_is_exclusive(v_cin_2082_)) as u8;
                if v_isSharedCheck_2147_ == 0 {
                    v___x_2103_ = v_cin_2082_;
                    v_isShared_2104_ = v_isSharedCheck_2147_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2100_);
                    leanh::lean_dec(v_cin_2082_);
                    v___x_2103_ = leanh::lean_box(0);
                    v_isShared_2104_ = v_isSharedCheck_2147_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2104_ == 0 {
                    v_cin_2106_ = v___x_2103_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2146_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_gate_2100_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2146_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_invert_2101_,
                    );
                    v_cin_2106_ = v_reuseFailAlloc_2146_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2089_ == 0 {
                    leanh::lean_ctor_set(v___x_2088_, 1, v_cin_2106_);
                    leanh::lean_ctor_set(v___x_2088_, 0, v_ref_2086_);
                    v___x_2108_ = v___x_2088_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2145_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_ref_2086_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_cin_2106_);
                    v___x_2108_ = v_reuseFailAlloc_2145_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_res_2109_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(v_aig_2085_, v___x_2108_);
                v_aig_2110_ = leanh::lean_ctor_get(v_res_2109_, 0);
                v_ref_2111_ = leanh::lean_ctor_get(v_res_2109_, 1);
                v_isSharedCheck_2144_ = (!leanh::lean_is_exclusive(v_res_2109_)) as u8;
                if v_isSharedCheck_2144_ == 0 {
                    v___x_2113_ = v_res_2109_;
                    v_isShared_2114_ = v_isSharedCheck_2144_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_ref_2111_);
                    leanh::lean_inc(v_aig_2110_);
                    leanh::lean_dec(v_res_2109_);
                    v___x_2113_ = leanh::lean_box(0);
                    v_isShared_2114_ = v_isSharedCheck_2144_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2099_ == 0 {
                    leanh::lean_ctor_set(v___x_2098_, 0, v_gate_2090_);
                    v_lhs_2116_ = v___x_2098_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2143_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_gate_2090_);
                    v_lhs_2116_ = v_reuseFailAlloc_2143_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                leanh::lean_ctor_set_uint8(
                    v_lhs_2116_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_invert_2091_,
                );
                if v_isShared_2094_ == 0 {
                    leanh::lean_ctor_set(v___x_2093_, 0, v_gate_2095_);
                    v_rhs_2118_ = v___x_2093_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2142_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_gate_2095_);
                    v_rhs_2118_ = v_reuseFailAlloc_2142_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                leanh::lean_ctor_set_uint8(
                    v_rhs_2118_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_invert_2096_,
                );
                if v_isShared_2114_ == 0 {
                    leanh::lean_ctor_set(v___x_2113_, 1, v_rhs_2118_);
                    leanh::lean_ctor_set(v___x_2113_, 0, v_lhs_2116_);
                    v___x_2120_ = v___x_2113_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2141_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_lhs_2116_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_rhs_2118_);
                    v___x_2120_ = v_reuseFailAlloc_2141_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_res_2121_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(v_aig_2110_, v___x_2120_);
                v_aig_2122_ = leanh::lean_ctor_get(v_res_2121_, 0);
                v_ref_2123_ = leanh::lean_ctor_get(v_res_2121_, 1);
                v_isSharedCheck_2140_ = (!leanh::lean_is_exclusive(v_res_2121_)) as u8;
                if v_isSharedCheck_2140_ == 0 {
                    v___x_2125_ = v_res_2121_;
                    v_isShared_2126_ = v_isSharedCheck_2140_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_inc(v_ref_2123_);
                    leanh::lean_inc(v_aig_2122_);
                    leanh::lean_dec(v_res_2121_);
                    v___x_2125_ = leanh::lean_box(0);
                    v_isShared_2126_ = v_isSharedCheck_2140_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_gate_2127_ = leanh::lean_ctor_get(v_ref_2111_, 0);
                v_invert_2128_ = leanh::lean_ctor_get_uint8(
                    v_ref_2111_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2139_ = (!leanh::lean_is_exclusive(v_ref_2111_)) as u8;
                if v_isSharedCheck_2139_ == 0 {
                    v___x_2130_ = v_ref_2111_;
                    v_isShared_2131_ = v_isSharedCheck_2139_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2127_);
                    leanh::lean_dec(v_ref_2111_);
                    v___x_2130_ = leanh::lean_box(0);
                    v_isShared_2131_ = v_isSharedCheck_2139_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_2131_ == 0 {
                    v_lorRef_2133_ = v___x_2130_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2138_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_gate_2127_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2138_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_invert_2128_,
                    );
                    v_lorRef_2133_ = v_reuseFailAlloc_2138_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_2126_ == 0 {
                    leanh::lean_ctor_set(v___x_2125_, 0, v_lorRef_2133_);
                    v___x_2135_ = v___x_2125_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2137_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_lorRef_2133_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_ref_2123_);
                    v___x_2135_ = v_reuseFailAlloc_2137_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2136_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6_spec__13_spec__18_spec__25(v_aig_2122_, v___x_2135_);
                return v___x_2136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6_spec__13(
    mut v_w_2151_: *mut leanh::LeanObject,
    mut v_aig_2152_: *mut leanh::LeanObject,
    mut v_lhs_2153_: *mut leanh::LeanObject,
    mut v_rhs_2154_: *mut leanh::LeanObject,
    mut v_curr_2155_: *mut leanh::LeanObject,
    mut v_cin_2156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: u8 = 0;
    let mut v___y_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: u8 = 0;
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: u8 = 0;
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: u8 = 0;
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: u8 = 0;
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2167_ = lean_nat_dec_lt(v_curr_2155_, v_w_2151_);
                if v___x_2167_ == 0 {
                    leanh::lean_dec(v_curr_2155_);
                    v___x_2179_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2179_, 0, v_aig_2152_);
                    leanh::lean_ctor_set(v___x_2179_, 1, v_cin_2156_);
                    return v___x_2179_;
                } else {
                    v_ref_2180_ = lean_array_fget_borrowed(v_lhs_2153_, v_curr_2155_);
                    v___x_2181_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2182_ = lean_nat_shiftr(v_ref_2180_, v___x_2181_);
                    v___x_2183_ = lean_nat_land(v___x_2181_, v_ref_2180_);
                    v___x_2184_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2185_ = lean_nat_dec_eq(v___x_2183_, v___x_2184_);
                    leanh::lean_dec(v___x_2183_);
                    if v___x_2185_ == 0 {
                        v___x_2186_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_2186_, 0, v___x_2182_);
                        leanh::lean_ctor_set_uint8(
                            v___x_2186_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_2167_,
                        );
                        v___y_2169_ = v___x_2186_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2187_ = 0;
                        v___x_2188_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_2188_, 0, v___x_2182_);
                        leanh::lean_ctor_set_uint8(
                            v___x_2188_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_2187_,
                        );
                        v___y_2169_ = v___x_2188_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2160_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2160_, 0, v___y_2158_);
                leanh::lean_ctor_set(v___x_2160_, 1, v___y_2159_);
                leanh::lean_ctor_set(v___x_2160_, 2, v_cin_2156_);
                v_res_2161_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6_spec__13_spec__18(v_aig_2152_, v___x_2160_);
                v_aig_2162_ = leanh::lean_ctor_get(v_res_2161_, 0);
                leanh::lean_inc_ref(v_aig_2162_);
                v_ref_2163_ = leanh::lean_ctor_get(v_res_2161_, 1);
                leanh::lean_inc_ref(v_ref_2163_);
                leanh::lean_dec_ref(v_res_2161_);
                v___x_2164_ = leanh::lean_unsigned_to_nat(1);
                v___x_2165_ = lean_nat_add(v_curr_2155_, v___x_2164_);
                leanh::lean_dec(v_curr_2155_);
                v_aig_2152_ = v_aig_2162_;
                v_curr_2155_ = v___x_2165_;
                v_cin_2156_ = v_ref_2163_;
                state = 0;
                continue;
            }
            2 => {
                v_ref_2170_ = lean_array_fget_borrowed(v_rhs_2154_, v_curr_2155_);
                v___x_2171_ = leanh::lean_unsigned_to_nat(1);
                v___x_2172_ = lean_nat_shiftr(v_ref_2170_, v___x_2171_);
                v___x_2173_ = lean_nat_land(v___x_2171_, v_ref_2170_);
                v___x_2174_ = leanh::lean_unsigned_to_nat(0);
                v___x_2175_ = lean_nat_dec_eq(v___x_2173_, v___x_2174_);
                leanh::lean_dec(v___x_2173_);
                if v___x_2175_ == 0 {
                    v___x_2176_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_2176_, 0, v___x_2172_);
                    leanh::lean_ctor_set_uint8(
                        v___x_2176_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_2167_,
                    );
                    v___y_2158_ = v___y_2169_;
                    v___y_2159_ = v___x_2176_;
                    state = 1;
                    continue;
                } else {
                    v___x_2177_ = 0;
                    v___x_2178_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_2178_, 0, v___x_2172_);
                    leanh::lean_ctor_set_uint8(
                        v___x_2178_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_2177_,
                    );
                    v___y_2158_ = v___y_2169_;
                    v___y_2159_ = v___x_2178_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6_spec__13___boxed(
    mut v_w_2189_: *mut leanh::LeanObject,
    mut v_aig_2190_: *mut leanh::LeanObject,
    mut v_lhs_2191_: *mut leanh::LeanObject,
    mut v_rhs_2192_: *mut leanh::LeanObject,
    mut v_curr_2193_: *mut leanh::LeanObject,
    mut v_cin_2194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2195_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6_spec__13(v_w_2189_, v_aig_2190_, v_lhs_2191_, v_rhs_2192_, v_curr_2193_, v_cin_2194_);
    leanh::lean_dec_ref(v_rhs_2192_);
    leanh::lean_dec_ref(v_lhs_2191_);
    leanh::lean_dec(v_w_2189_);
    return v_res_2195_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6(
    mut v_aig_2196_: *mut leanh::LeanObject,
    mut v_input_2197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vec_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_w_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_vec_2198_ = leanh::lean_ctor_get(v_input_2197_, 1);
    leanh::lean_inc_ref(v_vec_2198_);
    v_w_2199_ = leanh::lean_ctor_get(v_input_2197_, 0);
    leanh::lean_inc(v_w_2199_);
    v_cin_2200_ = leanh::lean_ctor_get(v_input_2197_, 2);
    leanh::lean_inc_ref(v_cin_2200_);
    leanh::lean_dec_ref(v_input_2197_);
    v_lhs_2201_ = leanh::lean_ctor_get(v_vec_2198_, 0);
    leanh::lean_inc_ref(v_lhs_2201_);
    v_rhs_2202_ = leanh::lean_ctor_get(v_vec_2198_, 1);
    leanh::lean_inc_ref(v_rhs_2202_);
    leanh::lean_dec_ref(v_vec_2198_);
    v___x_2203_ = leanh::lean_unsigned_to_nat(0);
    v___x_2204_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6_spec__13(v_w_2199_, v_aig_2196_, v_lhs_2201_, v_rhs_2202_, v___x_2203_, v_cin_2200_);
    leanh::lean_dec_ref(v_rhs_2202_);
    leanh::lean_dec_ref(v_lhs_2201_);
    leanh::lean_dec(v_w_2199_);
    return v___x_2204_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1(
    mut v_w_2205_: *mut leanh::LeanObject,
    mut v_aig_2206_: *mut leanh::LeanObject,
    mut v_pair_2207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2212_: u8 = 0;
    let mut v_res_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: u8 = 0;
    let mut v_trueRef_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2223_: u8 = 0;
    let mut v_aig_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2227_: u8 = 0;
    let mut v_gate_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2231_: u8 = 0;
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2238_: u8 = 0;
    let mut v_isSharedCheck_2239_: u8 = 0;
    let mut v_unused_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2244_: u8 = 0;
    let mut v_gate_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2248_: u8 = 0;
    let mut v___x_2249_: u8 = 0;
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2256_: u8 = 0;
    let mut v_isSharedCheck_2257_: u8 = 0;
    let mut v_unused_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2260_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_2208_ = leanh::lean_ctor_get(v_pair_2207_, 0);
                v_rhs_2209_ = leanh::lean_ctor_get(v_pair_2207_, 1);
                v_isSharedCheck_2260_ = (!leanh::lean_is_exclusive(v_pair_2207_)) as u8;
                if v_isSharedCheck_2260_ == 0 {
                    v___x_2211_ = v_pair_2207_;
                    v_isShared_2212_ = v_isSharedCheck_2260_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rhs_2209_);
                    leanh::lean_inc(v_lhs_2208_);
                    leanh::lean_dec(v_pair_2207_);
                    v___x_2211_ = leanh::lean_box(0);
                    v_isShared_2212_ = v_isSharedCheck_2260_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_res_2213_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5(v_w_2205_, v_aig_2206_, v_rhs_2209_);
                v_aig_2214_ = leanh::lean_ctor_get(v_res_2213_, 0);
                leanh::lean_inc_ref(v_aig_2214_);
                v_vec_2215_ = leanh::lean_ctor_get(v_res_2213_, 1);
                leanh::lean_inc_ref(v_vec_2215_);
                leanh::lean_dec_ref(v_res_2213_);
                v___x_2216_ = 1;
                v_trueRef_2217_ = l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg___closed__0;
                if v_isShared_2212_ == 0 {
                    leanh::lean_ctor_set(v___x_2211_, 1, v_vec_2215_);
                    v___x_2219_ = v___x_2211_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2259_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_lhs_2208_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2259_, 1, v_vec_2215_);
                    v___x_2219_ = v_reuseFailAlloc_2259_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2220_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2220_, 0, v_w_2205_);
                leanh::lean_ctor_set(v___x_2220_, 1, v___x_2219_);
                leanh::lean_ctor_set(v___x_2220_, 2, v_trueRef_2217_);
                v_res_2221_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6(v_aig_2214_, v___x_2220_);
                v_ref_2222_ = leanh::lean_ctor_get(v_res_2221_, 1);
                leanh::lean_inc_ref(v_ref_2222_);
                v_invert_2223_ = leanh::lean_ctor_get_uint8(
                    v_ref_2222_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_2223_ == 0 {
                    v_aig_2224_ = leanh::lean_ctor_get(v_res_2221_, 0);
                    v_isSharedCheck_2239_ = (!leanh::lean_is_exclusive(v_res_2221_)) as u8;
                    if v_isSharedCheck_2239_ == 0 {
                        v_unused_2240_ = leanh::lean_ctor_get(v_res_2221_, 1);
                        leanh::lean_dec(v_unused_2240_);
                        v___x_2226_ = v_res_2221_;
                        v_isShared_2227_ = v_isSharedCheck_2239_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_aig_2224_);
                        leanh::lean_dec(v_res_2221_);
                        v___x_2226_ = leanh::lean_box(0);
                        v_isShared_2227_ = v_isSharedCheck_2239_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_aig_2241_ = leanh::lean_ctor_get(v_res_2221_, 0);
                    v_isSharedCheck_2257_ = (!leanh::lean_is_exclusive(v_res_2221_)) as u8;
                    if v_isSharedCheck_2257_ == 0 {
                        v_unused_2258_ = leanh::lean_ctor_get(v_res_2221_, 1);
                        leanh::lean_dec(v_unused_2258_);
                        v___x_2243_ = v_res_2221_;
                        v_isShared_2244_ = v_isSharedCheck_2257_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_aig_2241_);
                        leanh::lean_dec(v_res_2221_);
                        v___x_2243_ = leanh::lean_box(0);
                        v_isShared_2244_ = v_isSharedCheck_2257_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v_gate_2228_ = leanh::lean_ctor_get(v_ref_2222_, 0);
                v_isSharedCheck_2238_ = (!leanh::lean_is_exclusive(v_ref_2222_)) as u8;
                if v_isSharedCheck_2238_ == 0 {
                    v___x_2230_ = v_ref_2222_;
                    v_isShared_2231_ = v_isSharedCheck_2238_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2228_);
                    leanh::lean_dec(v_ref_2222_);
                    v___x_2230_ = leanh::lean_box(0);
                    v_isShared_2231_ = v_isSharedCheck_2238_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2231_ == 0 {
                    v___x_2233_ = v___x_2230_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2237_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_gate_2228_);
                    v___x_2233_ = v_reuseFailAlloc_2237_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2233_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2216_,
                );
                if v_isShared_2227_ == 0 {
                    leanh::lean_ctor_set(v___x_2226_, 1, v___x_2233_);
                    v___x_2235_ = v___x_2226_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2236_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_aig_2224_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2233_);
                    v___x_2235_ = v_reuseFailAlloc_2236_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2235_;
            }
            7 => {
                v_gate_2245_ = leanh::lean_ctor_get(v_ref_2222_, 0);
                v_isSharedCheck_2256_ = (!leanh::lean_is_exclusive(v_ref_2222_)) as u8;
                if v_isSharedCheck_2256_ == 0 {
                    v___x_2247_ = v_ref_2222_;
                    v_isShared_2248_ = v_isSharedCheck_2256_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2245_);
                    leanh::lean_dec(v_ref_2222_);
                    v___x_2247_ = leanh::lean_box(0);
                    v_isShared_2248_ = v_isSharedCheck_2256_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2249_ = 0;
                if v_isShared_2248_ == 0 {
                    v___x_2251_ = v___x_2247_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2255_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_gate_2245_);
                    v___x_2251_ = v_reuseFailAlloc_2255_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2251_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2249_,
                );
                if v_isShared_2244_ == 0 {
                    leanh::lean_ctor_set(v___x_2243_, 1, v___x_2251_);
                    v___x_2253_ = v___x_2243_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2254_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_aig_2241_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2254_, 1, v___x_2251_);
                    v___x_2253_ = v_reuseFailAlloc_2254_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_bitblast(
    mut v_aig_2261_: *mut leanh::LeanObject,
    mut v_input_2262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2267_: u8 = 0;
    let mut v_w_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_op_2270_: u8 = 0;
    let mut v_rhs_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2281_: u8 = 0;
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2289_: u8 = 0;
    let mut v_aig_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2294_: u8 = 0;
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2302_: u8 = 0;
    let mut v_isSharedCheck_2303_: u8 = 0;
    let mut v_unused_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2308_: u8 = 0;
    let mut v_aig_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2313_: u8 = 0;
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2321_: u8 = 0;
    let mut v_isSharedCheck_2322_: u8 = 0;
    let mut v_unused_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2325_: u8 = 0;
    let mut v_reuseFailAlloc_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2327_: u8 = 0;
    let mut v_unused_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2332_: u8 = 0;
    let mut v_w_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2338_: u8 = 0;
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2346_: u8 = 0;
    let mut v_aig_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2351_: u8 = 0;
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2362_: u8 = 0;
    let mut v_isSharedCheck_2363_: u8 = 0;
    let mut v_reuseFailAlloc_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2365_: u8 = 0;
    let mut v_isSharedCheck_2366_: u8 = 0;
    let mut v_unused_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_val_2263_ = leanh::lean_ctor_get(v_input_2262_, 0);
                leanh::lean_inc(v_val_2263_);
                if leanh::lean_obj_tag(v_val_2263_) == 0 {
                    v_cache_2264_ = leanh::lean_ctor_get(v_input_2262_, 1);
                    v_isSharedCheck_2327_ = (!leanh::lean_is_exclusive(v_input_2262_)) as u8;
                    if v_isSharedCheck_2327_ == 0 {
                        v_unused_2328_ = leanh::lean_ctor_get(v_input_2262_, 0);
                        leanh::lean_dec(v_unused_2328_);
                        v___x_2266_ = v_input_2262_;
                        v_isShared_2267_ = v_isSharedCheck_2327_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_cache_2264_);
                        leanh::lean_dec(v_input_2262_);
                        v___x_2266_ = leanh::lean_box(0);
                        v_isShared_2267_ = v_isSharedCheck_2327_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_cache_2329_ = leanh::lean_ctor_get(v_input_2262_, 1);
                    v_isSharedCheck_2366_ = (!leanh::lean_is_exclusive(v_input_2262_)) as u8;
                    if v_isSharedCheck_2366_ == 0 {
                        v_unused_2367_ = leanh::lean_ctor_get(v_input_2262_, 0);
                        leanh::lean_dec(v_unused_2367_);
                        v___x_2331_ = v_input_2262_;
                        v_isShared_2332_ = v_isSharedCheck_2366_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_cache_2329_);
                        leanh::lean_dec(v_input_2262_);
                        v___x_2331_ = leanh::lean_box(0);
                        v_isShared_2332_ = v_isSharedCheck_2366_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v_w_2268_ = leanh::lean_ctor_get(v_val_2263_, 0);
                leanh::lean_inc(v_w_2268_);
                v_lhs_2269_ = leanh::lean_ctor_get(v_val_2263_, 1);
                leanh::lean_inc_ref(v_lhs_2269_);
                v_op_2270_ = leanh::lean_ctor_get_uint8(
                    v_val_2263_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_rhs_2271_ = leanh::lean_ctor_get(v_val_2263_, 2);
                leanh::lean_inc_ref(v_rhs_2271_);
                leanh::lean_dec_ref_known(v_val_2263_, 3);
                if v_isShared_2267_ == 0 {
                    leanh::lean_ctor_set(v___x_2266_, 0, v_lhs_2269_);
                    v___x_2273_ = v___x_2266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2326_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_lhs_2269_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_cache_2264_);
                    v___x_2273_ = v_reuseFailAlloc_2326_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_w_2268_);
                v___x_2274_ =
                    l_Std_Tactic_BVDecide_BVExpr_bitblast(v_w_2268_, v_aig_2261_, v___x_2273_);
                v_result_2275_ = leanh::lean_ctor_get(v___x_2274_, 0);
                leanh::lean_inc_ref(v_result_2275_);
                v_cache_2276_ = leanh::lean_ctor_get(v___x_2274_, 1);
                leanh::lean_inc_ref(v_cache_2276_);
                leanh::lean_dec_ref(v___x_2274_);
                v_aig_2277_ = leanh::lean_ctor_get(v_result_2275_, 0);
                v_vec_2278_ = leanh::lean_ctor_get(v_result_2275_, 1);
                v_isSharedCheck_2325_ = (!leanh::lean_is_exclusive(v_result_2275_)) as u8;
                if v_isSharedCheck_2325_ == 0 {
                    v___x_2280_ = v_result_2275_;
                    v_isShared_2281_ = v_isSharedCheck_2325_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_vec_2278_);
                    leanh::lean_inc(v_aig_2277_);
                    leanh::lean_dec(v_result_2275_);
                    v___x_2280_ = leanh::lean_box(0);
                    v_isShared_2281_ = v_isSharedCheck_2325_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2281_ == 0 {
                    leanh::lean_ctor_set(v___x_2280_, 1, v_cache_2276_);
                    leanh::lean_ctor_set(v___x_2280_, 0, v_rhs_2271_);
                    v___x_2283_ = v___x_2280_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2324_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_rhs_2271_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_cache_2276_);
                    v___x_2283_ = v_reuseFailAlloc_2324_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc(v_w_2268_);
                v___x_2284_ =
                    l_Std_Tactic_BVDecide_BVExpr_bitblast(v_w_2268_, v_aig_2277_, v___x_2283_);
                v_result_2285_ = leanh::lean_ctor_get(v___x_2284_, 0);
                leanh::lean_inc_ref(v_result_2285_);
                if v_op_2270_ == 0 {
                    v_cache_2286_ = leanh::lean_ctor_get(v___x_2284_, 1);
                    v_isSharedCheck_2303_ = (!leanh::lean_is_exclusive(v___x_2284_)) as u8;
                    if v_isSharedCheck_2303_ == 0 {
                        v_unused_2304_ = leanh::lean_ctor_get(v___x_2284_, 0);
                        leanh::lean_dec(v_unused_2304_);
                        v___x_2288_ = v___x_2284_;
                        v_isShared_2289_ = v_isSharedCheck_2303_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_cache_2286_);
                        leanh::lean_dec(v___x_2284_);
                        v___x_2288_ = leanh::lean_box(0);
                        v_isShared_2289_ = v_isSharedCheck_2303_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_cache_2305_ = leanh::lean_ctor_get(v___x_2284_, 1);
                    v_isSharedCheck_2322_ = (!leanh::lean_is_exclusive(v___x_2284_)) as u8;
                    if v_isSharedCheck_2322_ == 0 {
                        v_unused_2323_ = leanh::lean_ctor_get(v___x_2284_, 0);
                        leanh::lean_dec(v_unused_2323_);
                        v___x_2307_ = v___x_2284_;
                        v_isShared_2308_ = v_isSharedCheck_2322_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_cache_2305_);
                        leanh::lean_dec(v___x_2284_);
                        v___x_2307_ = leanh::lean_box(0);
                        v_isShared_2308_ = v_isSharedCheck_2322_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v_aig_2290_ = leanh::lean_ctor_get(v_result_2285_, 0);
                v_vec_2291_ = leanh::lean_ctor_get(v_result_2285_, 1);
                v_isSharedCheck_2302_ = (!leanh::lean_is_exclusive(v_result_2285_)) as u8;
                if v_isSharedCheck_2302_ == 0 {
                    v___x_2293_ = v_result_2285_;
                    v_isShared_2294_ = v_isSharedCheck_2302_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_vec_2291_);
                    leanh::lean_inc(v_aig_2290_);
                    leanh::lean_dec(v_result_2285_);
                    v___x_2293_ = leanh::lean_box(0);
                    v_isShared_2294_ = v_isSharedCheck_2302_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2294_ == 0 {
                    leanh::lean_ctor_set(v___x_2293_, 0, v_vec_2278_);
                    v___x_2296_ = v___x_2293_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2301_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_vec_2278_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_vec_2291_);
                    v___x_2296_ = v_reuseFailAlloc_2301_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_res_2297_ = l_Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0(v_w_2268_, v_aig_2290_, v___x_2296_);
                leanh::lean_dec_ref(v___x_2296_);
                leanh::lean_dec(v_w_2268_);
                if v_isShared_2289_ == 0 {
                    leanh::lean_ctor_set(v___x_2288_, 0, v_res_2297_);
                    v___x_2299_ = v___x_2288_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2300_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_res_2297_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_cache_2286_);
                    v___x_2299_ = v_reuseFailAlloc_2300_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2299_;
            }
            9 => {
                v_aig_2309_ = leanh::lean_ctor_get(v_result_2285_, 0);
                v_vec_2310_ = leanh::lean_ctor_get(v_result_2285_, 1);
                v_isSharedCheck_2321_ = (!leanh::lean_is_exclusive(v_result_2285_)) as u8;
                if v_isSharedCheck_2321_ == 0 {
                    v___x_2312_ = v_result_2285_;
                    v_isShared_2313_ = v_isSharedCheck_2321_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc(v_vec_2310_);
                    leanh::lean_inc(v_aig_2309_);
                    leanh::lean_dec(v_result_2285_);
                    v___x_2312_ = leanh::lean_box(0);
                    v_isShared_2313_ = v_isSharedCheck_2321_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_2313_ == 0 {
                    leanh::lean_ctor_set(v___x_2312_, 0, v_vec_2278_);
                    v___x_2315_ = v___x_2312_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2320_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_vec_2278_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_vec_2310_);
                    v___x_2315_ = v_reuseFailAlloc_2320_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_res_2316_ = l_Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1(v_w_2268_, v_aig_2309_, v___x_2315_);
                if v_isShared_2308_ == 0 {
                    leanh::lean_ctor_set(v___x_2307_, 0, v_res_2316_);
                    v___x_2318_ = v___x_2307_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2319_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_res_2316_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_cache_2305_);
                    v___x_2318_ = v_reuseFailAlloc_2319_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2318_;
            }
            13 => {
                v_w_2333_ = leanh::lean_ctor_get(v_val_2263_, 0);
                v_expr_2334_ = leanh::lean_ctor_get(v_val_2263_, 1);
                v_idx_2335_ = leanh::lean_ctor_get(v_val_2263_, 2);
                v_isSharedCheck_2365_ = (!leanh::lean_is_exclusive(v_val_2263_)) as u8;
                if v_isSharedCheck_2365_ == 0 {
                    v___x_2337_ = v_val_2263_;
                    v_isShared_2338_ = v_isSharedCheck_2365_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_idx_2335_);
                    leanh::lean_inc(v_expr_2334_);
                    leanh::lean_inc(v_w_2333_);
                    leanh::lean_dec(v_val_2263_);
                    v___x_2337_ = leanh::lean_box(0);
                    v_isShared_2338_ = v_isSharedCheck_2365_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2332_ == 0 {
                    leanh::lean_ctor_set(v___x_2331_, 0, v_expr_2334_);
                    v___x_2340_ = v___x_2331_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2364_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_expr_2334_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_cache_2329_);
                    v___x_2340_ = v_reuseFailAlloc_2364_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                leanh::lean_inc(v_w_2333_);
                v___x_2341_ =
                    l_Std_Tactic_BVDecide_BVExpr_bitblast(v_w_2333_, v_aig_2261_, v___x_2340_);
                v_result_2342_ = leanh::lean_ctor_get(v___x_2341_, 0);
                v_cache_2343_ = leanh::lean_ctor_get(v___x_2341_, 1);
                v_isSharedCheck_2363_ = (!leanh::lean_is_exclusive(v___x_2341_)) as u8;
                if v_isSharedCheck_2363_ == 0 {
                    v___x_2345_ = v___x_2341_;
                    v_isShared_2346_ = v_isSharedCheck_2363_;
                    state = 16;
                    continue;
                } else {
                    leanh::lean_inc(v_cache_2343_);
                    leanh::lean_inc(v_result_2342_);
                    leanh::lean_dec(v___x_2341_);
                    v___x_2345_ = leanh::lean_box(0);
                    v_isShared_2346_ = v_isSharedCheck_2363_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v_aig_2347_ = leanh::lean_ctor_get(v_result_2342_, 0);
                v_vec_2348_ = leanh::lean_ctor_get(v_result_2342_, 1);
                v_isSharedCheck_2362_ = (!leanh::lean_is_exclusive(v_result_2342_)) as u8;
                if v_isSharedCheck_2362_ == 0 {
                    v___x_2350_ = v_result_2342_;
                    v_isShared_2351_ = v_isSharedCheck_2362_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_vec_2348_);
                    leanh::lean_inc(v_aig_2347_);
                    leanh::lean_dec(v_result_2342_);
                    v___x_2350_ = leanh::lean_box(0);
                    v_isShared_2351_ = v_isSharedCheck_2362_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_2338_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2337_, 0);
                    leanh::lean_ctor_set(v___x_2337_, 1, v_vec_2348_);
                    v___x_2353_ = v___x_2337_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2361_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_w_2333_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2361_, 1, v_vec_2348_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2361_, 2, v_idx_2335_);
                    v___x_2353_ = v_reuseFailAlloc_2361_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v_res_2354_ = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__2___redArg(v___x_2353_);
                leanh::lean_dec_ref(v___x_2353_);
                if v_isShared_2351_ == 0 {
                    leanh::lean_ctor_set(v___x_2350_, 1, v_res_2354_);
                    v___x_2356_ = v___x_2350_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2360_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_aig_2347_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_res_2354_);
                    v___x_2356_ = v_reuseFailAlloc_2360_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2346_ == 0 {
                    leanh::lean_ctor_set(v___x_2345_, 0, v___x_2356_);
                    v___x_2358_ = v___x_2345_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2359_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2356_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_cache_2343_);
                    v___x_2358_ = v_reuseFailAlloc_2359_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2358_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__3___redArg(
    mut v_c_2368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2369_ = lean_mk_empty_array_with_capacity(v_c_2368_);
    return v___x_2369_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_c_2370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2371_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__3___redArg(v_c_2370_);
    leanh::lean_dec(v_c_2370_);
    return v_res_2371_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__3(
    mut v_aig_2372_: *mut leanh::LeanObject,
    mut v_c_2373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2374_ = lean_mk_empty_array_with_capacity(v_c_2373_);
    return v___x_2374_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__3___boxed(
    mut v_aig_2375_: *mut leanh::LeanObject,
    mut v_c_2376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2377_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__3(v_aig_2375_, v_c_2376_);
    leanh::lean_dec(v_c_2376_);
    leanh::lean_dec_ref(v_aig_2375_);
    return v_res_2377_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1(
    mut v_len_2378_: *mut leanh::LeanObject,
    mut v_aig_2379_: *mut leanh::LeanObject,
    mut v_input_2380_: *mut leanh::LeanObject,
    mut v_inst_2381_: *mut leanh::LeanObject,
    mut v_inst_2382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2383_ = l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1___redArg(v_len_2378_, v_aig_2379_, v_input_2380_);
    return v___x_2383_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1___boxed(
    mut v_len_2384_: *mut leanh::LeanObject,
    mut v_aig_2385_: *mut leanh::LeanObject,
    mut v_input_2386_: *mut leanh::LeanObject,
    mut v_inst_2387_: *mut leanh::LeanObject,
    mut v_inst_2388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2389_ = l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1(v_len_2384_, v_aig_2385_, v_input_2386_, v_inst_2387_, v_inst_2388_);
    leanh::lean_dec_ref(v_input_2386_);
    leanh::lean_dec(v_len_2384_);
    return v_res_2389_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3(
    mut v_len_2390_: *mut leanh::LeanObject,
    mut v_aig_2391_: *mut leanh::LeanObject,
    mut v_vec_2392_: *mut leanh::LeanObject,
    mut v_inst_2393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2394_ = l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg(v_len_2390_, v_aig_2391_, v_vec_2392_);
    return v___x_2394_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___boxed(
    mut v_len_2395_: *mut leanh::LeanObject,
    mut v_aig_2396_: *mut leanh::LeanObject,
    mut v_vec_2397_: *mut leanh::LeanObject,
    mut v_inst_2398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2399_ = l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3(v_len_2395_, v_aig_2396_, v_vec_2397_, v_inst_2398_);
    leanh::lean_dec_ref(v_vec_2397_);
    leanh::lean_dec(v_len_2395_);
    return v_res_2399_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__4(
    mut v_len_2400_: *mut leanh::LeanObject,
    mut v_aig_2401_: *mut leanh::LeanObject,
    mut v_idx_2402_: *mut leanh::LeanObject,
    mut v_s_2403_: *mut leanh::LeanObject,
    mut v_hidx_2404_: *mut leanh::LeanObject,
    mut v_lhs_2405_: *mut leanh::LeanObject,
    mut v_rhs_2406_: *mut leanh::LeanObject,
    mut v_inst_2407_: *mut leanh::LeanObject,
    mut v_inst_2408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2409_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__4___redArg(v_len_2400_, v_aig_2401_, v_idx_2402_, v_s_2403_, v_lhs_2405_, v_rhs_2406_);
    return v___x_2409_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__4___boxed(
    mut v_len_2410_: *mut leanh::LeanObject,
    mut v_aig_2411_: *mut leanh::LeanObject,
    mut v_idx_2412_: *mut leanh::LeanObject,
    mut v_s_2413_: *mut leanh::LeanObject,
    mut v_hidx_2414_: *mut leanh::LeanObject,
    mut v_lhs_2415_: *mut leanh::LeanObject,
    mut v_rhs_2416_: *mut leanh::LeanObject,
    mut v_inst_2417_: *mut leanh::LeanObject,
    mut v_inst_2418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2419_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__4(v_len_2410_, v_aig_2411_, v_idx_2412_, v_s_2413_, v_hidx_2414_, v_lhs_2415_, v_rhs_2416_, v_inst_2417_, v_inst_2418_);
    leanh::lean_dec_ref(v_rhs_2416_);
    leanh::lean_dec_ref(v_lhs_2415_);
    leanh::lean_dec(v_len_2410_);
    return v_res_2419_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3_spec__8(
    mut v_aig_2420_: *mut leanh::LeanObject,
    mut v_acc_2421_: *mut leanh::LeanObject,
    mut v_idx_2422_: *mut leanh::LeanObject,
    mut v_len_2423_: *mut leanh::LeanObject,
    mut v_input_2424_: *mut leanh::LeanObject,
    mut v_inst_2425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2426_ = l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3_spec__8___redArg(v_aig_2420_, v_acc_2421_, v_idx_2422_, v_len_2423_, v_input_2424_);
    return v___x_2426_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3_spec__8___boxed(
    mut v_aig_2427_: *mut leanh::LeanObject,
    mut v_acc_2428_: *mut leanh::LeanObject,
    mut v_idx_2429_: *mut leanh::LeanObject,
    mut v_len_2430_: *mut leanh::LeanObject,
    mut v_input_2431_: *mut leanh::LeanObject,
    mut v_inst_2432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2433_ = l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3_spec__8(v_aig_2427_, v_acc_2428_, v_idx_2429_, v_len_2430_, v_input_2431_, v_inst_2432_);
    leanh::lean_dec_ref(v_input_2431_);
    leanh::lean_dec(v_len_2430_);
    return v_res_2433_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8(
    mut v_00_u03b2_2434_: *mut leanh::LeanObject,
    mut v_m_2435_: *mut leanh::LeanObject,
    mut v_a_2436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2437_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8___redArg(v_m_2435_, v_a_2436_);
    return v___x_2437_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8___boxed(
    mut v_00_u03b2_2438_: *mut leanh::LeanObject,
    mut v_m_2439_: *mut leanh::LeanObject,
    mut v_a_2440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2441_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8(v_00_u03b2_2438_, v_m_2439_, v_a_2440_);
    leanh::lean_dec_ref(v_m_2439_);
    return v_res_2441_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10(
    mut v_00_u03b2_2442_: *mut leanh::LeanObject,
    mut v_m_2443_: *mut leanh::LeanObject,
    mut v_a_2444_: *mut leanh::LeanObject,
    mut v_b_2445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2446_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10___redArg(v_m_2443_, v_a_2444_, v_b_2445_);
    return v___x_2446_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11_spec__15(
    mut v___x_2447_: *mut leanh::LeanObject,
    mut v_len_2448_: *mut leanh::LeanObject,
    mut v_aig_2449_: *mut leanh::LeanObject,
    mut v_idx_2450_: *mut leanh::LeanObject,
    mut v_hidx_2451_: *mut leanh::LeanObject,
    mut v_s_2452_: *mut leanh::LeanObject,
    mut v_input_2453_: *mut leanh::LeanObject,
    mut v_inst_2454_: *mut leanh::LeanObject,
    mut v_inst_2455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2456_ = l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11_spec__15___redArg(v___x_2447_, v_len_2448_, v_aig_2449_, v_idx_2450_, v_s_2452_, v_input_2453_);
    return v___x_2456_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11_spec__15___boxed(
    mut v___x_2457_: *mut leanh::LeanObject,
    mut v_len_2458_: *mut leanh::LeanObject,
    mut v_aig_2459_: *mut leanh::LeanObject,
    mut v_idx_2460_: *mut leanh::LeanObject,
    mut v_hidx_2461_: *mut leanh::LeanObject,
    mut v_s_2462_: *mut leanh::LeanObject,
    mut v_input_2463_: *mut leanh::LeanObject,
    mut v_inst_2464_: *mut leanh::LeanObject,
    mut v_inst_2465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2466_ = l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11_spec__15(v___x_2457_, v_len_2458_, v_aig_2459_, v_idx_2460_, v_hidx_2461_, v_s_2462_, v_input_2463_, v_inst_2464_, v_inst_2465_);
    leanh::lean_dec_ref(v_input_2463_);
    leanh::lean_dec(v_len_2458_);
    return v_res_2466_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8_spec__13(
    mut v_00_u03b2_2467_: *mut leanh::LeanObject,
    mut v_a_2468_: *mut leanh::LeanObject,
    mut v_x_2469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2470_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8_spec__13___redArg(v_a_2468_, v_x_2469_);
    return v___x_2470_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__16(
    mut v_00_u03b2_2471_: *mut leanh::LeanObject,
    mut v_a_2472_: *mut leanh::LeanObject,
    mut v_x_2473_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2474_: u8 = 0;
    v___x_2474_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__16___redArg(v_a_2472_, v_x_2473_);
    return v___x_2474_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__16___boxed(
    mut v_00_u03b2_2475_: *mut leanh::LeanObject,
    mut v_a_2476_: *mut leanh::LeanObject,
    mut v_x_2477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2478_: u8 = 0;
    let mut v_r_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2478_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__16(v_00_u03b2_2475_, v_a_2476_, v_x_2477_);
    v_r_2479_ = leanh::lean_box((v_res_2478_) as usize);
    return v_r_2479_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17(
    mut v_00_u03b2_2480_: *mut leanh::LeanObject,
    mut v_data_2481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2482_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17___redArg(v_data_2481_);
    return v___x_2482_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__18(
    mut v_00_u03b2_2483_: *mut leanh::LeanObject,
    mut v_a_2484_: *mut leanh::LeanObject,
    mut v_b_2485_: *mut leanh::LeanObject,
    mut v_x_2486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2487_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__18___redArg(v_a_2484_, v_b_2485_, v_x_2486_);
    return v___x_2487_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17_spec__21(
    mut v_00_u03b2_2488_: *mut leanh::LeanObject,
    mut v_i_2489_: *mut leanh::LeanObject,
    mut v_source_2490_: *mut leanh::LeanObject,
    mut v_target_2491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2492_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17_spec__21___redArg(v_i_2489_, v_source_2490_, v_target_2491_);
    return v___x_2492_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17_spec__21_spec__24(
    mut v_00_u03b2_2493_: *mut leanh::LeanObject,
    mut v_x_2494_: *mut leanh::LeanObject,
    mut v_x_2495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2496_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17_spec__21_spec__24___redArg(v_x_2494_, v_x_2495_);
    return v___x_2496_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(
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
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin);
}