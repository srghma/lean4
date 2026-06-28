// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Pred
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.GetLsbD Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr Init.Omega
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::{
    lean_nat_land, lean_nat_lor, lean_nat_shiftr,
};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_uint64_mix_hash,
};
pub static l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 8) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,0 as *mut crate::leanh::LeanObject] };
static mut l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 8) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,1 as *mut crate::leanh::LeanObject] };
static mut l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5___lam__0 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__2___redArg(
    mut v_target_1249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: u8 = 0;
    v_w_1250_ = crate::leanh::lean_ctor_get(v_target_1249_, 0);
    v_vec_1251_ = crate::leanh::lean_ctor_get(v_target_1249_, 1);
    v_idx_1252_ = crate::leanh::lean_ctor_get(v_target_1249_, 2);
    v___x_1253_ = lean_nat_dec_lt(v_idx_1252_, v_w_1250_);
    if v___x_1253_ == 0 {
        let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1254_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1255_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_1255_, 0, v___x_1254_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_1255_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_1253_,
        );
        return v___x_1255_;
    } else {
        let mut v_ref_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1261_: u8 = 0;
        v_ref_1256_ = lean_array_fget_borrowed(v_vec_1251_, v_idx_1252_);
        v___x_1257_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1258_ = lean_nat_shiftr(v_ref_1256_, v___x_1257_);
        v___x_1259_ = lean_nat_land(v___x_1257_, v_ref_1256_);
        v___x_1260_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1261_ = lean_nat_dec_eq(v___x_1259_, v___x_1260_);
        crate::leanh::lean_dec(v___x_1259_);
        if v___x_1261_ == 0 {
            let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1262_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
            crate::leanh::lean_ctor_set(v___x_1262_, 0, v___x_1258_);
            crate::leanh::lean_ctor_set_uint8(
                v___x_1262_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                v___x_1253_,
            );
            return v___x_1262_;
        } else {
            let mut v___x_1263_: u8 = 0;
            let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1263_ = 0;
            v___x_1264_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
            crate::leanh::lean_ctor_set(v___x_1264_, 0, v___x_1258_);
            crate::leanh::lean_ctor_set_uint8(
                v___x_1264_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                v___x_1263_,
            );
            return v___x_1264_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__2___redArg___boxed(
    mut v_target_1265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1266_ = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__2___redArg(v_target_1265_);
    crate::leanh::lean_dec_ref(v_target_1265_);
    return v_res_1266_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__2(
    mut v_aig_1267_: *mut crate::leanh::LeanObject,
    mut v_target_1268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__2___redArg(v_target_1268_);
    return v___x_1269_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__2___boxed(
    mut v_aig_1270_: *mut crate::leanh::LeanObject,
    mut v_target_1271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1272_ = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__2(v_aig_1270_, v_target_1271_);
    crate::leanh::lean_dec_ref(v_target_1271_);
    crate::leanh::lean_dec_ref(v_aig_1270_);
    return v_res_1272_;
}
pub unsafe fn l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8_spec__12(
    mut v_x_1273_: *mut crate::leanh::LeanObject,
) -> u64 {
    match crate::leanh::lean_obj_tag(v_x_1273_) {
        0 => {
            let mut v___x_1274_: u64 = 0;
            v___x_1274_ = 0u64;
            return v___x_1274_;
        }
        1 => {
            let mut v_idx_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1276_: u64 = 0;
            let mut v___x_1277_: u64 = 0;
            let mut v___x_1278_: u64 = 0;
            v_idx_1275_ = crate::leanh::lean_ctor_get(v_x_1273_, 0);
            v___x_1276_ = 1u64;
            v___x_1277_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_idx_1275_);
            v___x_1278_ = lean_uint64_mix_hash(v___x_1276_, v___x_1277_);
            return v___x_1278_;
        }
        _ => {
            let mut v_l_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1281_: u64 = 0;
            let mut v___x_1282_: u64 = 0;
            let mut v___x_1283_: u64 = 0;
            let mut v___x_1284_: u64 = 0;
            let mut v___x_1285_: u64 = 0;
            v_l_1279_ = crate::leanh::lean_ctor_get(v_x_1273_, 0);
            v_r_1280_ = crate::leanh::lean_ctor_get(v_x_1273_, 1);
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
    mut v_x_1286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1287_: u64 = 0;
    let mut v_r_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1287_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8_spec__12(v_x_1286_);
    crate::leanh::lean_dec(v_x_1286_);
    v_r_1288_ = crate::leanh::lean_box_uint64(v_res_1287_);
    return v_r_1288_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8_spec__13___redArg(
    mut v_a_1289_: *mut crate::leanh::LeanObject,
    mut v_x_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: u8 = 0;
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1290_) == 0 {
                    crate::leanh::lean_dec(v_a_1289_);
                    v___x_1291_ = crate::leanh::lean_box(0);
                    return v___x_1291_;
                } else {
                    v_key_1292_ = crate::leanh::lean_ctor_get(v_x_1290_, 0);
                    crate::leanh::lean_inc(v_key_1292_);
                    v_value_1293_ = crate::leanh::lean_ctor_get(v_x_1290_, 1);
                    crate::leanh::lean_inc(v_value_1293_);
                    v_tail_1294_ = crate::leanh::lean_ctor_get(v_x_1290_, 2);
                    crate::leanh::lean_inc(v_tail_1294_);
                    crate::leanh::lean_dec_ref_known(v_x_1290_, 3);
                    v___x_1295_ = crate::leanh::lean_alloc_closure(
                        l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed
                            as *mut core::ffi::c_void,
                        2,
                        0,
                    );
                    crate::leanh::lean_inc(v_a_1289_);
                    v___x_1296_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(
                        v___x_1295_,
                        v_key_1292_,
                        v_a_1289_,
                    );
                    if v___x_1296_ == 0 {
                        crate::leanh::lean_dec(v_value_1293_);
                        v_x_1290_ = v_tail_1294_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1294_);
                        crate::leanh::lean_dec(v_a_1289_);
                        v___x_1298_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1298_, 0, v_value_1293_);
                        return v___x_1298_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8___redArg(
    mut v_m_1299_: *mut crate::leanh::LeanObject,
    mut v_a_1300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1301_ = crate::leanh::lean_ctor_get(v_m_1299_, 1);
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
    crate::leanh::lean_inc(v___x_1315_);
    v___x_1316_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8_spec__13___redArg(v_a_1300_, v___x_1315_);
    return v___x_1316_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8___redArg___boxed(
    mut v_m_1317_: *mut crate::leanh::LeanObject,
    mut v_a_1318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1319_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8___redArg(v_m_1317_, v_a_1318_);
    crate::leanh::lean_dec_ref(v_m_1317_);
    return v_res_1319_;
}
pub unsafe fn l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__9(
    mut v_aig_1320_: *mut crate::leanh::LeanObject,
    mut v_ref_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gate_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1323_: u8 = 0;
    let mut v_decls_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_gate_1322_ = crate::leanh::lean_ctor_get(v_ref_1321_, 0);
    v_invert_1323_ = crate::leanh::lean_ctor_get_uint8(
        v_ref_1321_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v_decls_1324_ = crate::leanh::lean_ctor_get(v_aig_1320_, 0);
    v_decl_1325_ = lean_array_fget_borrowed(v_decls_1324_, v_gate_1322_);
    if crate::leanh::lean_obj_tag(v_decl_1325_) == 0 {
        let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1326_ = crate::leanh::lean_box((v_invert_1323_) as usize);
        v___x_1327_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1327_, 0, v___x_1326_);
        return v___x_1327_;
    } else {
        let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1328_ = crate::leanh::lean_box(0);
        return v___x_1328_;
    }
}
pub unsafe fn l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__9___boxed(
    mut v_aig_1329_: *mut crate::leanh::LeanObject,
    mut v_ref_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1331_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__9(v_aig_1329_, v_ref_1330_);
    crate::leanh::lean_dec_ref(v_ref_1330_);
    crate::leanh::lean_dec_ref(v_aig_1329_);
    return v_res_1331_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__18___redArg(
    mut v_a_1332_: *mut crate::leanh::LeanObject,
    mut v_b_1333_: *mut crate::leanh::LeanObject,
    mut v_x_1334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1340_: u8 = 0;
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: u8 = 0;
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1334_) == 0 {
                    crate::leanh::lean_dec(v_b_1333_);
                    crate::leanh::lean_dec(v_a_1332_);
                    return v_x_1334_;
                } else {
                    v_key_1335_ = crate::leanh::lean_ctor_get(v_x_1334_, 0);
                    v_value_1336_ = crate::leanh::lean_ctor_get(v_x_1334_, 1);
                    v_tail_1337_ = crate::leanh::lean_ctor_get(v_x_1334_, 2);
                    v_isSharedCheck_1350_ = (!crate::leanh::lean_is_exclusive(v_x_1334_)) as u8;
                    if v_isSharedCheck_1350_ == 0 {
                        v___x_1339_ = v_x_1334_;
                        v_isShared_1340_ = v_isSharedCheck_1350_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1337_);
                        crate::leanh::lean_inc(v_value_1336_);
                        crate::leanh::lean_inc(v_key_1335_);
                        crate::leanh::lean_dec(v_x_1334_);
                        v___x_1339_ = crate::leanh::lean_box(0);
                        v_isShared_1340_ = v_isSharedCheck_1350_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1341_ = crate::leanh::lean_alloc_closure(
                    l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed as *mut core::ffi::c_void,
                    2,
                    0,
                );
                crate::leanh::lean_inc(v_a_1332_);
                crate::leanh::lean_inc(v_key_1335_);
                v___x_1342_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(
                    v___x_1341_,
                    v_key_1335_,
                    v_a_1332_,
                );
                if v___x_1342_ == 0 {
                    v___x_1343_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__18___redArg(v_a_1332_, v_b_1333_, v_tail_1337_);
                    if v_isShared_1340_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1339_, 2, v___x_1343_);
                        v___x_1345_ = v___x_1339_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1346_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_key_1335_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_value_1336_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 2, v___x_1343_);
                        v___x_1345_ = v_reuseFailAlloc_1346_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_1336_);
                    crate::leanh::lean_dec(v_key_1335_);
                    if v_isShared_1340_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1339_, 1, v_b_1333_);
                        crate::leanh::lean_ctor_set(v___x_1339_, 0, v_a_1332_);
                        v___x_1348_ = v___x_1339_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1349_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1332_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_b_1333_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_tail_1337_);
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
    mut v_a_1351_: *mut crate::leanh::LeanObject,
    mut v_x_1352_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1353_: u8 = 0;
    let mut v_key_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1352_) == 0 {
                    crate::leanh::lean_dec(v_a_1351_);
                    v___x_1353_ = 0;
                    return v___x_1353_;
                } else {
                    v_key_1354_ = crate::leanh::lean_ctor_get(v_x_1352_, 0);
                    crate::leanh::lean_inc(v_key_1354_);
                    v_tail_1355_ = crate::leanh::lean_ctor_get(v_x_1352_, 2);
                    crate::leanh::lean_inc(v_tail_1355_);
                    crate::leanh::lean_dec_ref_known(v_x_1352_, 3);
                    v___x_1356_ = crate::leanh::lean_alloc_closure(
                        l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed
                            as *mut core::ffi::c_void,
                        2,
                        0,
                    );
                    crate::leanh::lean_inc(v_a_1351_);
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
                        crate::leanh::lean_dec(v_tail_1355_);
                        crate::leanh::lean_dec(v_a_1351_);
                        return v___x_1357_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__16___redArg___boxed(
    mut v_a_1359_: *mut crate::leanh::LeanObject,
    mut v_x_1360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1361_: u8 = 0;
    let mut v_r_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1361_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__16___redArg(v_a_1359_, v_x_1360_);
    v_r_1362_ = crate::leanh::lean_box((v_res_1361_) as usize);
    return v_r_1362_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17_spec__21_spec__24___redArg(
    mut v_x_1363_: *mut crate::leanh::LeanObject,
    mut v_x_1364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1370_: u8 = 0;
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1390_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1364_) == 0 {
                    return v_x_1363_;
                } else {
                    v_key_1365_ = crate::leanh::lean_ctor_get(v_x_1364_, 0);
                    v_value_1366_ = crate::leanh::lean_ctor_get(v_x_1364_, 1);
                    v_tail_1367_ = crate::leanh::lean_ctor_get(v_x_1364_, 2);
                    v_isSharedCheck_1390_ = (!crate::leanh::lean_is_exclusive(v_x_1364_)) as u8;
                    if v_isSharedCheck_1390_ == 0 {
                        v___x_1369_ = v_x_1364_;
                        v_isShared_1370_ = v_isSharedCheck_1390_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1367_);
                        crate::leanh::lean_inc(v_value_1366_);
                        crate::leanh::lean_inc(v_key_1365_);
                        crate::leanh::lean_dec(v_x_1364_);
                        v___x_1369_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_inc(v___x_1384_);
                if v_isShared_1370_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1369_, 2, v___x_1384_);
                    v___x_1386_ = v___x_1369_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1389_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_key_1365_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_value_1366_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 2, v___x_1384_);
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
    mut v_i_1391_: *mut crate::leanh::LeanObject,
    mut v_source_1392_: *mut crate::leanh::LeanObject,
    mut v_target_1393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: u8 = 0;
    let mut v_es_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1394_ = lean_array_get_size(v_source_1392_);
                v___x_1395_ = lean_nat_dec_lt(v_i_1391_, v___x_1394_);
                if v___x_1395_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1392_);
                    crate::leanh::lean_dec(v_i_1391_);
                    return v_target_1393_;
                } else {
                    v_es_1396_ = lean_array_fget(v_source_1392_, v_i_1391_);
                    v___x_1397_ = crate::leanh::lean_box(0);
                    v_source_1398_ = lean_array_fset(v_source_1392_, v_i_1391_, v___x_1397_);
                    v_target_1399_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17_spec__21_spec__24___redArg(v_target_1393_, v_es_1396_);
                    v___x_1400_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1401_ = lean_nat_add(v_i_1391_, v___x_1400_);
                    crate::leanh::lean_dec(v_i_1391_);
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
    mut v_data_1403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = lean_array_get_size(v_data_1403_);
    v___x_1405_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1406_ = lean_nat_mul(v___x_1404_, v___x_1405_);
    v___x_1407_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1408_ = crate::leanh::lean_box(0);
    v___x_1409_ = lean_mk_array(v_nbuckets_1406_, v___x_1408_);
    v___x_1410_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17_spec__21___redArg(v___x_1407_, v_data_1403_, v___x_1409_);
    return v___x_1410_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10___redArg(
    mut v_m_1411_: *mut crate::leanh::LeanObject,
    mut v_a_1412_: *mut crate::leanh::LeanObject,
    mut v_b_1413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1418_: u8 = 0;
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: u8 = 0;
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: u8 = 0;
    let mut v_val_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1458_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1414_ = crate::leanh::lean_ctor_get(v_m_1411_, 0);
                v_buckets_1415_ = crate::leanh::lean_ctor_get(v_m_1411_, 1);
                v_isSharedCheck_1458_ = (!crate::leanh::lean_is_exclusive(v_m_1411_)) as u8;
                if v_isSharedCheck_1458_ == 0 {
                    v___x_1417_ = v_m_1411_;
                    v_isShared_1418_ = v_isSharedCheck_1458_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1415_);
                    crate::leanh::lean_inc(v_size_1414_);
                    crate::leanh::lean_dec(v_m_1411_);
                    v___x_1417_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_inc(v_bkt_1432_);
                crate::leanh::lean_inc(v_a_1412_);
                v___x_1433_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__16___redArg(v_a_1412_, v_bkt_1432_);
                if v___x_1433_ == 0 {
                    v___x_1434_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1435_ = lean_nat_add(v_size_1414_, v___x_1434_);
                    crate::leanh::lean_dec(v_size_1414_);
                    crate::leanh::lean_inc(v_bkt_1432_);
                    v___x_1436_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1436_, 0, v_a_1412_);
                    crate::leanh::lean_ctor_set(v___x_1436_, 1, v_b_1413_);
                    crate::leanh::lean_ctor_set(v___x_1436_, 2, v_bkt_1432_);
                    v_buckets_x27_1437_ =
                        lean_array_uset(v_buckets_1415_, v___x_1431_, v___x_1436_);
                    v___x_1438_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1439_ = lean_nat_mul(v_size_x27_1435_, v___x_1438_);
                    v___x_1440_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1441_ = lean_nat_div(v___x_1439_, v___x_1440_);
                    crate::leanh::lean_dec(v___x_1439_);
                    v___x_1442_ = lean_array_get_size(v_buckets_x27_1437_);
                    v___x_1443_ = lean_nat_dec_le(v___x_1441_, v___x_1442_);
                    crate::leanh::lean_dec(v___x_1441_);
                    if v___x_1443_ == 0 {
                        v_val_1444_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17___redArg(v_buckets_x27_1437_);
                        if v_isShared_1418_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1417_, 1, v_val_1444_);
                            crate::leanh::lean_ctor_set(v___x_1417_, 0, v_size_x27_1435_);
                            v___x_1446_ = v___x_1417_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1447_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1447_,
                                0,
                                v_size_x27_1435_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_val_1444_);
                            v___x_1446_ = v_reuseFailAlloc_1447_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1418_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1417_, 1, v_buckets_x27_1437_);
                            crate::leanh::lean_ctor_set(v___x_1417_, 0, v_size_x27_1435_);
                            v___x_1449_ = v___x_1417_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1450_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1450_,
                                0,
                                v_size_x27_1435_,
                            );
                            crate::leanh::lean_ctor_set(
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
                    crate::leanh::lean_inc(v_bkt_1432_);
                    v___x_1451_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1452_ =
                        lean_array_uset(v_buckets_1415_, v___x_1431_, v___x_1451_);
                    v___x_1453_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__18___redArg(v_a_1412_, v_b_1413_, v_bkt_1432_);
                    v___x_1454_ = lean_array_uset(v_buckets_x27_1452_, v___x_1431_, v___x_1453_);
                    if v_isShared_1418_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1417_, 1, v___x_1454_);
                        v___x_1456_ = v___x_1417_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1457_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_size_1414_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1457_, 1, v___x_1454_);
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
    mut v_aig_1462_: *mut crate::leanh::LeanObject,
    mut v_input_1463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1468_: u8 = 0;
    let mut v_decls_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1473_: u8 = 0;
    let mut v_gate_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1475_: u8 = 0;
    let mut v_gate_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1477_: u8 = 0;
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1491_: u8 = 0;
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1496_: u8 = 0;
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsVal_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhsVal_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1509_: u8 = 0;
    let mut v_val_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: u8 = 0;
    let mut v_val_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: u8 = 0;
    let mut v_val_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: u8 = 0;
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: u8 = 0;
    let mut v_g_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1529_: u8 = 0;
    let mut v_unused_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1534_: u8 = 0;
    let mut v_val_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: u8 = 0;
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1544_: u8 = 0;
    let mut v_unused_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1547_: u8 = 0;
    let mut v_isSharedCheck_1548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_1464_ = crate::leanh::lean_ctor_get(v_input_1463_, 0);
                v_rhs_1465_ = crate::leanh::lean_ctor_get(v_input_1463_, 1);
                v_isSharedCheck_1548_ = (!crate::leanh::lean_is_exclusive(v_input_1463_)) as u8;
                if v_isSharedCheck_1548_ == 0 {
                    v___x_1467_ = v_input_1463_;
                    v_isShared_1468_ = v_isSharedCheck_1548_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_1465_);
                    crate::leanh::lean_inc(v_lhs_1464_);
                    crate::leanh::lean_dec(v_input_1463_);
                    v___x_1467_ = crate::leanh::lean_box(0);
                    v_isShared_1468_ = v_isSharedCheck_1548_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_decls_1469_ = crate::leanh::lean_ctor_get(v_aig_1462_, 0);
                v_cache_1470_ = crate::leanh::lean_ctor_get(v_aig_1462_, 1);
                v_isSharedCheck_1547_ = (!crate::leanh::lean_is_exclusive(v_aig_1462_)) as u8;
                if v_isSharedCheck_1547_ == 0 {
                    v___x_1472_ = v_aig_1462_;
                    v_isShared_1473_ = v_isSharedCheck_1547_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cache_1470_);
                    crate::leanh::lean_inc(v_decls_1469_);
                    crate::leanh::lean_dec(v_aig_1462_);
                    v___x_1472_ = crate::leanh::lean_box(0);
                    v_isShared_1473_ = v_isSharedCheck_1547_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_1474_ = crate::leanh::lean_ctor_get(v_lhs_1464_, 0);
                crate::leanh::lean_inc(v_gate_1474_);
                v_invert_1475_ = crate::leanh::lean_ctor_get_uint8(
                    v_lhs_1464_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_gate_1476_ = crate::leanh::lean_ctor_get(v_rhs_1465_, 0);
                v_invert_1477_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_1465_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_1478_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1479_ = lean_nat_mul(v_gate_1474_, v___x_1478_);
                v___x_1480_ = l_Bool_toNat(v_invert_1475_);
                v___x_1481_ = lean_nat_lor(v___x_1479_, v___x_1480_);
                crate::leanh::lean_dec(v___x_1480_);
                crate::leanh::lean_dec(v___x_1479_);
                v___x_1482_ = lean_nat_mul(v_gate_1476_, v___x_1478_);
                v___x_1483_ = l_Bool_toNat(v_invert_1477_);
                v___x_1484_ = lean_nat_lor(v___x_1482_, v___x_1483_);
                crate::leanh::lean_dec(v___x_1483_);
                crate::leanh::lean_dec(v___x_1482_);
                if v_isShared_1468_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1467_, 2);
                    crate::leanh::lean_ctor_set(v___x_1467_, 1, v___x_1484_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1481_);
                    v_decl_1486_ = v___x_1467_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1546_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___x_1484_);
                    v_decl_1486_ = v_reuseFailAlloc_1546_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v_decl_1486_);
                v___x_1487_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8___redArg(v_cache_1470_, v_decl_1486_);
                if crate::leanh::lean_obj_tag(v___x_1487_) == 0 {
                    crate::leanh::lean_inc(v_gate_1476_);
                    crate::leanh::lean_inc_ref(v_cache_1470_);
                    crate::leanh::lean_inc_ref(v_decls_1469_);
                    if v_isShared_1473_ == 0 {
                        v___x_1489_ = v___x_1472_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1531_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_decls_1469_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_cache_1470_);
                        v___x_1489_ = v_reuseFailAlloc_1531_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_decl_1486_);
                    crate::leanh::lean_dec(v_gate_1474_);
                    crate::leanh::lean_dec_ref(v_lhs_1464_);
                    v_isSharedCheck_1544_ = (!crate::leanh::lean_is_exclusive(v_rhs_1465_)) as u8;
                    if v_isSharedCheck_1544_ == 0 {
                        v_unused_1545_ = crate::leanh::lean_ctor_get(v_rhs_1465_, 0);
                        crate::leanh::lean_dec(v_unused_1545_);
                        v___x_1533_ = v_rhs_1465_;
                        v_isShared_1534_ = v_isSharedCheck_1544_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_rhs_1465_);
                        v___x_1533_ = crate::leanh::lean_box(0);
                        v_isShared_1534_ = v_isSharedCheck_1544_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                v_lhsVal_1505_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__9(v___x_1489_, v_lhs_1464_);
                crate::leanh::lean_dec_ref(v_lhs_1464_);
                v_rhsVal_1506_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__9(v___x_1489_, v_rhs_1465_);
                v_isSharedCheck_1529_ = (!crate::leanh::lean_is_exclusive(v_rhs_1465_)) as u8;
                if v_isSharedCheck_1529_ == 0 {
                    v_unused_1530_ = crate::leanh::lean_ctor_get(v_rhs_1465_, 0);
                    crate::leanh::lean_dec(v_unused_1530_);
                    v___x_1508_ = v_rhs_1465_;
                    v_isShared_1509_ = v_isSharedCheck_1529_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_rhs_1465_);
                    v___x_1508_ = crate::leanh::lean_box(0);
                    v_isShared_1509_ = v_isSharedCheck_1529_;
                    state = 9;
                    continue;
                }
            }
            5 => {
                v___x_1492_ = crate::leanh::lean_unsigned_to_nat(0);
                v_ref_1493_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v_ref_1493_, 0, v___x_1492_);
                crate::leanh::lean_ctor_set_uint8(
                    v_ref_1493_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___y_1491_,
                );
                v___x_1494_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1494_, 0, v___x_1489_);
                crate::leanh::lean_ctor_set(v___x_1494_, 1, v_ref_1493_);
                return v___x_1494_;
            }
            6 => {
                if v___y_1496_ == 0 {
                    crate::leanh::lean_dec(v_gate_1474_);
                    v___y_1491_ = v___y_1496_;
                    state = 5;
                    continue;
                } else {
                    v___x_1497_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1497_, 0, v_gate_1474_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1497_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_1475_,
                    );
                    v___x_1498_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1498_, 0, v___x_1489_);
                    crate::leanh::lean_ctor_set(v___x_1498_, 1, v___x_1497_);
                    return v___x_1498_;
                }
            }
            7 => {
                v___x_1500_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1500_, 0, v_gate_1476_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1500_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_1477_,
                );
                v___x_1501_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1501_, 0, v___x_1489_);
                crate::leanh::lean_ctor_set(v___x_1501_, 1, v___x_1500_);
                return v___x_1501_;
            }
            8 => {
                v_ref_1503_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6___closed__0;
                v___x_1504_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1504_, 0, v___x_1489_);
                crate::leanh::lean_ctor_set(v___x_1504_, 1, v_ref_1503_);
                return v___x_1504_;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_lhsVal_1505_) == 1 {
                    crate::leanh::lean_del_object(v___x_1508_);
                    crate::leanh::lean_dec_ref(v_decl_1486_);
                    crate::leanh::lean_dec(v_gate_1474_);
                    crate::leanh::lean_dec_ref(v_cache_1470_);
                    crate::leanh::lean_dec_ref(v_decls_1469_);
                    v_val_1510_ = crate::leanh::lean_ctor_get(v_lhsVal_1505_, 0);
                    crate::leanh::lean_inc(v_val_1510_);
                    crate::leanh::lean_dec_ref_known(v_lhsVal_1505_, 1);
                    v___x_1511_ = (crate::leanh::lean_unbox(v_val_1510_) as u8);
                    crate::leanh::lean_dec(v_val_1510_);
                    if v___x_1511_ == 0 {
                        crate::leanh::lean_dec(v_rhsVal_1506_);
                        crate::leanh::lean_dec(v_gate_1476_);
                        state = 8;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v_rhsVal_1506_) == 1 {
                            v_val_1512_ = crate::leanh::lean_ctor_get(v_rhsVal_1506_, 0);
                            crate::leanh::lean_inc(v_val_1512_);
                            crate::leanh::lean_dec_ref_known(v_rhsVal_1506_, 1);
                            v___x_1513_ = (crate::leanh::lean_unbox(v_val_1512_) as u8);
                            crate::leanh::lean_dec(v_val_1512_);
                            if v___x_1513_ == 0 {
                                crate::leanh::lean_dec(v_gate_1476_);
                                state = 8;
                                continue;
                            } else {
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_rhsVal_1506_);
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_lhsVal_1505_);
                    if crate::leanh::lean_obj_tag(v_rhsVal_1506_) == 1 {
                        crate::leanh::lean_dec_ref(v_decl_1486_);
                        crate::leanh::lean_dec(v_gate_1476_);
                        crate::leanh::lean_dec_ref(v_cache_1470_);
                        crate::leanh::lean_dec_ref(v_decls_1469_);
                        v_val_1514_ = crate::leanh::lean_ctor_get(v_rhsVal_1506_, 0);
                        crate::leanh::lean_inc(v_val_1514_);
                        crate::leanh::lean_dec_ref_known(v_rhsVal_1506_, 1);
                        v___x_1515_ = (crate::leanh::lean_unbox(v_val_1514_) as u8);
                        crate::leanh::lean_dec(v_val_1514_);
                        if v___x_1515_ == 0 {
                            crate::leanh::lean_del_object(v___x_1508_);
                            crate::leanh::lean_dec(v_gate_1474_);
                            state = 8;
                            continue;
                        } else {
                            if v_isShared_1509_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1508_, 0, v_gate_1474_);
                                v___x_1517_ = v___x_1508_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_1519_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                crate::leanh::lean_ctor_set(
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
                        crate::leanh::lean_dec(v_rhsVal_1506_);
                        v___x_1520_ = lean_nat_dec_eq(v_gate_1474_, v_gate_1476_);
                        crate::leanh::lean_dec(v_gate_1476_);
                        if v___x_1520_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1489_);
                            crate::leanh::lean_dec(v_gate_1474_);
                            v_g_1521_ = lean_array_get_size(v_decls_1469_);
                            crate::leanh::lean_inc_ref(v_decl_1486_);
                            v_cache_1522_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10___redArg(v_cache_1470_, v_decl_1486_, v_g_1521_);
                            v_decls_1523_ = lean_array_push(v_decls_1469_, v_decl_1486_);
                            v___x_1524_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1524_, 0, v_decls_1523_);
                            crate::leanh::lean_ctor_set(v___x_1524_, 1, v_cache_1522_);
                            if v_isShared_1509_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1508_, 0, v_g_1521_);
                                v___x_1526_ = v___x_1508_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_1528_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_g_1521_);
                                v___x_1526_ = v_reuseFailAlloc_1528_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1508_);
                            crate::leanh::lean_dec_ref(v_decl_1486_);
                            crate::leanh::lean_dec_ref(v_cache_1470_);
                            crate::leanh::lean_dec_ref(v_decls_1469_);
                            if v_invert_1475_ == 0 {
                                if v_invert_1477_ == 0 {
                                    v___y_1496_ = v___x_1520_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_gate_1474_);
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
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1517_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_1475_,
                );
                v___x_1518_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1518_, 0, v___x_1489_);
                crate::leanh::lean_ctor_set(v___x_1518_, 1, v___x_1517_);
                return v___x_1518_;
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1526_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1520_,
                );
                v___x_1527_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1527_, 0, v___x_1524_);
                crate::leanh::lean_ctor_set(v___x_1527_, 1, v___x_1526_);
                return v___x_1527_;
            }
            12 => {
                v_val_1535_ = crate::leanh::lean_ctor_get(v___x_1487_, 0);
                crate::leanh::lean_inc(v_val_1535_);
                crate::leanh::lean_dec_ref_known(v___x_1487_, 1);
                if v_isShared_1473_ == 0 {
                    v___x_1537_ = v___x_1472_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1543_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_decls_1469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_cache_1470_);
                    v___x_1537_ = v_reuseFailAlloc_1543_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_1538_ = 0;
                if v_isShared_1534_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1533_, 0, v_val_1535_);
                    v___x_1540_ = v___x_1533_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1542_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_val_1535_);
                    v___x_1540_ = v_reuseFailAlloc_1542_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1540_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1538_,
                );
                v___x_1541_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1541_, 0, v___x_1537_);
                crate::leanh::lean_ctor_set(v___x_1541_, 1, v___x_1540_);
                return v___x_1541_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(
    mut v_aig_1549_: *mut crate::leanh::LeanObject,
    mut v_input_1550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1555_: u8 = 0;
    let mut v_gate_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: u8 = 0;
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1567_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_1551_ = crate::leanh::lean_ctor_get(v_input_1550_, 0);
                v_rhs_1552_ = crate::leanh::lean_ctor_get(v_input_1550_, 1);
                v_isSharedCheck_1567_ = (!crate::leanh::lean_is_exclusive(v_input_1550_)) as u8;
                if v_isSharedCheck_1567_ == 0 {
                    v___x_1554_ = v_input_1550_;
                    v_isShared_1555_ = v_isSharedCheck_1567_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_1552_);
                    crate::leanh::lean_inc(v_lhs_1551_);
                    crate::leanh::lean_dec(v_input_1550_);
                    v___x_1554_ = crate::leanh::lean_box(0);
                    v_isShared_1555_ = v_isSharedCheck_1567_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_1556_ = crate::leanh::lean_ctor_get(v_lhs_1551_, 0);
                v_gate_1557_ = crate::leanh::lean_ctor_get(v_rhs_1552_, 0);
                v___x_1558_ = lean_nat_dec_lt(v_gate_1556_, v_gate_1557_);
                if v___x_1558_ == 0 {
                    if v_isShared_1555_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1554_, 1, v_lhs_1551_);
                        crate::leanh::lean_ctor_set(v___x_1554_, 0, v_rhs_1552_);
                        v___x_1560_ = v___x_1554_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1562_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_rhs_1552_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_lhs_1551_);
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
                        v_reuseFailAlloc_1566_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_lhs_1551_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_rhs_1552_);
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
    mut v_aig_1568_: *mut crate::leanh::LeanObject,
    mut v_acc_1569_: *mut crate::leanh::LeanObject,
    mut v_idx_1570_: *mut crate::leanh::LeanObject,
    mut v_len_1571_: *mut crate::leanh::LeanObject,
    mut v_input_1572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: u8 = 0;
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: u8 = 0;
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: u8 = 0;
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1582_ = lean_nat_dec_lt(v_idx_1570_, v_len_1571_);
                if v___x_1582_ == 0 {
                    crate::leanh::lean_dec(v_idx_1570_);
                    v___x_1583_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1583_, 0, v_aig_1568_);
                    crate::leanh::lean_ctor_set(v___x_1583_, 1, v_acc_1569_);
                    return v___x_1583_;
                } else {
                    v_ref_1584_ = lean_array_fget_borrowed(v_input_1572_, v_idx_1570_);
                    v___x_1585_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1586_ = lean_nat_shiftr(v_ref_1584_, v___x_1585_);
                    v___x_1587_ = lean_nat_land(v___x_1585_, v_ref_1584_);
                    v___x_1588_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1589_ = lean_nat_dec_eq(v___x_1587_, v___x_1588_);
                    crate::leanh::lean_dec(v___x_1587_);
                    if v___x_1589_ == 0 {
                        v___x_1590_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1590_, 0, v___x_1586_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1590_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_1582_,
                        );
                        v___y_1574_ = v___x_1590_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1591_ = 0;
                        v___x_1592_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1592_, 0, v___x_1586_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1592_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_1591_,
                        );
                        v___y_1574_ = v___x_1592_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1575_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1575_, 0, v_acc_1569_);
                crate::leanh::lean_ctor_set(v___x_1575_, 1, v___y_1574_);
                v_res_1576_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(v_aig_1568_, v___x_1575_);
                v_aig_1577_ = crate::leanh::lean_ctor_get(v_res_1576_, 0);
                crate::leanh::lean_inc_ref(v_aig_1577_);
                v_ref_1578_ = crate::leanh::lean_ctor_get(v_res_1576_, 1);
                crate::leanh::lean_inc_ref(v_ref_1578_);
                crate::leanh::lean_dec_ref(v_res_1576_);
                v___x_1579_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1580_ = lean_nat_add(v_idx_1570_, v___x_1579_);
                crate::leanh::lean_dec(v_idx_1570_);
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
    mut v_aig_1593_: *mut crate::leanh::LeanObject,
    mut v_acc_1594_: *mut crate::leanh::LeanObject,
    mut v_idx_1595_: *mut crate::leanh::LeanObject,
    mut v_len_1596_: *mut crate::leanh::LeanObject,
    mut v_input_1597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3_spec__8___redArg(v_aig_1593_, v_acc_1594_, v_idx_1595_, v_len_1596_, v_input_1597_);
    crate::leanh::lean_dec_ref(v_input_1597_);
    crate::leanh::lean_dec(v_len_1596_);
    return v_res_1598_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg(
    mut v_len_1602_: *mut crate::leanh::LeanObject,
    mut v_aig_1603_: *mut crate::leanh::LeanObject,
    mut v_vec_1604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1605_ = crate::leanh::lean_unsigned_to_nat(0);
    v_acc_1606_ = l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg___closed__0;
    v___x_1607_ = l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3_spec__8___redArg(v_aig_1603_, v_acc_1606_, v___x_1605_, v_len_1602_, v_vec_1604_);
    return v___x_1607_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg___boxed(
    mut v_len_1608_: *mut crate::leanh::LeanObject,
    mut v_aig_1609_: *mut crate::leanh::LeanObject,
    mut v_vec_1610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1611_ = l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg(v_len_1608_, v_aig_1609_, v_vec_1610_);
    crate::leanh::lean_dec_ref(v_vec_1610_);
    crate::leanh::lean_dec(v_len_1608_);
    return v_res_1611_;
}
pub unsafe fn l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__0(
    mut v_aig_1612_: *mut crate::leanh::LeanObject,
    mut v_input_1613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1624_: u8 = 0;
    let mut v_gate_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1628_: u8 = 0;
    let mut v___x_1629_: u8 = 0;
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1633_: u8 = 0;
    let mut v_gate_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1637_: u8 = 0;
    let mut v___x_1638_: u8 = 0;
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1642_: u8 = 0;
    let mut v___y_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1647_: u8 = 0;
    let mut v___y_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1652_: u8 = 0;
    let mut v_aig_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1658_: u8 = 0;
    let mut v___x_1659_: u8 = 0;
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1663_: u8 = 0;
    let mut v_aig_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1669_: u8 = 0;
    let mut v___x_1670_: u8 = 0;
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1674_: u8 = 0;
    let mut v_lhs_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1679_: u8 = 0;
    let mut v_gate_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1681_: u8 = 0;
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1684_: u8 = 0;
    let mut v_gate_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1686_: u8 = 0;
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1689_: u8 = 0;
    let mut v___y_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: u8 = 0;
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: u8 = 0;
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: u8 = 0;
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: u8 = 0;
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1718_: u8 = 0;
    let mut v_isSharedCheck_1719_: u8 = 0;
    let mut v_isSharedCheck_1720_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_1675_ = crate::leanh::lean_ctor_get(v_input_1613_, 0);
                v_rhs_1676_ = crate::leanh::lean_ctor_get(v_input_1613_, 1);
                v_isSharedCheck_1720_ = (!crate::leanh::lean_is_exclusive(v_input_1613_)) as u8;
                if v_isSharedCheck_1720_ == 0 {
                    v___x_1678_ = v_input_1613_;
                    v_isShared_1679_ = v_isSharedCheck_1720_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_1676_);
                    crate::leanh::lean_inc(v_lhs_1675_);
                    crate::leanh::lean_dec(v_input_1613_);
                    v___x_1678_ = crate::leanh::lean_box(0);
                    v_isShared_1679_ = v_isSharedCheck_1720_;
                    state = 12;
                    continue;
                }
            }
            1 => {
                v___x_1618_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1618_, 0, v___y_1615_);
                crate::leanh::lean_ctor_set(v___x_1618_, 1, v___y_1617_);
                v___x_1619_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(v___y_1616_, v___x_1618_);
                return v___x_1619_;
            }
            2 => {
                v_invert_1624_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1621_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1624_ == 0 {
                    v_gate_1625_ = crate::leanh::lean_ctor_get(v___y_1621_, 0);
                    v_isSharedCheck_1633_ = (!crate::leanh::lean_is_exclusive(v___y_1621_)) as u8;
                    if v_isSharedCheck_1633_ == 0 {
                        v___x_1627_ = v___y_1621_;
                        v_isShared_1628_ = v_isSharedCheck_1633_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1625_);
                        crate::leanh::lean_dec(v___y_1621_);
                        v___x_1627_ = crate::leanh::lean_box(0);
                        v_isShared_1628_ = v_isSharedCheck_1633_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_gate_1634_ = crate::leanh::lean_ctor_get(v___y_1621_, 0);
                    v_isSharedCheck_1642_ = (!crate::leanh::lean_is_exclusive(v___y_1621_)) as u8;
                    if v_isSharedCheck_1642_ == 0 {
                        v___x_1636_ = v___y_1621_;
                        v_isShared_1637_ = v_isSharedCheck_1642_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1634_);
                        crate::leanh::lean_dec(v___y_1621_);
                        v___x_1636_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1632_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_gate_1625_);
                    v___x_1631_ = v_reuseFailAlloc_1632_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1631_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                    v_reuseFailAlloc_1641_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_gate_1634_);
                    v___x_1640_ = v_reuseFailAlloc_1641_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1640_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1638_,
                );
                v___y_1615_ = v___y_1623_;
                v___y_1616_ = v___y_1622_;
                v___y_1617_ = v___x_1640_;
                state = 1;
                continue;
            }
            7 => {
                v___x_1649_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1649_, 0, v___y_1644_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1649_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___y_1647_,
                );
                v___x_1650_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1650_, 0, v___y_1648_);
                crate::leanh::lean_ctor_set(v___x_1650_, 1, v___x_1649_);
                v_res_1651_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(v___y_1646_, v___x_1650_);
                v_invert_1652_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1645_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1652_ == 0 {
                    v_aig_1653_ = crate::leanh::lean_ctor_get(v_res_1651_, 0);
                    crate::leanh::lean_inc_ref(v_aig_1653_);
                    v_ref_1654_ = crate::leanh::lean_ctor_get(v_res_1651_, 1);
                    crate::leanh::lean_inc_ref(v_ref_1654_);
                    crate::leanh::lean_dec_ref(v_res_1651_);
                    v_gate_1655_ = crate::leanh::lean_ctor_get(v___y_1645_, 0);
                    v_isSharedCheck_1663_ = (!crate::leanh::lean_is_exclusive(v___y_1645_)) as u8;
                    if v_isSharedCheck_1663_ == 0 {
                        v___x_1657_ = v___y_1645_;
                        v_isShared_1658_ = v_isSharedCheck_1663_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1655_);
                        crate::leanh::lean_dec(v___y_1645_);
                        v___x_1657_ = crate::leanh::lean_box(0);
                        v_isShared_1658_ = v_isSharedCheck_1663_;
                        state = 8;
                        continue;
                    }
                } else {
                    v_aig_1664_ = crate::leanh::lean_ctor_get(v_res_1651_, 0);
                    crate::leanh::lean_inc_ref(v_aig_1664_);
                    v_ref_1665_ = crate::leanh::lean_ctor_get(v_res_1651_, 1);
                    crate::leanh::lean_inc_ref(v_ref_1665_);
                    crate::leanh::lean_dec_ref(v_res_1651_);
                    v_gate_1666_ = crate::leanh::lean_ctor_get(v___y_1645_, 0);
                    v_isSharedCheck_1674_ = (!crate::leanh::lean_is_exclusive(v___y_1645_)) as u8;
                    if v_isSharedCheck_1674_ == 0 {
                        v___x_1668_ = v___y_1645_;
                        v_isShared_1669_ = v_isSharedCheck_1674_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1666_);
                        crate::leanh::lean_dec(v___y_1645_);
                        v___x_1668_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1662_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_gate_1655_);
                    v___x_1661_ = v_reuseFailAlloc_1662_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1661_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                    v_reuseFailAlloc_1673_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_gate_1666_);
                    v___x_1672_ = v_reuseFailAlloc_1673_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1672_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1670_,
                );
                v___y_1621_ = v_ref_1665_;
                v___y_1622_ = v_aig_1664_;
                v___y_1623_ = v___x_1672_;
                state = 2;
                continue;
            }
            12 => {
                v_gate_1680_ = crate::leanh::lean_ctor_get(v_lhs_1675_, 0);
                v_invert_1681_ = crate::leanh::lean_ctor_get_uint8(
                    v_lhs_1675_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1719_ = (!crate::leanh::lean_is_exclusive(v_lhs_1675_)) as u8;
                if v_isSharedCheck_1719_ == 0 {
                    v___x_1683_ = v_lhs_1675_;
                    v_isShared_1684_ = v_isSharedCheck_1719_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_1680_);
                    crate::leanh::lean_dec(v_lhs_1675_);
                    v___x_1683_ = crate::leanh::lean_box(0);
                    v_isShared_1684_ = v_isSharedCheck_1719_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_gate_1685_ = crate::leanh::lean_ctor_get(v_rhs_1676_, 0);
                v_invert_1686_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_1676_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1718_ = (!crate::leanh::lean_is_exclusive(v_rhs_1676_)) as u8;
                if v_isSharedCheck_1718_ == 0 {
                    v___x_1688_ = v_rhs_1676_;
                    v_isShared_1689_ = v_isSharedCheck_1718_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_1685_);
                    crate::leanh::lean_dec(v_rhs_1676_);
                    v___x_1688_ = crate::leanh::lean_box(0);
                    v_isShared_1689_ = v_isSharedCheck_1718_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                crate::leanh::lean_inc(v_gate_1680_);
                if v_isShared_1684_ == 0 {
                    v___x_1706_ = v___x_1683_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1717_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_gate_1680_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1717_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                    v_aig_1693_ = crate::leanh::lean_ctor_get(v_res_1692_, 0);
                    crate::leanh::lean_inc_ref(v_aig_1693_);
                    v_ref_1694_ = crate::leanh::lean_ctor_get(v_res_1692_, 1);
                    crate::leanh::lean_inc_ref(v_ref_1694_);
                    crate::leanh::lean_dec_ref(v_res_1692_);
                    v___x_1695_ = 1;
                    if v_isShared_1689_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1688_, 0, v_gate_1680_);
                        v___x_1697_ = v___x_1688_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_1698_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_gate_1680_);
                        v___x_1697_ = v_reuseFailAlloc_1698_;
                        state = 16;
                        continue;
                    }
                } else {
                    v_aig_1699_ = crate::leanh::lean_ctor_get(v_res_1692_, 0);
                    crate::leanh::lean_inc_ref(v_aig_1699_);
                    v_ref_1700_ = crate::leanh::lean_ctor_get(v_res_1692_, 1);
                    crate::leanh::lean_inc_ref(v_ref_1700_);
                    crate::leanh::lean_dec_ref(v_res_1692_);
                    v___x_1701_ = 0;
                    if v_isShared_1689_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1688_, 0, v_gate_1680_);
                        v___x_1703_ = v___x_1688_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_1704_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_gate_1680_);
                        v___x_1703_ = v_reuseFailAlloc_1704_;
                        state = 17;
                        continue;
                    }
                }
            }
            16 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1697_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1703_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                    crate::leanh::lean_inc(v_gate_1685_);
                    v___x_1708_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1708_, 0, v_gate_1685_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1708_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1707_,
                    );
                    if v_isShared_1679_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1678_, 1, v___x_1708_);
                        crate::leanh::lean_ctor_set(v___x_1678_, 0, v___x_1706_);
                        v___x_1710_ = v___x_1678_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_1711_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1706_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1711_, 1, v___x_1708_);
                        v___x_1710_ = v_reuseFailAlloc_1711_;
                        state = 19;
                        continue;
                    }
                } else {
                    v___x_1712_ = 0;
                    crate::leanh::lean_inc(v_gate_1685_);
                    v___x_1713_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1713_, 0, v_gate_1685_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1713_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1712_,
                    );
                    if v_isShared_1679_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1678_, 1, v___x_1713_);
                        crate::leanh::lean_ctor_set(v___x_1678_, 0, v___x_1706_);
                        v___x_1715_ = v___x_1678_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_1716_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1706_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 1, v___x_1713_);
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
    mut v_len_1721_: *mut crate::leanh::LeanObject,
    mut v_aig_1722_: *mut crate::leanh::LeanObject,
    mut v_idx_1723_: *mut crate::leanh::LeanObject,
    mut v_s_1724_: *mut crate::leanh::LeanObject,
    mut v_lhs_1725_: *mut crate::leanh::LeanObject,
    mut v_rhs_1726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1735_: u8 = 0;
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: u8 = 0;
    let mut v___y_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: u8 = 0;
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: u8 = 0;
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: u8 = 0;
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: u8 = 0;
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1744_ = lean_nat_dec_lt(v_idx_1723_, v_len_1721_);
                if v___x_1744_ == 0 {
                    crate::leanh::lean_dec(v_idx_1723_);
                    v___x_1756_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1756_, 0, v_aig_1722_);
                    crate::leanh::lean_ctor_set(v___x_1756_, 1, v_s_1724_);
                    return v___x_1756_;
                } else {
                    v_ref_1757_ = lean_array_fget_borrowed(v_lhs_1725_, v_idx_1723_);
                    v___x_1758_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1759_ = lean_nat_shiftr(v_ref_1757_, v___x_1758_);
                    v___x_1760_ = lean_nat_land(v___x_1758_, v_ref_1757_);
                    v___x_1761_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1762_ = lean_nat_dec_eq(v___x_1760_, v___x_1761_);
                    crate::leanh::lean_dec(v___x_1760_);
                    if v___x_1762_ == 0 {
                        v___x_1763_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1763_, 0, v___x_1759_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1763_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_1744_,
                        );
                        v___y_1746_ = v___x_1763_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1764_ = 0;
                        v___x_1765_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1765_, 0, v___x_1759_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1765_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_1764_,
                        );
                        v___y_1746_ = v___x_1765_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1730_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1730_, 0, v___y_1728_);
                crate::leanh::lean_ctor_set(v___x_1730_, 1, v___y_1729_);
                v_res_1731_ = l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__0(v_aig_1722_, v___x_1730_);
                v_ref_1732_ = crate::leanh::lean_ctor_get(v_res_1731_, 1);
                crate::leanh::lean_inc_ref(v_ref_1732_);
                v_aig_1733_ = crate::leanh::lean_ctor_get(v_res_1731_, 0);
                crate::leanh::lean_inc_ref(v_aig_1733_);
                crate::leanh::lean_dec_ref(v_res_1731_);
                v_gate_1734_ = crate::leanh::lean_ctor_get(v_ref_1732_, 0);
                crate::leanh::lean_inc(v_gate_1734_);
                v_invert_1735_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_1732_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_dec_ref(v_ref_1732_);
                v___x_1736_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1737_ = lean_nat_add(v_idx_1723_, v___x_1736_);
                crate::leanh::lean_dec(v_idx_1723_);
                v___x_1738_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1739_ = lean_nat_mul(v_gate_1734_, v___x_1738_);
                crate::leanh::lean_dec(v_gate_1734_);
                v___x_1740_ = l_Bool_toNat(v_invert_1735_);
                v___x_1741_ = lean_nat_lor(v___x_1739_, v___x_1740_);
                crate::leanh::lean_dec(v___x_1740_);
                crate::leanh::lean_dec(v___x_1739_);
                v_s_1742_ = lean_array_push(v_s_1724_, v___x_1741_);
                v_aig_1722_ = v_aig_1733_;
                v_idx_1723_ = v___x_1737_;
                v_s_1724_ = v_s_1742_;
                state = 0;
                continue;
            }
            2 => {
                v_ref_1747_ = lean_array_fget_borrowed(v_rhs_1726_, v_idx_1723_);
                v___x_1748_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1749_ = lean_nat_shiftr(v_ref_1747_, v___x_1748_);
                v___x_1750_ = lean_nat_land(v___x_1748_, v_ref_1747_);
                v___x_1751_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1752_ = lean_nat_dec_eq(v___x_1750_, v___x_1751_);
                crate::leanh::lean_dec(v___x_1750_);
                if v___x_1752_ == 0 {
                    v___x_1753_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1753_, 0, v___x_1749_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1753_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1744_,
                    );
                    v___y_1728_ = v___y_1746_;
                    v___y_1729_ = v___x_1753_;
                    state = 1;
                    continue;
                } else {
                    v___x_1754_ = 0;
                    v___x_1755_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1755_, 0, v___x_1749_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1755_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_len_1766_: *mut crate::leanh::LeanObject,
    mut v_aig_1767_: *mut crate::leanh::LeanObject,
    mut v_idx_1768_: *mut crate::leanh::LeanObject,
    mut v_s_1769_: *mut crate::leanh::LeanObject,
    mut v_lhs_1770_: *mut crate::leanh::LeanObject,
    mut v_rhs_1771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1772_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__4___redArg(v_len_1766_, v_aig_1767_, v_idx_1768_, v_s_1769_, v_lhs_1770_, v_rhs_1771_);
    crate::leanh::lean_dec_ref(v_rhs_1771_);
    crate::leanh::lean_dec_ref(v_lhs_1770_);
    crate::leanh::lean_dec(v_len_1766_);
    return v_res_1772_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1___redArg(
    mut v_len_1773_: *mut crate::leanh::LeanObject,
    mut v_aig_1774_: *mut crate::leanh::LeanObject,
    mut v_input_1775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lhs_1776_ = crate::leanh::lean_ctor_get(v_input_1775_, 0);
    v_rhs_1777_ = crate::leanh::lean_ctor_get(v_input_1775_, 1);
    v___x_1778_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1779_ = lean_mk_empty_array_with_capacity(v_len_1773_);
    v___x_1780_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__4___redArg(v_len_1773_, v_aig_1774_, v___x_1778_, v___x_1779_, v_lhs_1776_, v_rhs_1777_);
    return v___x_1780_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1___redArg___boxed(
    mut v_len_1781_: *mut crate::leanh::LeanObject,
    mut v_aig_1782_: *mut crate::leanh::LeanObject,
    mut v_input_1783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1784_ = l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1___redArg(v_len_1781_, v_aig_1782_, v_input_1783_);
    crate::leanh::lean_dec_ref(v_input_1783_);
    crate::leanh::lean_dec(v_len_1781_);
    return v_res_1784_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0(
    mut v_w_1785_: *mut crate::leanh::LeanObject,
    mut v_aig_1786_: *mut crate::leanh::LeanObject,
    mut v_pair_1787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1788_ = l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1___redArg(v_w_1785_, v_aig_1786_, v_pair_1787_);
    v_aig_1789_ = crate::leanh::lean_ctor_get(v_res_1788_, 0);
    crate::leanh::lean_inc_ref(v_aig_1789_);
    v_vec_1790_ = crate::leanh::lean_ctor_get(v_res_1788_, 1);
    crate::leanh::lean_inc_ref(v_vec_1790_);
    crate::leanh::lean_dec_ref(v_res_1788_);
    v___x_1791_ = l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg(v_w_1785_, v_aig_1789_, v_vec_1790_);
    crate::leanh::lean_dec_ref(v_vec_1790_);
    return v___x_1791_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0___boxed(
    mut v_w_1792_: *mut crate::leanh::LeanObject,
    mut v_aig_1793_: *mut crate::leanh::LeanObject,
    mut v_pair_1794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1795_ =
        l_Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0(
            v_w_1792_,
            v_aig_1793_,
            v_pair_1794_,
        );
    crate::leanh::lean_dec_ref(v_pair_1794_);
    crate::leanh::lean_dec(v_w_1792_);
    return v_res_1795_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11_spec__15___redArg(
    mut v___x_1796_: *mut crate::leanh::LeanObject,
    mut v_len_1797_: *mut crate::leanh::LeanObject,
    mut v_aig_1798_: *mut crate::leanh::LeanObject,
    mut v_idx_1799_: *mut crate::leanh::LeanObject,
    mut v_s_1800_: *mut crate::leanh::LeanObject,
    mut v_input_1801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1808_: u8 = 0;
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: u8 = 0;
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: u8 = 0;
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: u8 = 0;
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1817_ = lean_nat_dec_lt(v_idx_1799_, v_len_1797_);
                if v___x_1817_ == 0 {
                    crate::leanh::lean_dec(v_idx_1799_);
                    crate::leanh::lean_dec_ref(v___x_1796_);
                    v___x_1818_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1818_, 0, v_aig_1798_);
                    crate::leanh::lean_ctor_set(v___x_1818_, 1, v_s_1800_);
                    return v___x_1818_;
                } else {
                    v_ref_1819_ = lean_array_fget_borrowed(v_input_1801_, v_idx_1799_);
                    v___x_1820_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1821_ = lean_nat_shiftr(v_ref_1819_, v___x_1820_);
                    v___x_1822_ = lean_nat_land(v___x_1820_, v_ref_1819_);
                    v___x_1823_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1824_ = lean_nat_dec_eq(v___x_1822_, v___x_1823_);
                    crate::leanh::lean_dec(v___x_1822_);
                    if v___x_1824_ == 0 {
                        v___x_1825_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1825_, 0, v___x_1821_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1825_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_1817_,
                        );
                        v___y_1803_ = v___x_1825_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1826_ = 0;
                        v___x_1827_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1827_, 0, v___x_1821_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1827_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_1826_,
                        );
                        v___y_1803_ = v___x_1827_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___x_1796_);
                v_res_1804_ = crate::leanh::lean_apply_2(v___x_1796_, v_aig_1798_, v___y_1803_);
                v_ref_1805_ = crate::leanh::lean_ctor_get(v_res_1804_, 1);
                crate::leanh::lean_inc_ref(v_ref_1805_);
                v_aig_1806_ = crate::leanh::lean_ctor_get(v_res_1804_, 0);
                crate::leanh::lean_inc_ref(v_aig_1806_);
                crate::leanh::lean_dec_ref(v_res_1804_);
                v_gate_1807_ = crate::leanh::lean_ctor_get(v_ref_1805_, 0);
                crate::leanh::lean_inc(v_gate_1807_);
                v_invert_1808_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_1805_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_dec_ref(v_ref_1805_);
                v___x_1809_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1810_ = lean_nat_add(v_idx_1799_, v___x_1809_);
                crate::leanh::lean_dec(v_idx_1799_);
                v___x_1811_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1812_ = lean_nat_mul(v_gate_1807_, v___x_1811_);
                crate::leanh::lean_dec(v_gate_1807_);
                v___x_1813_ = l_Bool_toNat(v_invert_1808_);
                v___x_1814_ = lean_nat_lor(v___x_1812_, v___x_1813_);
                crate::leanh::lean_dec(v___x_1813_);
                crate::leanh::lean_dec(v___x_1812_);
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
    mut v___x_1828_: *mut crate::leanh::LeanObject,
    mut v_len_1829_: *mut crate::leanh::LeanObject,
    mut v_aig_1830_: *mut crate::leanh::LeanObject,
    mut v_idx_1831_: *mut crate::leanh::LeanObject,
    mut v_s_1832_: *mut crate::leanh::LeanObject,
    mut v_input_1833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1834_ = l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11_spec__15___redArg(v___x_1828_, v_len_1829_, v_aig_1830_, v_idx_1831_, v_s_1832_, v_input_1833_);
    crate::leanh::lean_dec_ref(v_input_1833_);
    crate::leanh::lean_dec(v_len_1829_);
    return v_res_1834_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11(
    mut v_len_1835_: *mut crate::leanh::LeanObject,
    mut v_aig_1836_: *mut crate::leanh::LeanObject,
    mut v_target_1837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vec_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_func_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_vec_1838_ = crate::leanh::lean_ctor_get(v_target_1837_, 0);
    crate::leanh::lean_inc_ref(v_vec_1838_);
    v_func_1839_ = crate::leanh::lean_ctor_get(v_target_1837_, 1);
    crate::leanh::lean_inc_ref(v_func_1839_);
    crate::leanh::lean_dec_ref(v_target_1837_);
    v___x_1840_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1841_ = lean_mk_empty_array_with_capacity(v_len_1835_);
    v___x_1842_ = l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11_spec__15___redArg(v_func_1839_, v_len_1835_, v_aig_1836_, v___x_1840_, v___x_1841_, v_vec_1838_);
    crate::leanh::lean_dec_ref(v_vec_1838_);
    return v___x_1842_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11___boxed(
    mut v_len_1843_: *mut crate::leanh::LeanObject,
    mut v_aig_1844_: *mut crate::leanh::LeanObject,
    mut v_target_1845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1846_ = l_Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11(v_len_1843_, v_aig_1844_, v_target_1845_);
    crate::leanh::lean_dec(v_len_1843_);
    return v_res_1846_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5___lam__0(
    mut v___y_1847_: *mut crate::leanh::LeanObject,
    mut v___y_1848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_invert_1849_: u8 = 0;
    let mut v_gate_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___x_1854_: u8 = 0;
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1859_: u8 = 0;
    let mut v_gate_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1863_: u8 = 0;
    let mut v___x_1864_: u8 = 0;
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1869_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_invert_1849_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1848_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1849_ == 0 {
                    v_gate_1850_ = crate::leanh::lean_ctor_get(v___y_1848_, 0);
                    v_isSharedCheck_1859_ = (!crate::leanh::lean_is_exclusive(v___y_1848_)) as u8;
                    if v_isSharedCheck_1859_ == 0 {
                        v___x_1852_ = v___y_1848_;
                        v_isShared_1853_ = v_isSharedCheck_1859_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1850_);
                        crate::leanh::lean_dec(v___y_1848_);
                        v___x_1852_ = crate::leanh::lean_box(0);
                        v_isShared_1853_ = v_isSharedCheck_1859_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_gate_1860_ = crate::leanh::lean_ctor_get(v___y_1848_, 0);
                    v_isSharedCheck_1869_ = (!crate::leanh::lean_is_exclusive(v___y_1848_)) as u8;
                    if v_isSharedCheck_1869_ == 0 {
                        v___x_1862_ = v___y_1848_;
                        v_isShared_1863_ = v_isSharedCheck_1869_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1860_);
                        crate::leanh::lean_dec(v___y_1848_);
                        v___x_1862_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1858_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_gate_1850_);
                    v___x_1856_ = v_reuseFailAlloc_1858_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1856_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1854_,
                );
                v___x_1857_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1857_, 0, v___y_1847_);
                crate::leanh::lean_ctor_set(v___x_1857_, 1, v___x_1856_);
                return v___x_1857_;
            }
            3 => {
                v___x_1864_ = 0;
                if v_isShared_1863_ == 0 {
                    v___x_1866_ = v___x_1862_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1868_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_gate_1860_);
                    v___x_1866_ = v_reuseFailAlloc_1868_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1866_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1864_,
                );
                v___x_1867_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1867_, 0, v___y_1847_);
                crate::leanh::lean_ctor_set(v___x_1867_, 1, v___x_1866_);
                return v___x_1867_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5(
    mut v_w_1871_: *mut crate::leanh::LeanObject,
    mut v_aig_1872_: *mut crate::leanh::LeanObject,
    mut v_s_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1874_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5___closed__0;
    v___x_1875_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1875_, 0, v_s_1873_);
    crate::leanh::lean_ctor_set(v___x_1875_, 1, v___f_1874_);
    v___x_1876_ = l_Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11(v_w_1871_, v_aig_1872_, v___x_1875_);
    return v___x_1876_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5___boxed(
    mut v_w_1877_: *mut crate::leanh::LeanObject,
    mut v_aig_1878_: *mut crate::leanh::LeanObject,
    mut v_s_1879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1880_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5(v_w_1877_, v_aig_1878_, v_s_1879_);
    crate::leanh::lean_dec(v_w_1877_);
    return v_res_1880_;
}
pub unsafe fn l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6_spec__13_spec__18_spec__25(
    mut v_aig_1881_: *mut crate::leanh::LeanObject,
    mut v_input_1882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1887_: u8 = 0;
    let mut v_aig_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1891_: u8 = 0;
    let mut v_gate_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1895_: u8 = 0;
    let mut v___x_1896_: u8 = 0;
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1903_: u8 = 0;
    let mut v_isSharedCheck_1904_: u8 = 0;
    let mut v_unused_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1909_: u8 = 0;
    let mut v_gate_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1913_: u8 = 0;
    let mut v___x_1914_: u8 = 0;
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1921_: u8 = 0;
    let mut v_isSharedCheck_1922_: u8 = 0;
    let mut v_unused_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1928_: u8 = 0;
    let mut v___y_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1931_: u8 = 0;
    let mut v_gate_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1935_: u8 = 0;
    let mut v___x_1936_: u8 = 0;
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1943_: u8 = 0;
    let mut v_gate_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1947_: u8 = 0;
    let mut v___x_1948_: u8 = 0;
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1955_: u8 = 0;
    let mut v_invert_1956_: u8 = 0;
    let mut v_gate_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1960_: u8 = 0;
    let mut v___x_1961_: u8 = 0;
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1965_: u8 = 0;
    let mut v_gate_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1970_: u8 = 0;
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1974_: u8 = 0;
    let mut v_isSharedCheck_1975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_1924_ = crate::leanh::lean_ctor_get(v_input_1882_, 0);
                v_rhs_1925_ = crate::leanh::lean_ctor_get(v_input_1882_, 1);
                v_isSharedCheck_1975_ = (!crate::leanh::lean_is_exclusive(v_input_1882_)) as u8;
                if v_isSharedCheck_1975_ == 0 {
                    v___x_1927_ = v_input_1882_;
                    v_isShared_1928_ = v_isSharedCheck_1975_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_1925_);
                    crate::leanh::lean_inc(v_lhs_1924_);
                    crate::leanh::lean_dec(v_input_1882_);
                    v___x_1927_ = crate::leanh::lean_box(0);
                    v_isShared_1928_ = v_isSharedCheck_1975_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v_res_1885_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(v_aig_1881_, v___y_1884_);
                v_ref_1886_ = crate::leanh::lean_ctor_get(v_res_1885_, 1);
                crate::leanh::lean_inc_ref(v_ref_1886_);
                v_invert_1887_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_1886_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1887_ == 0 {
                    v_aig_1888_ = crate::leanh::lean_ctor_get(v_res_1885_, 0);
                    v_isSharedCheck_1904_ = (!crate::leanh::lean_is_exclusive(v_res_1885_)) as u8;
                    if v_isSharedCheck_1904_ == 0 {
                        v_unused_1905_ = crate::leanh::lean_ctor_get(v_res_1885_, 1);
                        crate::leanh::lean_dec(v_unused_1905_);
                        v___x_1890_ = v_res_1885_;
                        v_isShared_1891_ = v_isSharedCheck_1904_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_aig_1888_);
                        crate::leanh::lean_dec(v_res_1885_);
                        v___x_1890_ = crate::leanh::lean_box(0);
                        v_isShared_1891_ = v_isSharedCheck_1904_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_aig_1906_ = crate::leanh::lean_ctor_get(v_res_1885_, 0);
                    v_isSharedCheck_1922_ = (!crate::leanh::lean_is_exclusive(v_res_1885_)) as u8;
                    if v_isSharedCheck_1922_ == 0 {
                        v_unused_1923_ = crate::leanh::lean_ctor_get(v_res_1885_, 1);
                        crate::leanh::lean_dec(v_unused_1923_);
                        v___x_1908_ = v_res_1885_;
                        v_isShared_1909_ = v_isSharedCheck_1922_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_aig_1906_);
                        crate::leanh::lean_dec(v_res_1885_);
                        v___x_1908_ = crate::leanh::lean_box(0);
                        v_isShared_1909_ = v_isSharedCheck_1922_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_gate_1892_ = crate::leanh::lean_ctor_get(v_ref_1886_, 0);
                v_isSharedCheck_1903_ = (!crate::leanh::lean_is_exclusive(v_ref_1886_)) as u8;
                if v_isSharedCheck_1903_ == 0 {
                    v___x_1894_ = v_ref_1886_;
                    v_isShared_1895_ = v_isSharedCheck_1903_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_1892_);
                    crate::leanh::lean_dec(v_ref_1886_);
                    v___x_1894_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1902_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_gate_1892_);
                    v___x_1898_ = v_reuseFailAlloc_1902_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1898_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1896_,
                );
                if v_isShared_1891_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1890_, 1, v___x_1898_);
                    v___x_1900_ = v___x_1890_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1901_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_aig_1888_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 1, v___x_1898_);
                    v___x_1900_ = v_reuseFailAlloc_1901_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1900_;
            }
            6 => {
                v_gate_1910_ = crate::leanh::lean_ctor_get(v_ref_1886_, 0);
                v_isSharedCheck_1921_ = (!crate::leanh::lean_is_exclusive(v_ref_1886_)) as u8;
                if v_isSharedCheck_1921_ == 0 {
                    v___x_1912_ = v_ref_1886_;
                    v_isShared_1913_ = v_isSharedCheck_1921_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_1910_);
                    crate::leanh::lean_dec(v_ref_1886_);
                    v___x_1912_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1920_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_gate_1910_);
                    v___x_1916_ = v_reuseFailAlloc_1920_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1916_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1914_,
                );
                if v_isShared_1909_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1908_, 1, v___x_1916_);
                    v___x_1918_ = v___x_1908_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1919_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_aig_1906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1919_, 1, v___x_1916_);
                    v___x_1918_ = v_reuseFailAlloc_1919_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1918_;
            }
            10 => {
                v_invert_1956_ = crate::leanh::lean_ctor_get_uint8(
                    v_lhs_1924_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1956_ == 0 {
                    v_gate_1957_ = crate::leanh::lean_ctor_get(v_lhs_1924_, 0);
                    v_isSharedCheck_1965_ = (!crate::leanh::lean_is_exclusive(v_lhs_1924_)) as u8;
                    if v_isSharedCheck_1965_ == 0 {
                        v___x_1959_ = v_lhs_1924_;
                        v_isShared_1960_ = v_isSharedCheck_1965_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1957_);
                        crate::leanh::lean_dec(v_lhs_1924_);
                        v___x_1959_ = crate::leanh::lean_box(0);
                        v_isShared_1960_ = v_isSharedCheck_1965_;
                        state = 18;
                        continue;
                    }
                } else {
                    v_gate_1966_ = crate::leanh::lean_ctor_get(v_lhs_1924_, 0);
                    v_isSharedCheck_1974_ = (!crate::leanh::lean_is_exclusive(v_lhs_1924_)) as u8;
                    if v_isSharedCheck_1974_ == 0 {
                        v___x_1968_ = v_lhs_1924_;
                        v_isShared_1969_ = v_isSharedCheck_1974_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1966_);
                        crate::leanh::lean_dec(v_lhs_1924_);
                        v___x_1968_ = crate::leanh::lean_box(0);
                        v_isShared_1969_ = v_isSharedCheck_1974_;
                        state = 20;
                        continue;
                    }
                }
            }
            11 => {
                v_invert_1931_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_1925_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1931_ == 0 {
                    v_gate_1932_ = crate::leanh::lean_ctor_get(v_rhs_1925_, 0);
                    v_isSharedCheck_1943_ = (!crate::leanh::lean_is_exclusive(v_rhs_1925_)) as u8;
                    if v_isSharedCheck_1943_ == 0 {
                        v___x_1934_ = v_rhs_1925_;
                        v_isShared_1935_ = v_isSharedCheck_1943_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1932_);
                        crate::leanh::lean_dec(v_rhs_1925_);
                        v___x_1934_ = crate::leanh::lean_box(0);
                        v_isShared_1935_ = v_isSharedCheck_1943_;
                        state = 12;
                        continue;
                    }
                } else {
                    v_gate_1944_ = crate::leanh::lean_ctor_get(v_rhs_1925_, 0);
                    v_isSharedCheck_1955_ = (!crate::leanh::lean_is_exclusive(v_rhs_1925_)) as u8;
                    if v_isSharedCheck_1955_ == 0 {
                        v___x_1946_ = v_rhs_1925_;
                        v_isShared_1947_ = v_isSharedCheck_1955_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1944_);
                        crate::leanh::lean_dec(v_rhs_1925_);
                        v___x_1946_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1942_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_gate_1932_);
                    v___x_1938_ = v_reuseFailAlloc_1942_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1938_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1936_,
                );
                if v_isShared_1928_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1927_, 1, v___x_1938_);
                    crate::leanh::lean_ctor_set(v___x_1927_, 0, v___y_1930_);
                    v___x_1940_ = v___x_1927_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1941_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___y_1930_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1941_, 1, v___x_1938_);
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
                    v_reuseFailAlloc_1954_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_gate_1944_);
                    v___x_1950_ = v_reuseFailAlloc_1954_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1950_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1948_,
                );
                if v_isShared_1928_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1927_, 1, v___x_1950_);
                    crate::leanh::lean_ctor_set(v___x_1927_, 0, v___y_1930_);
                    v___x_1952_ = v___x_1927_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1953_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___y_1930_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1953_, 1, v___x_1950_);
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
                    v_reuseFailAlloc_1964_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_gate_1957_);
                    v___x_1963_ = v_reuseFailAlloc_1964_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1963_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                    v_reuseFailAlloc_1973_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_gate_1966_);
                    v___x_1972_ = v_reuseFailAlloc_1973_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1972_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_aig_1976_: *mut crate::leanh::LeanObject,
    mut v_input_1977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1988_: u8 = 0;
    let mut v_gate_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1993_: u8 = 0;
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1997_: u8 = 0;
    let mut v_gate_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2001_: u8 = 0;
    let mut v___x_2002_: u8 = 0;
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2006_: u8 = 0;
    let mut v_res_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2013_: u8 = 0;
    let mut v_aig_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2019_: u8 = 0;
    let mut v___x_2020_: u8 = 0;
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2024_: u8 = 0;
    let mut v_aig_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2030_: u8 = 0;
    let mut v___x_2031_: u8 = 0;
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2035_: u8 = 0;
    let mut v_lhs_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2040_: u8 = 0;
    let mut v_gate_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2042_: u8 = 0;
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2045_: u8 = 0;
    let mut v_gate_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2047_: u8 = 0;
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2050_: u8 = 0;
    let mut v___y_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: u8 = 0;
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: u8 = 0;
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: u8 = 0;
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: u8 = 0;
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2075_: u8 = 0;
    let mut v_isSharedCheck_2076_: u8 = 0;
    let mut v_isSharedCheck_2077_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_input_1977_);
                v_res_2007_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(v_aig_1976_, v_input_1977_);
                v_aig_2008_ = crate::leanh::lean_ctor_get(v_res_2007_, 0);
                crate::leanh::lean_inc_ref(v_aig_2008_);
                v_ref_2009_ = crate::leanh::lean_ctor_get(v_res_2007_, 1);
                crate::leanh::lean_inc_ref(v_ref_2009_);
                crate::leanh::lean_dec_ref(v_res_2007_);
                v_lhs_2036_ = crate::leanh::lean_ctor_get(v_input_1977_, 0);
                v_rhs_2037_ = crate::leanh::lean_ctor_get(v_input_1977_, 1);
                v_isSharedCheck_2077_ = (!crate::leanh::lean_is_exclusive(v_input_1977_)) as u8;
                if v_isSharedCheck_2077_ == 0 {
                    v___x_2039_ = v_input_1977_;
                    v_isShared_2040_ = v_isSharedCheck_2077_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_2037_);
                    crate::leanh::lean_inc(v_lhs_2036_);
                    crate::leanh::lean_dec(v_input_1977_);
                    v___x_2039_ = crate::leanh::lean_box(0);
                    v_isShared_2040_ = v_isSharedCheck_2077_;
                    state = 12;
                    continue;
                }
            }
            1 => {
                v___x_1982_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1982_, 0, v___y_1979_);
                crate::leanh::lean_ctor_set(v___x_1982_, 1, v___y_1981_);
                v___x_1983_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(v___y_1980_, v___x_1982_);
                return v___x_1983_;
            }
            2 => {
                v_invert_1988_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1986_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1988_ == 0 {
                    v_gate_1989_ = crate::leanh::lean_ctor_get(v___y_1986_, 0);
                    v_isSharedCheck_1997_ = (!crate::leanh::lean_is_exclusive(v___y_1986_)) as u8;
                    if v_isSharedCheck_1997_ == 0 {
                        v___x_1991_ = v___y_1986_;
                        v_isShared_1992_ = v_isSharedCheck_1997_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1989_);
                        crate::leanh::lean_dec(v___y_1986_);
                        v___x_1991_ = crate::leanh::lean_box(0);
                        v_isShared_1992_ = v_isSharedCheck_1997_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_gate_1998_ = crate::leanh::lean_ctor_get(v___y_1986_, 0);
                    v_isSharedCheck_2006_ = (!crate::leanh::lean_is_exclusive(v___y_1986_)) as u8;
                    if v_isSharedCheck_2006_ == 0 {
                        v___x_2000_ = v___y_1986_;
                        v_isShared_2001_ = v_isSharedCheck_2006_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1998_);
                        crate::leanh::lean_dec(v___y_1986_);
                        v___x_2000_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1996_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_gate_1989_);
                    v___x_1995_ = v_reuseFailAlloc_1996_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1995_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                    v_reuseFailAlloc_2005_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_gate_1998_);
                    v___x_2004_ = v_reuseFailAlloc_2005_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2004_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                v_invert_2013_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_2009_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_2013_ == 0 {
                    v_aig_2014_ = crate::leanh::lean_ctor_get(v_res_2012_, 0);
                    crate::leanh::lean_inc_ref(v_aig_2014_);
                    v_ref_2015_ = crate::leanh::lean_ctor_get(v_res_2012_, 1);
                    crate::leanh::lean_inc_ref(v_ref_2015_);
                    crate::leanh::lean_dec_ref(v_res_2012_);
                    v_gate_2016_ = crate::leanh::lean_ctor_get(v_ref_2009_, 0);
                    v_isSharedCheck_2024_ = (!crate::leanh::lean_is_exclusive(v_ref_2009_)) as u8;
                    if v_isSharedCheck_2024_ == 0 {
                        v___x_2018_ = v_ref_2009_;
                        v_isShared_2019_ = v_isSharedCheck_2024_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_2016_);
                        crate::leanh::lean_dec(v_ref_2009_);
                        v___x_2018_ = crate::leanh::lean_box(0);
                        v_isShared_2019_ = v_isSharedCheck_2024_;
                        state = 8;
                        continue;
                    }
                } else {
                    v_aig_2025_ = crate::leanh::lean_ctor_get(v_res_2012_, 0);
                    crate::leanh::lean_inc_ref(v_aig_2025_);
                    v_ref_2026_ = crate::leanh::lean_ctor_get(v_res_2012_, 1);
                    crate::leanh::lean_inc_ref(v_ref_2026_);
                    crate::leanh::lean_dec_ref(v_res_2012_);
                    v_gate_2027_ = crate::leanh::lean_ctor_get(v_ref_2009_, 0);
                    v_isSharedCheck_2035_ = (!crate::leanh::lean_is_exclusive(v_ref_2009_)) as u8;
                    if v_isSharedCheck_2035_ == 0 {
                        v___x_2029_ = v_ref_2009_;
                        v_isShared_2030_ = v_isSharedCheck_2035_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_2027_);
                        crate::leanh::lean_dec(v_ref_2009_);
                        v___x_2029_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2023_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_gate_2016_);
                    v___x_2022_ = v_reuseFailAlloc_2023_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2022_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                    v_reuseFailAlloc_2034_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_gate_2027_);
                    v___x_2033_ = v_reuseFailAlloc_2034_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2033_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2031_,
                );
                v___y_1985_ = v_aig_2025_;
                v___y_1986_ = v_ref_2026_;
                v___y_1987_ = v___x_2033_;
                state = 2;
                continue;
            }
            12 => {
                v_gate_2041_ = crate::leanh::lean_ctor_get(v_lhs_2036_, 0);
                v_invert_2042_ = crate::leanh::lean_ctor_get_uint8(
                    v_lhs_2036_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2076_ = (!crate::leanh::lean_is_exclusive(v_lhs_2036_)) as u8;
                if v_isSharedCheck_2076_ == 0 {
                    v___x_2044_ = v_lhs_2036_;
                    v_isShared_2045_ = v_isSharedCheck_2076_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_2041_);
                    crate::leanh::lean_dec(v_lhs_2036_);
                    v___x_2044_ = crate::leanh::lean_box(0);
                    v_isShared_2045_ = v_isSharedCheck_2076_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_gate_2046_ = crate::leanh::lean_ctor_get(v_rhs_2037_, 0);
                v_invert_2047_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_2037_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2075_ = (!crate::leanh::lean_is_exclusive(v_rhs_2037_)) as u8;
                if v_isSharedCheck_2075_ == 0 {
                    v___x_2049_ = v_rhs_2037_;
                    v_isShared_2050_ = v_isSharedCheck_2075_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_2046_);
                    crate::leanh::lean_dec(v_rhs_2037_);
                    v___x_2049_ = crate::leanh::lean_box(0);
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
                        v_reuseFailAlloc_2070_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_gate_2041_);
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
                        v_reuseFailAlloc_2074_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_gate_2041_);
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
                        v_reuseFailAlloc_2059_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_gate_2046_);
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
                        v_reuseFailAlloc_2066_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_gate_2046_);
                        v___x_2062_ = v_reuseFailAlloc_2066_;
                        state = 18;
                        continue;
                    }
                }
            }
            16 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2055_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2053_,
                );
                if v_isShared_2040_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2039_, 1, v___x_2055_);
                    crate::leanh::lean_ctor_set(v___x_2039_, 0, v___y_2052_);
                    v___x_2057_ = v___x_2039_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2058_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___y_2052_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2058_, 1, v___x_2055_);
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
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2062_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2060_,
                );
                if v_isShared_2040_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2039_, 1, v___x_2062_);
                    crate::leanh::lean_ctor_set(v___x_2039_, 0, v___y_2052_);
                    v___x_2064_ = v___x_2039_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2065_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___y_2052_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 1, v___x_2062_);
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
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2069_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2067_,
                );
                v___y_2052_ = v___x_2069_;
                state = 15;
                continue;
            }
            21 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2073_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_aig_2078_: *mut crate::leanh::LeanObject,
    mut v_input_2079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2089_: u8 = 0;
    let mut v_gate_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2091_: u8 = 0;
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2094_: u8 = 0;
    let mut v_gate_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2096_: u8 = 0;
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2099_: u8 = 0;
    let mut v_gate_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2101_: u8 = 0;
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2104_: u8 = 0;
    let mut v_cin_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v_lhs_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2126_: u8 = 0;
    let mut v_gate_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2128_: u8 = 0;
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2131_: u8 = 0;
    let mut v_lorRef_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2139_: u8 = 0;
    let mut v_isSharedCheck_2140_: u8 = 0;
    let mut v_reuseFailAlloc_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2144_: u8 = 0;
    let mut v_reuseFailAlloc_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2147_: u8 = 0;
    let mut v_isSharedCheck_2148_: u8 = 0;
    let mut v_isSharedCheck_2149_: u8 = 0;
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_2080_ = crate::leanh::lean_ctor_get(v_input_2079_, 0);
                crate::leanh::lean_inc_ref_n(v_lhs_2080_, 2);
                v_rhs_2081_ = crate::leanh::lean_ctor_get(v_input_2079_, 1);
                crate::leanh::lean_inc_ref_n(v_rhs_2081_, 2);
                v_cin_2082_ = crate::leanh::lean_ctor_get(v_input_2079_, 2);
                crate::leanh::lean_inc_ref(v_cin_2082_);
                crate::leanh::lean_dec_ref(v_input_2079_);
                v___x_2083_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2083_, 0, v_lhs_2080_);
                crate::leanh::lean_ctor_set(v___x_2083_, 1, v_rhs_2081_);
                v_res_2084_ = l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6_spec__13_spec__18_spec__24(v_aig_2078_, v___x_2083_);
                v_aig_2085_ = crate::leanh::lean_ctor_get(v_res_2084_, 0);
                v_ref_2086_ = crate::leanh::lean_ctor_get(v_res_2084_, 1);
                v_isSharedCheck_2150_ = (!crate::leanh::lean_is_exclusive(v_res_2084_)) as u8;
                if v_isSharedCheck_2150_ == 0 {
                    v___x_2088_ = v_res_2084_;
                    v_isShared_2089_ = v_isSharedCheck_2150_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_2086_);
                    crate::leanh::lean_inc(v_aig_2085_);
                    crate::leanh::lean_dec(v_res_2084_);
                    v___x_2088_ = crate::leanh::lean_box(0);
                    v_isShared_2089_ = v_isSharedCheck_2150_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_2090_ = crate::leanh::lean_ctor_get(v_lhs_2080_, 0);
                v_invert_2091_ = crate::leanh::lean_ctor_get_uint8(
                    v_lhs_2080_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2149_ = (!crate::leanh::lean_is_exclusive(v_lhs_2080_)) as u8;
                if v_isSharedCheck_2149_ == 0 {
                    v___x_2093_ = v_lhs_2080_;
                    v_isShared_2094_ = v_isSharedCheck_2149_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_2090_);
                    crate::leanh::lean_dec(v_lhs_2080_);
                    v___x_2093_ = crate::leanh::lean_box(0);
                    v_isShared_2094_ = v_isSharedCheck_2149_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_2095_ = crate::leanh::lean_ctor_get(v_rhs_2081_, 0);
                v_invert_2096_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_2081_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2148_ = (!crate::leanh::lean_is_exclusive(v_rhs_2081_)) as u8;
                if v_isSharedCheck_2148_ == 0 {
                    v___x_2098_ = v_rhs_2081_;
                    v_isShared_2099_ = v_isSharedCheck_2148_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_2095_);
                    crate::leanh::lean_dec(v_rhs_2081_);
                    v___x_2098_ = crate::leanh::lean_box(0);
                    v_isShared_2099_ = v_isSharedCheck_2148_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_gate_2100_ = crate::leanh::lean_ctor_get(v_cin_2082_, 0);
                v_invert_2101_ = crate::leanh::lean_ctor_get_uint8(
                    v_cin_2082_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2147_ = (!crate::leanh::lean_is_exclusive(v_cin_2082_)) as u8;
                if v_isSharedCheck_2147_ == 0 {
                    v___x_2103_ = v_cin_2082_;
                    v_isShared_2104_ = v_isSharedCheck_2147_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_2100_);
                    crate::leanh::lean_dec(v_cin_2082_);
                    v___x_2103_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2146_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_gate_2100_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2146_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_2101_,
                    );
                    v_cin_2106_ = v_reuseFailAlloc_2146_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2089_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2088_, 1, v_cin_2106_);
                    crate::leanh::lean_ctor_set(v___x_2088_, 0, v_ref_2086_);
                    v___x_2108_ = v___x_2088_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2145_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_ref_2086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_cin_2106_);
                    v___x_2108_ = v_reuseFailAlloc_2145_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_res_2109_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(v_aig_2085_, v___x_2108_);
                v_aig_2110_ = crate::leanh::lean_ctor_get(v_res_2109_, 0);
                v_ref_2111_ = crate::leanh::lean_ctor_get(v_res_2109_, 1);
                v_isSharedCheck_2144_ = (!crate::leanh::lean_is_exclusive(v_res_2109_)) as u8;
                if v_isSharedCheck_2144_ == 0 {
                    v___x_2113_ = v_res_2109_;
                    v_isShared_2114_ = v_isSharedCheck_2144_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_2111_);
                    crate::leanh::lean_inc(v_aig_2110_);
                    crate::leanh::lean_dec(v_res_2109_);
                    v___x_2113_ = crate::leanh::lean_box(0);
                    v_isShared_2114_ = v_isSharedCheck_2144_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2099_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2098_, 0, v_gate_2090_);
                    v_lhs_2116_ = v___x_2098_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2143_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_gate_2090_);
                    v_lhs_2116_ = v_reuseFailAlloc_2143_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_lhs_2116_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_2091_,
                );
                if v_isShared_2094_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2093_, 0, v_gate_2095_);
                    v_rhs_2118_ = v___x_2093_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2142_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_gate_2095_);
                    v_rhs_2118_ = v_reuseFailAlloc_2142_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_rhs_2118_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_2096_,
                );
                if v_isShared_2114_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2113_, 1, v_rhs_2118_);
                    crate::leanh::lean_ctor_set(v___x_2113_, 0, v_lhs_2116_);
                    v___x_2120_ = v___x_2113_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2141_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_lhs_2116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_rhs_2118_);
                    v___x_2120_ = v_reuseFailAlloc_2141_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_res_2121_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2(v_aig_2110_, v___x_2120_);
                v_aig_2122_ = crate::leanh::lean_ctor_get(v_res_2121_, 0);
                v_ref_2123_ = crate::leanh::lean_ctor_get(v_res_2121_, 1);
                v_isSharedCheck_2140_ = (!crate::leanh::lean_is_exclusive(v_res_2121_)) as u8;
                if v_isSharedCheck_2140_ == 0 {
                    v___x_2125_ = v_res_2121_;
                    v_isShared_2126_ = v_isSharedCheck_2140_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_2123_);
                    crate::leanh::lean_inc(v_aig_2122_);
                    crate::leanh::lean_dec(v_res_2121_);
                    v___x_2125_ = crate::leanh::lean_box(0);
                    v_isShared_2126_ = v_isSharedCheck_2140_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_gate_2127_ = crate::leanh::lean_ctor_get(v_ref_2111_, 0);
                v_invert_2128_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_2111_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2139_ = (!crate::leanh::lean_is_exclusive(v_ref_2111_)) as u8;
                if v_isSharedCheck_2139_ == 0 {
                    v___x_2130_ = v_ref_2111_;
                    v_isShared_2131_ = v_isSharedCheck_2139_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_2127_);
                    crate::leanh::lean_dec(v_ref_2111_);
                    v___x_2130_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2138_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_gate_2127_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2138_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_2128_,
                    );
                    v_lorRef_2133_ = v_reuseFailAlloc_2138_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_2126_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2125_, 0, v_lorRef_2133_);
                    v___x_2135_ = v___x_2125_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2137_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_lorRef_2133_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_ref_2123_);
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
    mut v_w_2151_: *mut crate::leanh::LeanObject,
    mut v_aig_2152_: *mut crate::leanh::LeanObject,
    mut v_lhs_2153_: *mut crate::leanh::LeanObject,
    mut v_rhs_2154_: *mut crate::leanh::LeanObject,
    mut v_curr_2155_: *mut crate::leanh::LeanObject,
    mut v_cin_2156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: u8 = 0;
    let mut v___y_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: u8 = 0;
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: u8 = 0;
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: u8 = 0;
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: u8 = 0;
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2167_ = lean_nat_dec_lt(v_curr_2155_, v_w_2151_);
                if v___x_2167_ == 0 {
                    crate::leanh::lean_dec(v_curr_2155_);
                    v___x_2179_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2179_, 0, v_aig_2152_);
                    crate::leanh::lean_ctor_set(v___x_2179_, 1, v_cin_2156_);
                    return v___x_2179_;
                } else {
                    v_ref_2180_ = lean_array_fget_borrowed(v_lhs_2153_, v_curr_2155_);
                    v___x_2181_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2182_ = lean_nat_shiftr(v_ref_2180_, v___x_2181_);
                    v___x_2183_ = lean_nat_land(v___x_2181_, v_ref_2180_);
                    v___x_2184_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2185_ = lean_nat_dec_eq(v___x_2183_, v___x_2184_);
                    crate::leanh::lean_dec(v___x_2183_);
                    if v___x_2185_ == 0 {
                        v___x_2186_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_2186_, 0, v___x_2182_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_2186_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_2167_,
                        );
                        v___y_2169_ = v___x_2186_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2187_ = 0;
                        v___x_2188_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_2188_, 0, v___x_2182_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_2188_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_2187_,
                        );
                        v___y_2169_ = v___x_2188_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2160_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2160_, 0, v___y_2158_);
                crate::leanh::lean_ctor_set(v___x_2160_, 1, v___y_2159_);
                crate::leanh::lean_ctor_set(v___x_2160_, 2, v_cin_2156_);
                v_res_2161_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6_spec__13_spec__18(v_aig_2152_, v___x_2160_);
                v_aig_2162_ = crate::leanh::lean_ctor_get(v_res_2161_, 0);
                crate::leanh::lean_inc_ref(v_aig_2162_);
                v_ref_2163_ = crate::leanh::lean_ctor_get(v_res_2161_, 1);
                crate::leanh::lean_inc_ref(v_ref_2163_);
                crate::leanh::lean_dec_ref(v_res_2161_);
                v___x_2164_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2165_ = lean_nat_add(v_curr_2155_, v___x_2164_);
                crate::leanh::lean_dec(v_curr_2155_);
                v_aig_2152_ = v_aig_2162_;
                v_curr_2155_ = v___x_2165_;
                v_cin_2156_ = v_ref_2163_;
                state = 0;
                continue;
            }
            2 => {
                v_ref_2170_ = lean_array_fget_borrowed(v_rhs_2154_, v_curr_2155_);
                v___x_2171_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2172_ = lean_nat_shiftr(v_ref_2170_, v___x_2171_);
                v___x_2173_ = lean_nat_land(v___x_2171_, v_ref_2170_);
                v___x_2174_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2175_ = lean_nat_dec_eq(v___x_2173_, v___x_2174_);
                crate::leanh::lean_dec(v___x_2173_);
                if v___x_2175_ == 0 {
                    v___x_2176_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2176_, 0, v___x_2172_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2176_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_2167_,
                    );
                    v___y_2158_ = v___y_2169_;
                    v___y_2159_ = v___x_2176_;
                    state = 1;
                    continue;
                } else {
                    v___x_2177_ = 0;
                    v___x_2178_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2178_, 0, v___x_2172_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2178_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_w_2189_: *mut crate::leanh::LeanObject,
    mut v_aig_2190_: *mut crate::leanh::LeanObject,
    mut v_lhs_2191_: *mut crate::leanh::LeanObject,
    mut v_rhs_2192_: *mut crate::leanh::LeanObject,
    mut v_curr_2193_: *mut crate::leanh::LeanObject,
    mut v_cin_2194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2195_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6_spec__13(v_w_2189_, v_aig_2190_, v_lhs_2191_, v_rhs_2192_, v_curr_2193_, v_cin_2194_);
    crate::leanh::lean_dec_ref(v_rhs_2192_);
    crate::leanh::lean_dec_ref(v_lhs_2191_);
    crate::leanh::lean_dec(v_w_2189_);
    return v_res_2195_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6(
    mut v_aig_2196_: *mut crate::leanh::LeanObject,
    mut v_input_2197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vec_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_w_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_vec_2198_ = crate::leanh::lean_ctor_get(v_input_2197_, 1);
    crate::leanh::lean_inc_ref(v_vec_2198_);
    v_w_2199_ = crate::leanh::lean_ctor_get(v_input_2197_, 0);
    crate::leanh::lean_inc(v_w_2199_);
    v_cin_2200_ = crate::leanh::lean_ctor_get(v_input_2197_, 2);
    crate::leanh::lean_inc_ref(v_cin_2200_);
    crate::leanh::lean_dec_ref(v_input_2197_);
    v_lhs_2201_ = crate::leanh::lean_ctor_get(v_vec_2198_, 0);
    crate::leanh::lean_inc_ref(v_lhs_2201_);
    v_rhs_2202_ = crate::leanh::lean_ctor_get(v_vec_2198_, 1);
    crate::leanh::lean_inc_ref(v_rhs_2202_);
    crate::leanh::lean_dec_ref(v_vec_2198_);
    v___x_2203_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2204_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at___00Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6_spec__13(v_w_2199_, v_aig_2196_, v_lhs_2201_, v_rhs_2202_, v___x_2203_, v_cin_2200_);
    crate::leanh::lean_dec_ref(v_rhs_2202_);
    crate::leanh::lean_dec_ref(v_lhs_2201_);
    crate::leanh::lean_dec(v_w_2199_);
    return v___x_2204_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1(
    mut v_w_2205_: *mut crate::leanh::LeanObject,
    mut v_aig_2206_: *mut crate::leanh::LeanObject,
    mut v_pair_2207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2212_: u8 = 0;
    let mut v_res_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: u8 = 0;
    let mut v_trueRef_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2223_: u8 = 0;
    let mut v_aig_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2227_: u8 = 0;
    let mut v_gate_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2231_: u8 = 0;
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2238_: u8 = 0;
    let mut v_isSharedCheck_2239_: u8 = 0;
    let mut v_unused_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2244_: u8 = 0;
    let mut v_gate_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2248_: u8 = 0;
    let mut v___x_2249_: u8 = 0;
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2256_: u8 = 0;
    let mut v_isSharedCheck_2257_: u8 = 0;
    let mut v_unused_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2260_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_2208_ = crate::leanh::lean_ctor_get(v_pair_2207_, 0);
                v_rhs_2209_ = crate::leanh::lean_ctor_get(v_pair_2207_, 1);
                v_isSharedCheck_2260_ = (!crate::leanh::lean_is_exclusive(v_pair_2207_)) as u8;
                if v_isSharedCheck_2260_ == 0 {
                    v___x_2211_ = v_pair_2207_;
                    v_isShared_2212_ = v_isSharedCheck_2260_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_2209_);
                    crate::leanh::lean_inc(v_lhs_2208_);
                    crate::leanh::lean_dec(v_pair_2207_);
                    v___x_2211_ = crate::leanh::lean_box(0);
                    v_isShared_2212_ = v_isSharedCheck_2260_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_res_2213_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5(v_w_2205_, v_aig_2206_, v_rhs_2209_);
                v_aig_2214_ = crate::leanh::lean_ctor_get(v_res_2213_, 0);
                crate::leanh::lean_inc_ref(v_aig_2214_);
                v_vec_2215_ = crate::leanh::lean_ctor_get(v_res_2213_, 1);
                crate::leanh::lean_inc_ref(v_vec_2215_);
                crate::leanh::lean_dec_ref(v_res_2213_);
                v___x_2216_ = 1;
                v_trueRef_2217_ = l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg___closed__0;
                if v_isShared_2212_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2211_, 1, v_vec_2215_);
                    v___x_2219_ = v___x_2211_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2259_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_lhs_2208_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2259_, 1, v_vec_2215_);
                    v___x_2219_ = v_reuseFailAlloc_2259_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2220_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2220_, 0, v_w_2205_);
                crate::leanh::lean_ctor_set(v___x_2220_, 1, v___x_2219_);
                crate::leanh::lean_ctor_set(v___x_2220_, 2, v_trueRef_2217_);
                v_res_2221_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__6(v_aig_2214_, v___x_2220_);
                v_ref_2222_ = crate::leanh::lean_ctor_get(v_res_2221_, 1);
                crate::leanh::lean_inc_ref(v_ref_2222_);
                v_invert_2223_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_2222_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_2223_ == 0 {
                    v_aig_2224_ = crate::leanh::lean_ctor_get(v_res_2221_, 0);
                    v_isSharedCheck_2239_ = (!crate::leanh::lean_is_exclusive(v_res_2221_)) as u8;
                    if v_isSharedCheck_2239_ == 0 {
                        v_unused_2240_ = crate::leanh::lean_ctor_get(v_res_2221_, 1);
                        crate::leanh::lean_dec(v_unused_2240_);
                        v___x_2226_ = v_res_2221_;
                        v_isShared_2227_ = v_isSharedCheck_2239_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_aig_2224_);
                        crate::leanh::lean_dec(v_res_2221_);
                        v___x_2226_ = crate::leanh::lean_box(0);
                        v_isShared_2227_ = v_isSharedCheck_2239_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_aig_2241_ = crate::leanh::lean_ctor_get(v_res_2221_, 0);
                    v_isSharedCheck_2257_ = (!crate::leanh::lean_is_exclusive(v_res_2221_)) as u8;
                    if v_isSharedCheck_2257_ == 0 {
                        v_unused_2258_ = crate::leanh::lean_ctor_get(v_res_2221_, 1);
                        crate::leanh::lean_dec(v_unused_2258_);
                        v___x_2243_ = v_res_2221_;
                        v_isShared_2244_ = v_isSharedCheck_2257_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_aig_2241_);
                        crate::leanh::lean_dec(v_res_2221_);
                        v___x_2243_ = crate::leanh::lean_box(0);
                        v_isShared_2244_ = v_isSharedCheck_2257_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v_gate_2228_ = crate::leanh::lean_ctor_get(v_ref_2222_, 0);
                v_isSharedCheck_2238_ = (!crate::leanh::lean_is_exclusive(v_ref_2222_)) as u8;
                if v_isSharedCheck_2238_ == 0 {
                    v___x_2230_ = v_ref_2222_;
                    v_isShared_2231_ = v_isSharedCheck_2238_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_2228_);
                    crate::leanh::lean_dec(v_ref_2222_);
                    v___x_2230_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2237_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_gate_2228_);
                    v___x_2233_ = v_reuseFailAlloc_2237_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2233_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2216_,
                );
                if v_isShared_2227_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2226_, 1, v___x_2233_);
                    v___x_2235_ = v___x_2226_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2236_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_aig_2224_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2233_);
                    v___x_2235_ = v_reuseFailAlloc_2236_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2235_;
            }
            7 => {
                v_gate_2245_ = crate::leanh::lean_ctor_get(v_ref_2222_, 0);
                v_isSharedCheck_2256_ = (!crate::leanh::lean_is_exclusive(v_ref_2222_)) as u8;
                if v_isSharedCheck_2256_ == 0 {
                    v___x_2247_ = v_ref_2222_;
                    v_isShared_2248_ = v_isSharedCheck_2256_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_2245_);
                    crate::leanh::lean_dec(v_ref_2222_);
                    v___x_2247_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2255_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_gate_2245_);
                    v___x_2251_ = v_reuseFailAlloc_2255_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2251_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2249_,
                );
                if v_isShared_2244_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2243_, 1, v___x_2251_);
                    v___x_2253_ = v___x_2243_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2254_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_aig_2241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2254_, 1, v___x_2251_);
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
    mut v_aig_2261_: *mut crate::leanh::LeanObject,
    mut v_input_2262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2267_: u8 = 0;
    let mut v_w_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_op_2270_: u8 = 0;
    let mut v_rhs_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2281_: u8 = 0;
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2289_: u8 = 0;
    let mut v_aig_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2294_: u8 = 0;
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2302_: u8 = 0;
    let mut v_isSharedCheck_2303_: u8 = 0;
    let mut v_unused_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2308_: u8 = 0;
    let mut v_aig_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2313_: u8 = 0;
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2321_: u8 = 0;
    let mut v_isSharedCheck_2322_: u8 = 0;
    let mut v_unused_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2325_: u8 = 0;
    let mut v_reuseFailAlloc_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2327_: u8 = 0;
    let mut v_unused_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2332_: u8 = 0;
    let mut v_w_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2338_: u8 = 0;
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2346_: u8 = 0;
    let mut v_aig_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2351_: u8 = 0;
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2362_: u8 = 0;
    let mut v_isSharedCheck_2363_: u8 = 0;
    let mut v_reuseFailAlloc_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2365_: u8 = 0;
    let mut v_isSharedCheck_2366_: u8 = 0;
    let mut v_unused_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_val_2263_ = crate::leanh::lean_ctor_get(v_input_2262_, 0);
                crate::leanh::lean_inc(v_val_2263_);
                if crate::leanh::lean_obj_tag(v_val_2263_) == 0 {
                    v_cache_2264_ = crate::leanh::lean_ctor_get(v_input_2262_, 1);
                    v_isSharedCheck_2327_ = (!crate::leanh::lean_is_exclusive(v_input_2262_)) as u8;
                    if v_isSharedCheck_2327_ == 0 {
                        v_unused_2328_ = crate::leanh::lean_ctor_get(v_input_2262_, 0);
                        crate::leanh::lean_dec(v_unused_2328_);
                        v___x_2266_ = v_input_2262_;
                        v_isShared_2267_ = v_isSharedCheck_2327_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cache_2264_);
                        crate::leanh::lean_dec(v_input_2262_);
                        v___x_2266_ = crate::leanh::lean_box(0);
                        v_isShared_2267_ = v_isSharedCheck_2327_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_cache_2329_ = crate::leanh::lean_ctor_get(v_input_2262_, 1);
                    v_isSharedCheck_2366_ = (!crate::leanh::lean_is_exclusive(v_input_2262_)) as u8;
                    if v_isSharedCheck_2366_ == 0 {
                        v_unused_2367_ = crate::leanh::lean_ctor_get(v_input_2262_, 0);
                        crate::leanh::lean_dec(v_unused_2367_);
                        v___x_2331_ = v_input_2262_;
                        v_isShared_2332_ = v_isSharedCheck_2366_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cache_2329_);
                        crate::leanh::lean_dec(v_input_2262_);
                        v___x_2331_ = crate::leanh::lean_box(0);
                        v_isShared_2332_ = v_isSharedCheck_2366_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v_w_2268_ = crate::leanh::lean_ctor_get(v_val_2263_, 0);
                crate::leanh::lean_inc(v_w_2268_);
                v_lhs_2269_ = crate::leanh::lean_ctor_get(v_val_2263_, 1);
                crate::leanh::lean_inc_ref(v_lhs_2269_);
                v_op_2270_ = crate::leanh::lean_ctor_get_uint8(
                    v_val_2263_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_rhs_2271_ = crate::leanh::lean_ctor_get(v_val_2263_, 2);
                crate::leanh::lean_inc_ref(v_rhs_2271_);
                crate::leanh::lean_dec_ref_known(v_val_2263_, 3);
                if v_isShared_2267_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2266_, 0, v_lhs_2269_);
                    v___x_2273_ = v___x_2266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2326_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_lhs_2269_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_cache_2264_);
                    v___x_2273_ = v_reuseFailAlloc_2326_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_w_2268_);
                v___x_2274_ =
                    l_Std_Tactic_BVDecide_BVExpr_bitblast(v_w_2268_, v_aig_2261_, v___x_2273_);
                v_result_2275_ = crate::leanh::lean_ctor_get(v___x_2274_, 0);
                crate::leanh::lean_inc_ref(v_result_2275_);
                v_cache_2276_ = crate::leanh::lean_ctor_get(v___x_2274_, 1);
                crate::leanh::lean_inc_ref(v_cache_2276_);
                crate::leanh::lean_dec_ref(v___x_2274_);
                v_aig_2277_ = crate::leanh::lean_ctor_get(v_result_2275_, 0);
                v_vec_2278_ = crate::leanh::lean_ctor_get(v_result_2275_, 1);
                v_isSharedCheck_2325_ = (!crate::leanh::lean_is_exclusive(v_result_2275_)) as u8;
                if v_isSharedCheck_2325_ == 0 {
                    v___x_2280_ = v_result_2275_;
                    v_isShared_2281_ = v_isSharedCheck_2325_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_2278_);
                    crate::leanh::lean_inc(v_aig_2277_);
                    crate::leanh::lean_dec(v_result_2275_);
                    v___x_2280_ = crate::leanh::lean_box(0);
                    v_isShared_2281_ = v_isSharedCheck_2325_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2281_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2280_, 1, v_cache_2276_);
                    crate::leanh::lean_ctor_set(v___x_2280_, 0, v_rhs_2271_);
                    v___x_2283_ = v___x_2280_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2324_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_rhs_2271_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_cache_2276_);
                    v___x_2283_ = v_reuseFailAlloc_2324_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_w_2268_);
                v___x_2284_ =
                    l_Std_Tactic_BVDecide_BVExpr_bitblast(v_w_2268_, v_aig_2277_, v___x_2283_);
                v_result_2285_ = crate::leanh::lean_ctor_get(v___x_2284_, 0);
                crate::leanh::lean_inc_ref(v_result_2285_);
                if v_op_2270_ == 0 {
                    v_cache_2286_ = crate::leanh::lean_ctor_get(v___x_2284_, 1);
                    v_isSharedCheck_2303_ = (!crate::leanh::lean_is_exclusive(v___x_2284_)) as u8;
                    if v_isSharedCheck_2303_ == 0 {
                        v_unused_2304_ = crate::leanh::lean_ctor_get(v___x_2284_, 0);
                        crate::leanh::lean_dec(v_unused_2304_);
                        v___x_2288_ = v___x_2284_;
                        v_isShared_2289_ = v_isSharedCheck_2303_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cache_2286_);
                        crate::leanh::lean_dec(v___x_2284_);
                        v___x_2288_ = crate::leanh::lean_box(0);
                        v_isShared_2289_ = v_isSharedCheck_2303_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_cache_2305_ = crate::leanh::lean_ctor_get(v___x_2284_, 1);
                    v_isSharedCheck_2322_ = (!crate::leanh::lean_is_exclusive(v___x_2284_)) as u8;
                    if v_isSharedCheck_2322_ == 0 {
                        v_unused_2323_ = crate::leanh::lean_ctor_get(v___x_2284_, 0);
                        crate::leanh::lean_dec(v_unused_2323_);
                        v___x_2307_ = v___x_2284_;
                        v_isShared_2308_ = v_isSharedCheck_2322_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cache_2305_);
                        crate::leanh::lean_dec(v___x_2284_);
                        v___x_2307_ = crate::leanh::lean_box(0);
                        v_isShared_2308_ = v_isSharedCheck_2322_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v_aig_2290_ = crate::leanh::lean_ctor_get(v_result_2285_, 0);
                v_vec_2291_ = crate::leanh::lean_ctor_get(v_result_2285_, 1);
                v_isSharedCheck_2302_ = (!crate::leanh::lean_is_exclusive(v_result_2285_)) as u8;
                if v_isSharedCheck_2302_ == 0 {
                    v___x_2293_ = v_result_2285_;
                    v_isShared_2294_ = v_isSharedCheck_2302_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_2291_);
                    crate::leanh::lean_inc(v_aig_2290_);
                    crate::leanh::lean_dec(v_result_2285_);
                    v___x_2293_ = crate::leanh::lean_box(0);
                    v_isShared_2294_ = v_isSharedCheck_2302_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2294_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2293_, 0, v_vec_2278_);
                    v___x_2296_ = v___x_2293_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2301_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_vec_2278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_vec_2291_);
                    v___x_2296_ = v_reuseFailAlloc_2301_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_res_2297_ = l_Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0(v_w_2268_, v_aig_2290_, v___x_2296_);
                crate::leanh::lean_dec_ref(v___x_2296_);
                crate::leanh::lean_dec(v_w_2268_);
                if v_isShared_2289_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2288_, 0, v_res_2297_);
                    v___x_2299_ = v___x_2288_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2300_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_res_2297_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_cache_2286_);
                    v___x_2299_ = v_reuseFailAlloc_2300_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2299_;
            }
            9 => {
                v_aig_2309_ = crate::leanh::lean_ctor_get(v_result_2285_, 0);
                v_vec_2310_ = crate::leanh::lean_ctor_get(v_result_2285_, 1);
                v_isSharedCheck_2321_ = (!crate::leanh::lean_is_exclusive(v_result_2285_)) as u8;
                if v_isSharedCheck_2321_ == 0 {
                    v___x_2312_ = v_result_2285_;
                    v_isShared_2313_ = v_isSharedCheck_2321_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_2310_);
                    crate::leanh::lean_inc(v_aig_2309_);
                    crate::leanh::lean_dec(v_result_2285_);
                    v___x_2312_ = crate::leanh::lean_box(0);
                    v_isShared_2313_ = v_isSharedCheck_2321_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_2313_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2312_, 0, v_vec_2278_);
                    v___x_2315_ = v___x_2312_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2320_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_vec_2278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_vec_2310_);
                    v___x_2315_ = v_reuseFailAlloc_2320_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_res_2316_ = l_Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1(v_w_2268_, v_aig_2309_, v___x_2315_);
                if v_isShared_2308_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2307_, 0, v_res_2316_);
                    v___x_2318_ = v___x_2307_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2319_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_res_2316_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_cache_2305_);
                    v___x_2318_ = v_reuseFailAlloc_2319_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2318_;
            }
            13 => {
                v_w_2333_ = crate::leanh::lean_ctor_get(v_val_2263_, 0);
                v_expr_2334_ = crate::leanh::lean_ctor_get(v_val_2263_, 1);
                v_idx_2335_ = crate::leanh::lean_ctor_get(v_val_2263_, 2);
                v_isSharedCheck_2365_ = (!crate::leanh::lean_is_exclusive(v_val_2263_)) as u8;
                if v_isSharedCheck_2365_ == 0 {
                    v___x_2337_ = v_val_2263_;
                    v_isShared_2338_ = v_isSharedCheck_2365_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_2335_);
                    crate::leanh::lean_inc(v_expr_2334_);
                    crate::leanh::lean_inc(v_w_2333_);
                    crate::leanh::lean_dec(v_val_2263_);
                    v___x_2337_ = crate::leanh::lean_box(0);
                    v_isShared_2338_ = v_isSharedCheck_2365_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2332_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2331_, 0, v_expr_2334_);
                    v___x_2340_ = v___x_2331_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2364_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_expr_2334_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_cache_2329_);
                    v___x_2340_ = v_reuseFailAlloc_2364_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                crate::leanh::lean_inc(v_w_2333_);
                v___x_2341_ =
                    l_Std_Tactic_BVDecide_BVExpr_bitblast(v_w_2333_, v_aig_2261_, v___x_2340_);
                v_result_2342_ = crate::leanh::lean_ctor_get(v___x_2341_, 0);
                v_cache_2343_ = crate::leanh::lean_ctor_get(v___x_2341_, 1);
                v_isSharedCheck_2363_ = (!crate::leanh::lean_is_exclusive(v___x_2341_)) as u8;
                if v_isSharedCheck_2363_ == 0 {
                    v___x_2345_ = v___x_2341_;
                    v_isShared_2346_ = v_isSharedCheck_2363_;
                    state = 16;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cache_2343_);
                    crate::leanh::lean_inc(v_result_2342_);
                    crate::leanh::lean_dec(v___x_2341_);
                    v___x_2345_ = crate::leanh::lean_box(0);
                    v_isShared_2346_ = v_isSharedCheck_2363_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v_aig_2347_ = crate::leanh::lean_ctor_get(v_result_2342_, 0);
                v_vec_2348_ = crate::leanh::lean_ctor_get(v_result_2342_, 1);
                v_isSharedCheck_2362_ = (!crate::leanh::lean_is_exclusive(v_result_2342_)) as u8;
                if v_isSharedCheck_2362_ == 0 {
                    v___x_2350_ = v_result_2342_;
                    v_isShared_2351_ = v_isSharedCheck_2362_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_2348_);
                    crate::leanh::lean_inc(v_aig_2347_);
                    crate::leanh::lean_dec(v_result_2342_);
                    v___x_2350_ = crate::leanh::lean_box(0);
                    v_isShared_2351_ = v_isSharedCheck_2362_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_2338_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2337_, 0);
                    crate::leanh::lean_ctor_set(v___x_2337_, 1, v_vec_2348_);
                    v___x_2353_ = v___x_2337_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2361_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_w_2333_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2361_, 1, v_vec_2348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2361_, 2, v_idx_2335_);
                    v___x_2353_ = v_reuseFailAlloc_2361_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v_res_2354_ = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__2___redArg(v___x_2353_);
                crate::leanh::lean_dec_ref(v___x_2353_);
                if v_isShared_2351_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2350_, 1, v_res_2354_);
                    v___x_2356_ = v___x_2350_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2360_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_aig_2347_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_res_2354_);
                    v___x_2356_ = v_reuseFailAlloc_2360_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2346_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2345_, 0, v___x_2356_);
                    v___x_2358_ = v___x_2345_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2359_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2356_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_cache_2343_);
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
    mut v_c_2368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2369_ = lean_mk_empty_array_with_capacity(v_c_2368_);
    return v___x_2369_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_c_2370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2371_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__3___redArg(v_c_2370_);
    crate::leanh::lean_dec(v_c_2370_);
    return v_res_2371_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__3(
    mut v_aig_2372_: *mut crate::leanh::LeanObject,
    mut v_c_2373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2374_ = lean_mk_empty_array_with_capacity(v_c_2373_);
    return v___x_2374_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__3___boxed(
    mut v_aig_2375_: *mut crate::leanh::LeanObject,
    mut v_c_2376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2377_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__3(v_aig_2375_, v_c_2376_);
    crate::leanh::lean_dec(v_c_2376_);
    crate::leanh::lean_dec_ref(v_aig_2375_);
    return v_res_2377_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1(
    mut v_len_2378_: *mut crate::leanh::LeanObject,
    mut v_aig_2379_: *mut crate::leanh::LeanObject,
    mut v_input_2380_: *mut crate::leanh::LeanObject,
    mut v_inst_2381_: *mut crate::leanh::LeanObject,
    mut v_inst_2382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2383_ = l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1___redArg(v_len_2378_, v_aig_2379_, v_input_2380_);
    return v___x_2383_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1___boxed(
    mut v_len_2384_: *mut crate::leanh::LeanObject,
    mut v_aig_2385_: *mut crate::leanh::LeanObject,
    mut v_input_2386_: *mut crate::leanh::LeanObject,
    mut v_inst_2387_: *mut crate::leanh::LeanObject,
    mut v_inst_2388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2389_ = l_Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1(v_len_2384_, v_aig_2385_, v_input_2386_, v_inst_2387_, v_inst_2388_);
    crate::leanh::lean_dec_ref(v_input_2386_);
    crate::leanh::lean_dec(v_len_2384_);
    return v_res_2389_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3(
    mut v_len_2390_: *mut crate::leanh::LeanObject,
    mut v_aig_2391_: *mut crate::leanh::LeanObject,
    mut v_vec_2392_: *mut crate::leanh::LeanObject,
    mut v_inst_2393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2394_ = l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___redArg(v_len_2390_, v_aig_2391_, v_vec_2392_);
    return v___x_2394_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3___boxed(
    mut v_len_2395_: *mut crate::leanh::LeanObject,
    mut v_aig_2396_: *mut crate::leanh::LeanObject,
    mut v_vec_2397_: *mut crate::leanh::LeanObject,
    mut v_inst_2398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2399_ = l_Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3(v_len_2395_, v_aig_2396_, v_vec_2397_, v_inst_2398_);
    crate::leanh::lean_dec_ref(v_vec_2397_);
    crate::leanh::lean_dec(v_len_2395_);
    return v_res_2399_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__4(
    mut v_len_2400_: *mut crate::leanh::LeanObject,
    mut v_aig_2401_: *mut crate::leanh::LeanObject,
    mut v_idx_2402_: *mut crate::leanh::LeanObject,
    mut v_s_2403_: *mut crate::leanh::LeanObject,
    mut v_hidx_2404_: *mut crate::leanh::LeanObject,
    mut v_lhs_2405_: *mut crate::leanh::LeanObject,
    mut v_rhs_2406_: *mut crate::leanh::LeanObject,
    mut v_inst_2407_: *mut crate::leanh::LeanObject,
    mut v_inst_2408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2409_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__4___redArg(v_len_2400_, v_aig_2401_, v_idx_2402_, v_s_2403_, v_lhs_2405_, v_rhs_2406_);
    return v___x_2409_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__4___boxed(
    mut v_len_2410_: *mut crate::leanh::LeanObject,
    mut v_aig_2411_: *mut crate::leanh::LeanObject,
    mut v_idx_2412_: *mut crate::leanh::LeanObject,
    mut v_s_2413_: *mut crate::leanh::LeanObject,
    mut v_hidx_2414_: *mut crate::leanh::LeanObject,
    mut v_lhs_2415_: *mut crate::leanh::LeanObject,
    mut v_rhs_2416_: *mut crate::leanh::LeanObject,
    mut v_inst_2417_: *mut crate::leanh::LeanObject,
    mut v_inst_2418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2419_ = l_Std_Sat_AIG_RefVec_zip_go___at___00Std_Sat_AIG_RefVec_zip___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__1_spec__4(v_len_2410_, v_aig_2411_, v_idx_2412_, v_s_2413_, v_hidx_2414_, v_lhs_2415_, v_rhs_2416_, v_inst_2417_, v_inst_2418_);
    crate::leanh::lean_dec_ref(v_rhs_2416_);
    crate::leanh::lean_dec_ref(v_lhs_2415_);
    crate::leanh::lean_dec(v_len_2410_);
    return v_res_2419_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3_spec__8(
    mut v_aig_2420_: *mut crate::leanh::LeanObject,
    mut v_acc_2421_: *mut crate::leanh::LeanObject,
    mut v_idx_2422_: *mut crate::leanh::LeanObject,
    mut v_len_2423_: *mut crate::leanh::LeanObject,
    mut v_input_2424_: *mut crate::leanh::LeanObject,
    mut v_inst_2425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2426_ = l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3_spec__8___redArg(v_aig_2420_, v_acc_2421_, v_idx_2422_, v_len_2423_, v_input_2424_);
    return v___x_2426_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3_spec__8___boxed(
    mut v_aig_2427_: *mut crate::leanh::LeanObject,
    mut v_acc_2428_: *mut crate::leanh::LeanObject,
    mut v_idx_2429_: *mut crate::leanh::LeanObject,
    mut v_len_2430_: *mut crate::leanh::LeanObject,
    mut v_input_2431_: *mut crate::leanh::LeanObject,
    mut v_inst_2432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2433_ = l_Std_Sat_AIG_RefVec_fold_go___at___00Std_Sat_AIG_RefVec_fold___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__3_spec__8(v_aig_2427_, v_acc_2428_, v_idx_2429_, v_len_2430_, v_input_2431_, v_inst_2432_);
    crate::leanh::lean_dec_ref(v_input_2431_);
    crate::leanh::lean_dec(v_len_2430_);
    return v_res_2433_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8(
    mut v_00_u03b2_2434_: *mut crate::leanh::LeanObject,
    mut v_m_2435_: *mut crate::leanh::LeanObject,
    mut v_a_2436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2437_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8___redArg(v_m_2435_, v_a_2436_);
    return v___x_2437_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8___boxed(
    mut v_00_u03b2_2438_: *mut crate::leanh::LeanObject,
    mut v_m_2439_: *mut crate::leanh::LeanObject,
    mut v_a_2440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2441_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8(v_00_u03b2_2438_, v_m_2439_, v_a_2440_);
    crate::leanh::lean_dec_ref(v_m_2439_);
    return v_res_2441_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10(
    mut v_00_u03b2_2442_: *mut crate::leanh::LeanObject,
    mut v_m_2443_: *mut crate::leanh::LeanObject,
    mut v_a_2444_: *mut crate::leanh::LeanObject,
    mut v_b_2445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2446_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10___redArg(v_m_2443_, v_a_2444_, v_b_2445_);
    return v___x_2446_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11_spec__15(
    mut v___x_2447_: *mut crate::leanh::LeanObject,
    mut v_len_2448_: *mut crate::leanh::LeanObject,
    mut v_aig_2449_: *mut crate::leanh::LeanObject,
    mut v_idx_2450_: *mut crate::leanh::LeanObject,
    mut v_hidx_2451_: *mut crate::leanh::LeanObject,
    mut v_s_2452_: *mut crate::leanh::LeanObject,
    mut v_input_2453_: *mut crate::leanh::LeanObject,
    mut v_inst_2454_: *mut crate::leanh::LeanObject,
    mut v_inst_2455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2456_ = l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11_spec__15___redArg(v___x_2447_, v_len_2448_, v_aig_2449_, v_idx_2450_, v_s_2452_, v_input_2453_);
    return v___x_2456_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11_spec__15___boxed(
    mut v___x_2457_: *mut crate::leanh::LeanObject,
    mut v_len_2458_: *mut crate::leanh::LeanObject,
    mut v_aig_2459_: *mut crate::leanh::LeanObject,
    mut v_idx_2460_: *mut crate::leanh::LeanObject,
    mut v_hidx_2461_: *mut crate::leanh::LeanObject,
    mut v_s_2462_: *mut crate::leanh::LeanObject,
    mut v_input_2463_: *mut crate::leanh::LeanObject,
    mut v_inst_2464_: *mut crate::leanh::LeanObject,
    mut v_inst_2465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2466_ = l_Std_Sat_AIG_RefVec_map_go___at___00Std_Sat_AIG_RefVec_map___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at___00Std_Tactic_BVDecide_BVPred_mkUlt___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__1_spec__5_spec__11_spec__15(v___x_2457_, v_len_2458_, v_aig_2459_, v_idx_2460_, v_hidx_2461_, v_s_2462_, v_input_2463_, v_inst_2464_, v_inst_2465_);
    crate::leanh::lean_dec_ref(v_input_2463_);
    crate::leanh::lean_dec(v_len_2458_);
    return v_res_2466_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8_spec__13(
    mut v_00_u03b2_2467_: *mut crate::leanh::LeanObject,
    mut v_a_2468_: *mut crate::leanh::LeanObject,
    mut v_x_2469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2470_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__8_spec__13___redArg(v_a_2468_, v_x_2469_);
    return v___x_2470_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__16(
    mut v_00_u03b2_2471_: *mut crate::leanh::LeanObject,
    mut v_a_2472_: *mut crate::leanh::LeanObject,
    mut v_x_2473_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2474_: u8 = 0;
    v___x_2474_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__16___redArg(v_a_2472_, v_x_2473_);
    return v___x_2474_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__16___boxed(
    mut v_00_u03b2_2475_: *mut crate::leanh::LeanObject,
    mut v_a_2476_: *mut crate::leanh::LeanObject,
    mut v_x_2477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2478_: u8 = 0;
    let mut v_r_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2478_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__16(v_00_u03b2_2475_, v_a_2476_, v_x_2477_);
    v_r_2479_ = crate::leanh::lean_box((v_res_2478_) as usize);
    return v_r_2479_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17(
    mut v_00_u03b2_2480_: *mut crate::leanh::LeanObject,
    mut v_data_2481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2482_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17___redArg(v_data_2481_);
    return v___x_2482_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__18(
    mut v_00_u03b2_2483_: *mut crate::leanh::LeanObject,
    mut v_a_2484_: *mut crate::leanh::LeanObject,
    mut v_b_2485_: *mut crate::leanh::LeanObject,
    mut v_x_2486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2487_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__18___redArg(v_a_2484_, v_b_2485_, v_x_2486_);
    return v___x_2487_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17_spec__21(
    mut v_00_u03b2_2488_: *mut crate::leanh::LeanObject,
    mut v_i_2489_: *mut crate::leanh::LeanObject,
    mut v_source_2490_: *mut crate::leanh::LeanObject,
    mut v_target_2491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2492_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17_spec__21___redArg(v_i_2489_, v_source_2490_, v_target_2491_);
    return v___x_2492_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17_spec__21_spec__24(
    mut v_00_u03b2_2493_: *mut crate::leanh::LeanObject,
    mut v_x_2494_: *mut crate::leanh::LeanObject,
    mut v_x_2495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2496_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVPred_mkEq___at___00Std_Tactic_BVDecide_BVPred_bitblast_spec__0_spec__2_spec__6_spec__10_spec__17_spec__21_spec__24___redArg(v_x_2494_, v_x_2495_);
    return v___x_2496_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(
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
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin);
}
