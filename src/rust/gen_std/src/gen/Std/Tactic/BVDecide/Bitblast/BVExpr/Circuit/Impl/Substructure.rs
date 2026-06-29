// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Substructure
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Pred Init.Omega
use crate::r#gen::Init::Data::Bool::l_Bool_toNat;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::Basic::{
    l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg, l_Std_Sat_AIG_instHashableFanin_hash,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::{
    l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed,
    l_Std_Tactic_BVDecide_instHashableBVBit_hash,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Pred::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred,
    l_Std_Tactic_BVDecide_BVPred_bitblast,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_lor;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_uint64_mix_hash,
};
pub static l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 8) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,0 as *mut crate::leanh::LeanObject] };
static mut l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0_value: crate::leanh::LeanArrayObject<1> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12___redArg(
    mut v_a_1010_: *mut crate::leanh::LeanObject,
    mut v_b_1011_: *mut crate::leanh::LeanObject,
    mut v_x_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1018_: u8 = 0;
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: u8 = 0;
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1028_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1012_) == 0 {
                    crate::leanh::lean_dec(v_b_1011_);
                    crate::leanh::lean_dec(v_a_1010_);
                    return v_x_1012_;
                } else {
                    v_key_1013_ = crate::leanh::lean_ctor_get(v_x_1012_, 0);
                    v_value_1014_ = crate::leanh::lean_ctor_get(v_x_1012_, 1);
                    v_tail_1015_ = crate::leanh::lean_ctor_get(v_x_1012_, 2);
                    v_isSharedCheck_1028_ = (!crate::leanh::lean_is_exclusive(v_x_1012_)) as u8;
                    if v_isSharedCheck_1028_ == 0 {
                        v___x_1017_ = v_x_1012_;
                        v_isShared_1018_ = v_isSharedCheck_1028_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1015_);
                        crate::leanh::lean_inc(v_value_1014_);
                        crate::leanh::lean_inc(v_key_1013_);
                        crate::leanh::lean_dec(v_x_1012_);
                        v___x_1017_ = crate::leanh::lean_box(0);
                        v_isShared_1018_ = v_isSharedCheck_1028_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1019_ = crate::leanh::lean_alloc_closure(
                    l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed as *mut core::ffi::c_void,
                    2,
                    0,
                );
                crate::leanh::lean_inc(v_a_1010_);
                crate::leanh::lean_inc(v_key_1013_);
                v___x_1020_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(
                    v___x_1019_,
                    v_key_1013_,
                    v_a_1010_,
                );
                if v___x_1020_ == 0 {
                    v___x_1021_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12___redArg(v_a_1010_, v_b_1011_, v_tail_1015_);
                    if v_isShared_1018_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1017_, 2, v___x_1021_);
                        v___x_1023_ = v___x_1017_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1024_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_key_1013_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_value_1014_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1024_, 2, v___x_1021_);
                        v___x_1023_ = v_reuseFailAlloc_1024_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_1014_);
                    crate::leanh::lean_dec(v_key_1013_);
                    if v_isShared_1018_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1017_, 1, v_b_1011_);
                        crate::leanh::lean_ctor_set(v___x_1017_, 0, v_a_1010_);
                        v___x_1026_ = v___x_1017_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1027_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1010_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_b_1011_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1027_, 2, v_tail_1015_);
                        v___x_1026_ = v_reuseFailAlloc_1027_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1023_;
            }
            3 => {
                return v___x_1026_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(
    mut v_a_1029_: *mut crate::leanh::LeanObject,
    mut v_x_1030_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1031_: u8 = 0;
    let mut v_key_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1030_) == 0 {
                    crate::leanh::lean_dec(v_a_1029_);
                    v___x_1031_ = 0;
                    return v___x_1031_;
                } else {
                    v_key_1032_ = crate::leanh::lean_ctor_get(v_x_1030_, 0);
                    crate::leanh::lean_inc(v_key_1032_);
                    v_tail_1033_ = crate::leanh::lean_ctor_get(v_x_1030_, 2);
                    crate::leanh::lean_inc(v_tail_1033_);
                    crate::leanh::lean_dec_ref_known(v_x_1030_, 3);
                    v___x_1034_ = crate::leanh::lean_alloc_closure(
                        l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed
                            as *mut core::ffi::c_void,
                        2,
                        0,
                    );
                    crate::leanh::lean_inc(v_a_1029_);
                    v___x_1035_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(
                        v___x_1034_,
                        v_key_1032_,
                        v_a_1029_,
                    );
                    if v___x_1035_ == 0 {
                        v_x_1030_ = v_tail_1033_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1033_);
                        crate::leanh::lean_dec(v_a_1029_);
                        return v___x_1035_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg___boxed(
    mut v_a_1037_: *mut crate::leanh::LeanObject,
    mut v_x_1038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1039_: u8 = 0;
    let mut v_r_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1039_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(v_a_1037_, v_x_1038_);
    v_r_1040_ = crate::leanh::lean_box((v_res_1039_) as usize);
    return v_r_1040_;
}
pub unsafe fn l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(
    mut v_x_1041_: *mut crate::leanh::LeanObject,
) -> u64 {
    match crate::leanh::lean_obj_tag(v_x_1041_) {
        0 => {
            let mut v___x_1042_: u64 = 0;
            v___x_1042_ = 0u64;
            return v___x_1042_;
        }
        1 => {
            let mut v_idx_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1044_: u64 = 0;
            let mut v___x_1045_: u64 = 0;
            let mut v___x_1046_: u64 = 0;
            v_idx_1043_ = crate::leanh::lean_ctor_get(v_x_1041_, 0);
            v___x_1044_ = 1u64;
            v___x_1045_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_idx_1043_);
            v___x_1046_ = lean_uint64_mix_hash(v___x_1044_, v___x_1045_);
            return v___x_1046_;
        }
        _ => {
            let mut v_l_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1049_: u64 = 0;
            let mut v___x_1050_: u64 = 0;
            let mut v___x_1051_: u64 = 0;
            let mut v___x_1052_: u64 = 0;
            let mut v___x_1053_: u64 = 0;
            v_l_1047_ = crate::leanh::lean_ctor_get(v_x_1041_, 0);
            v_r_1048_ = crate::leanh::lean_ctor_get(v_x_1041_, 1);
            v___x_1049_ = 2u64;
            v___x_1050_ = l_Std_Sat_AIG_instHashableFanin_hash(v_l_1047_);
            v___x_1051_ = lean_uint64_mix_hash(v___x_1049_, v___x_1050_);
            v___x_1052_ = l_Std_Sat_AIG_instHashableFanin_hash(v_r_1048_);
            v___x_1053_ = lean_uint64_mix_hash(v___x_1051_, v___x_1052_);
            return v___x_1053_;
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6___boxed(
    mut v_x_1054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1055_: u64 = 0;
    let mut v_r_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1055_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(v_x_1054_);
    crate::leanh::lean_dec(v_x_1054_);
    v_r_1056_ = crate::leanh::lean_box_uint64(v_res_1055_);
    return v_r_1056_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(
    mut v_x_1057_: *mut crate::leanh::LeanObject,
    mut v_x_1058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1064_: u8 = 0;
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: u64 = 0;
    let mut v___x_1067_: u64 = 0;
    let mut v___x_1068_: u64 = 0;
    let mut v_fold_1069_: u64 = 0;
    let mut v___x_1070_: u64 = 0;
    let mut v___x_1071_: u64 = 0;
    let mut v___x_1072_: u64 = 0;
    let mut v___x_1073_: usize = 0;
    let mut v___x_1074_: usize = 0;
    let mut v___x_1075_: usize = 0;
    let mut v___x_1076_: usize = 0;
    let mut v___x_1077_: usize = 0;
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1084_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1058_) == 0 {
                    return v_x_1057_;
                } else {
                    v_key_1059_ = crate::leanh::lean_ctor_get(v_x_1058_, 0);
                    v_value_1060_ = crate::leanh::lean_ctor_get(v_x_1058_, 1);
                    v_tail_1061_ = crate::leanh::lean_ctor_get(v_x_1058_, 2);
                    v_isSharedCheck_1084_ = (!crate::leanh::lean_is_exclusive(v_x_1058_)) as u8;
                    if v_isSharedCheck_1084_ == 0 {
                        v___x_1063_ = v_x_1058_;
                        v_isShared_1064_ = v_isSharedCheck_1084_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1061_);
                        crate::leanh::lean_inc(v_value_1060_);
                        crate::leanh::lean_inc(v_key_1059_);
                        crate::leanh::lean_dec(v_x_1058_);
                        v___x_1063_ = crate::leanh::lean_box(0);
                        v_isShared_1064_ = v_isSharedCheck_1084_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1065_ = lean_array_get_size(v_x_1057_);
                v___x_1066_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(v_key_1059_);
                v___x_1067_ = 32u64;
                v___x_1068_ = lean_uint64_shift_right(v___x_1066_, v___x_1067_);
                v_fold_1069_ = lean_uint64_xor(v___x_1066_, v___x_1068_);
                v___x_1070_ = 16u64;
                v___x_1071_ = lean_uint64_shift_right(v_fold_1069_, v___x_1070_);
                v___x_1072_ = lean_uint64_xor(v_fold_1069_, v___x_1071_);
                v___x_1073_ = lean_uint64_to_usize(v___x_1072_);
                v___x_1074_ = lean_usize_of_nat(v___x_1065_);
                v___x_1075_ = 1usize;
                v___x_1076_ = lean_usize_sub(v___x_1074_, v___x_1075_);
                v___x_1077_ = lean_usize_land(v___x_1073_, v___x_1076_);
                v___x_1078_ = lean_array_uget_borrowed(v_x_1057_, v___x_1077_);
                crate::leanh::lean_inc(v___x_1078_);
                if v_isShared_1064_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1063_, 2, v___x_1078_);
                    v___x_1080_ = v___x_1063_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1083_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_key_1059_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_value_1060_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 2, v___x_1078_);
                    v___x_1080_ = v_reuseFailAlloc_1083_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1081_ = lean_array_uset(v_x_1057_, v___x_1077_, v___x_1080_);
                v_x_1057_ = v___x_1081_;
                v_x_1058_ = v_tail_1061_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(
    mut v_i_1085_: *mut crate::leanh::LeanObject,
    mut v_source_1086_: *mut crate::leanh::LeanObject,
    mut v_target_1087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: u8 = 0;
    let mut v_es_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1088_ = lean_array_get_size(v_source_1086_);
                v___x_1089_ = lean_nat_dec_lt(v_i_1085_, v___x_1088_);
                if v___x_1089_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1086_);
                    crate::leanh::lean_dec(v_i_1085_);
                    return v_target_1087_;
                } else {
                    v_es_1090_ = lean_array_fget(v_source_1086_, v_i_1085_);
                    v___x_1091_ = crate::leanh::lean_box(0);
                    v_source_1092_ = lean_array_fset(v_source_1086_, v_i_1085_, v___x_1091_);
                    v_target_1093_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_target_1087_, v_es_1090_);
                    v___x_1094_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1095_ = lean_nat_add(v_i_1085_, v___x_1094_);
                    crate::leanh::lean_dec(v_i_1085_);
                    v_i_1085_ = v___x_1095_;
                    v_source_1086_ = v_source_1092_;
                    v_target_1087_ = v_target_1093_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11___redArg(
    mut v_data_1097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1098_ = lean_array_get_size(v_data_1097_);
    v___x_1099_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1100_ = lean_nat_mul(v___x_1098_, v___x_1099_);
    v___x_1101_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1102_ = crate::leanh::lean_box(0);
    v___x_1103_ = lean_mk_array(v_nbuckets_1100_, v___x_1102_);
    v___x_1104_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(v___x_1101_, v_data_1097_, v___x_1103_);
    return v___x_1104_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(
    mut v_m_1105_: *mut crate::leanh::LeanObject,
    mut v_a_1106_: *mut crate::leanh::LeanObject,
    mut v_b_1107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1112_: u8 = 0;
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: u64 = 0;
    let mut v___x_1115_: u64 = 0;
    let mut v___x_1116_: u64 = 0;
    let mut v_fold_1117_: u64 = 0;
    let mut v___x_1118_: u64 = 0;
    let mut v___x_1119_: u64 = 0;
    let mut v___x_1120_: u64 = 0;
    let mut v___x_1121_: usize = 0;
    let mut v___x_1122_: usize = 0;
    let mut v___x_1123_: usize = 0;
    let mut v___x_1124_: usize = 0;
    let mut v___x_1125_: usize = 0;
    let mut v_bkt_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: u8 = 0;
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: u8 = 0;
    let mut v_val_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1152_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1108_ = crate::leanh::lean_ctor_get(v_m_1105_, 0);
                v_buckets_1109_ = crate::leanh::lean_ctor_get(v_m_1105_, 1);
                v_isSharedCheck_1152_ = (!crate::leanh::lean_is_exclusive(v_m_1105_)) as u8;
                if v_isSharedCheck_1152_ == 0 {
                    v___x_1111_ = v_m_1105_;
                    v_isShared_1112_ = v_isSharedCheck_1152_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1109_);
                    crate::leanh::lean_inc(v_size_1108_);
                    crate::leanh::lean_dec(v_m_1105_);
                    v___x_1111_ = crate::leanh::lean_box(0);
                    v_isShared_1112_ = v_isSharedCheck_1152_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1113_ = lean_array_get_size(v_buckets_1109_);
                v___x_1114_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(v_a_1106_);
                v___x_1115_ = 32u64;
                v___x_1116_ = lean_uint64_shift_right(v___x_1114_, v___x_1115_);
                v_fold_1117_ = lean_uint64_xor(v___x_1114_, v___x_1116_);
                v___x_1118_ = 16u64;
                v___x_1119_ = lean_uint64_shift_right(v_fold_1117_, v___x_1118_);
                v___x_1120_ = lean_uint64_xor(v_fold_1117_, v___x_1119_);
                v___x_1121_ = lean_uint64_to_usize(v___x_1120_);
                v___x_1122_ = lean_usize_of_nat(v___x_1113_);
                v___x_1123_ = 1usize;
                v___x_1124_ = lean_usize_sub(v___x_1122_, v___x_1123_);
                v___x_1125_ = lean_usize_land(v___x_1121_, v___x_1124_);
                v_bkt_1126_ = lean_array_uget_borrowed(v_buckets_1109_, v___x_1125_);
                crate::leanh::lean_inc(v_bkt_1126_);
                crate::leanh::lean_inc(v_a_1106_);
                v___x_1127_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(v_a_1106_, v_bkt_1126_);
                if v___x_1127_ == 0 {
                    v___x_1128_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1129_ = lean_nat_add(v_size_1108_, v___x_1128_);
                    crate::leanh::lean_dec(v_size_1108_);
                    crate::leanh::lean_inc(v_bkt_1126_);
                    v___x_1130_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1130_, 0, v_a_1106_);
                    crate::leanh::lean_ctor_set(v___x_1130_, 1, v_b_1107_);
                    crate::leanh::lean_ctor_set(v___x_1130_, 2, v_bkt_1126_);
                    v_buckets_x27_1131_ =
                        lean_array_uset(v_buckets_1109_, v___x_1125_, v___x_1130_);
                    v___x_1132_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1133_ = lean_nat_mul(v_size_x27_1129_, v___x_1132_);
                    v___x_1134_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1135_ = lean_nat_div(v___x_1133_, v___x_1134_);
                    crate::leanh::lean_dec(v___x_1133_);
                    v___x_1136_ = lean_array_get_size(v_buckets_x27_1131_);
                    v___x_1137_ = lean_nat_dec_le(v___x_1135_, v___x_1136_);
                    crate::leanh::lean_dec(v___x_1135_);
                    if v___x_1137_ == 0 {
                        v_val_1138_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11___redArg(v_buckets_x27_1131_);
                        if v_isShared_1112_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1111_, 1, v_val_1138_);
                            crate::leanh::lean_ctor_set(v___x_1111_, 0, v_size_x27_1129_);
                            v___x_1140_ = v___x_1111_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1141_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1141_,
                                0,
                                v_size_x27_1129_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_val_1138_);
                            v___x_1140_ = v_reuseFailAlloc_1141_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1112_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1111_, 1, v_buckets_x27_1131_);
                            crate::leanh::lean_ctor_set(v___x_1111_, 0, v_size_x27_1129_);
                            v___x_1143_ = v___x_1111_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1144_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1144_,
                                0,
                                v_size_x27_1129_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1144_,
                                1,
                                v_buckets_x27_1131_,
                            );
                            v___x_1143_ = v_reuseFailAlloc_1144_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1126_);
                    v___x_1145_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1146_ =
                        lean_array_uset(v_buckets_1109_, v___x_1125_, v___x_1145_);
                    v___x_1147_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12___redArg(v_a_1106_, v_b_1107_, v_bkt_1126_);
                    v___x_1148_ = lean_array_uset(v_buckets_x27_1146_, v___x_1125_, v___x_1147_);
                    if v_isShared_1112_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1111_, 1, v___x_1148_);
                        v___x_1150_ = v___x_1111_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1151_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_size_1108_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1151_, 1, v___x_1148_);
                        v___x_1150_ = v_reuseFailAlloc_1151_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1140_;
            }
            3 => {
                return v___x_1143_;
            }
            4 => {
                return v___x_1150_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(
    mut v_aig_1153_: *mut crate::leanh::LeanObject,
    mut v_ref_1154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gate_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1156_: u8 = 0;
    let mut v_decls_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_gate_1155_ = crate::leanh::lean_ctor_get(v_ref_1154_, 0);
    v_invert_1156_ = crate::leanh::lean_ctor_get_uint8(
        v_ref_1154_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v_decls_1157_ = crate::leanh::lean_ctor_get(v_aig_1153_, 0);
    v_decl_1158_ = lean_array_fget_borrowed(v_decls_1157_, v_gate_1155_);
    if crate::leanh::lean_obj_tag(v_decl_1158_) == 0 {
        let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1159_ = crate::leanh::lean_box((v_invert_1156_) as usize);
        v___x_1160_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1160_, 0, v___x_1159_);
        return v___x_1160_;
    } else {
        let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1161_ = crate::leanh::lean_box(0);
        return v___x_1161_;
    }
}
pub unsafe fn l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2___boxed(
    mut v_aig_1162_: *mut crate::leanh::LeanObject,
    mut v_ref_1163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1164_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(v_aig_1162_, v_ref_1163_);
    crate::leanh::lean_dec_ref(v_ref_1163_);
    crate::leanh::lean_dec_ref(v_aig_1162_);
    return v_res_1164_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7___redArg(
    mut v_a_1165_: *mut crate::leanh::LeanObject,
    mut v_x_1166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: u8 = 0;
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1166_) == 0 {
                    crate::leanh::lean_dec(v_a_1165_);
                    v___x_1167_ = crate::leanh::lean_box(0);
                    return v___x_1167_;
                } else {
                    v_key_1168_ = crate::leanh::lean_ctor_get(v_x_1166_, 0);
                    crate::leanh::lean_inc(v_key_1168_);
                    v_value_1169_ = crate::leanh::lean_ctor_get(v_x_1166_, 1);
                    crate::leanh::lean_inc(v_value_1169_);
                    v_tail_1170_ = crate::leanh::lean_ctor_get(v_x_1166_, 2);
                    crate::leanh::lean_inc(v_tail_1170_);
                    crate::leanh::lean_dec_ref_known(v_x_1166_, 3);
                    v___x_1171_ = crate::leanh::lean_alloc_closure(
                        l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed
                            as *mut core::ffi::c_void,
                        2,
                        0,
                    );
                    crate::leanh::lean_inc(v_a_1165_);
                    v___x_1172_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(
                        v___x_1171_,
                        v_key_1168_,
                        v_a_1165_,
                    );
                    if v___x_1172_ == 0 {
                        crate::leanh::lean_dec(v_value_1169_);
                        v_x_1166_ = v_tail_1170_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1170_);
                        crate::leanh::lean_dec(v_a_1165_);
                        v___x_1174_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1174_, 0, v_value_1169_);
                        return v___x_1174_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(
    mut v_m_1175_: *mut crate::leanh::LeanObject,
    mut v_a_1176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: u64 = 0;
    let mut v___x_1180_: u64 = 0;
    let mut v___x_1181_: u64 = 0;
    let mut v_fold_1182_: u64 = 0;
    let mut v___x_1183_: u64 = 0;
    let mut v___x_1184_: u64 = 0;
    let mut v___x_1185_: u64 = 0;
    let mut v___x_1186_: usize = 0;
    let mut v___x_1187_: usize = 0;
    let mut v___x_1188_: usize = 0;
    let mut v___x_1189_: usize = 0;
    let mut v___x_1190_: usize = 0;
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1177_ = crate::leanh::lean_ctor_get(v_m_1175_, 1);
    v___x_1178_ = lean_array_get_size(v_buckets_1177_);
    v___x_1179_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(v_a_1176_);
    v___x_1180_ = 32u64;
    v___x_1181_ = lean_uint64_shift_right(v___x_1179_, v___x_1180_);
    v_fold_1182_ = lean_uint64_xor(v___x_1179_, v___x_1181_);
    v___x_1183_ = 16u64;
    v___x_1184_ = lean_uint64_shift_right(v_fold_1182_, v___x_1183_);
    v___x_1185_ = lean_uint64_xor(v_fold_1182_, v___x_1184_);
    v___x_1186_ = lean_uint64_to_usize(v___x_1185_);
    v___x_1187_ = lean_usize_of_nat(v___x_1178_);
    v___x_1188_ = 1usize;
    v___x_1189_ = lean_usize_sub(v___x_1187_, v___x_1188_);
    v___x_1190_ = lean_usize_land(v___x_1186_, v___x_1189_);
    v___x_1191_ = lean_array_uget_borrowed(v_buckets_1177_, v___x_1190_);
    crate::leanh::lean_inc(v___x_1191_);
    v___x_1192_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7___redArg(v_a_1176_, v___x_1191_);
    return v___x_1192_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_m_1193_: *mut crate::leanh::LeanObject,
    mut v_a_1194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1195_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(v_m_1193_, v_a_1194_);
    crate::leanh::lean_dec_ref(v_m_1193_);
    return v_res_1195_;
}
pub unsafe fn l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0(
    mut v_aig_1199_: *mut crate::leanh::LeanObject,
    mut v_input_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1205_: u8 = 0;
    let mut v_decls_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1210_: u8 = 0;
    let mut v_gate_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1212_: u8 = 0;
    let mut v_gate_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1214_: u8 = 0;
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1228_: u8 = 0;
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1233_: u8 = 0;
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsVal_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhsVal_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1246_: u8 = 0;
    let mut v_val_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: u8 = 0;
    let mut v_val_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: u8 = 0;
    let mut v_val_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: u8 = 0;
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: u8 = 0;
    let mut v_g_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1266_: u8 = 0;
    let mut v_unused_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1271_: u8 = 0;
    let mut v_val_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: u8 = 0;
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1281_: u8 = 0;
    let mut v_unused_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1284_: u8 = 0;
    let mut v_isSharedCheck_1285_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_1201_ = crate::leanh::lean_ctor_get(v_input_1200_, 0);
                v_rhs_1202_ = crate::leanh::lean_ctor_get(v_input_1200_, 1);
                v_isSharedCheck_1285_ = (!crate::leanh::lean_is_exclusive(v_input_1200_)) as u8;
                if v_isSharedCheck_1285_ == 0 {
                    v___x_1204_ = v_input_1200_;
                    v_isShared_1205_ = v_isSharedCheck_1285_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_1202_);
                    crate::leanh::lean_inc(v_lhs_1201_);
                    crate::leanh::lean_dec(v_input_1200_);
                    v___x_1204_ = crate::leanh::lean_box(0);
                    v_isShared_1205_ = v_isSharedCheck_1285_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_decls_1206_ = crate::leanh::lean_ctor_get(v_aig_1199_, 0);
                v_cache_1207_ = crate::leanh::lean_ctor_get(v_aig_1199_, 1);
                v_isSharedCheck_1284_ = (!crate::leanh::lean_is_exclusive(v_aig_1199_)) as u8;
                if v_isSharedCheck_1284_ == 0 {
                    v___x_1209_ = v_aig_1199_;
                    v_isShared_1210_ = v_isSharedCheck_1284_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cache_1207_);
                    crate::leanh::lean_inc(v_decls_1206_);
                    crate::leanh::lean_dec(v_aig_1199_);
                    v___x_1209_ = crate::leanh::lean_box(0);
                    v_isShared_1210_ = v_isSharedCheck_1284_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_1211_ = crate::leanh::lean_ctor_get(v_lhs_1201_, 0);
                crate::leanh::lean_inc(v_gate_1211_);
                v_invert_1212_ = crate::leanh::lean_ctor_get_uint8(
                    v_lhs_1201_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_gate_1213_ = crate::leanh::lean_ctor_get(v_rhs_1202_, 0);
                v_invert_1214_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_1202_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_1215_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1216_ = lean_nat_mul(v_gate_1211_, v___x_1215_);
                v___x_1217_ = l_Bool_toNat(v_invert_1212_);
                v___x_1218_ = lean_nat_lor(v___x_1216_, v___x_1217_);
                crate::leanh::lean_dec(v___x_1217_);
                crate::leanh::lean_dec(v___x_1216_);
                v___x_1219_ = lean_nat_mul(v_gate_1213_, v___x_1215_);
                v___x_1220_ = l_Bool_toNat(v_invert_1214_);
                v___x_1221_ = lean_nat_lor(v___x_1219_, v___x_1220_);
                crate::leanh::lean_dec(v___x_1220_);
                crate::leanh::lean_dec(v___x_1219_);
                if v_isShared_1205_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1204_, 2);
                    crate::leanh::lean_ctor_set(v___x_1204_, 1, v___x_1221_);
                    crate::leanh::lean_ctor_set(v___x_1204_, 0, v___x_1218_);
                    v_decl_1223_ = v___x_1204_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1283_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1218_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___x_1221_);
                    v_decl_1223_ = v_reuseFailAlloc_1283_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v_decl_1223_);
                v___x_1224_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(v_cache_1207_, v_decl_1223_);
                if crate::leanh::lean_obj_tag(v___x_1224_) == 0 {
                    crate::leanh::lean_inc(v_gate_1213_);
                    crate::leanh::lean_inc_ref(v_cache_1207_);
                    crate::leanh::lean_inc_ref(v_decls_1206_);
                    if v_isShared_1210_ == 0 {
                        v___x_1226_ = v___x_1209_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1268_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_decls_1206_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_cache_1207_);
                        v___x_1226_ = v_reuseFailAlloc_1268_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_decl_1223_);
                    crate::leanh::lean_dec(v_gate_1211_);
                    crate::leanh::lean_dec_ref(v_lhs_1201_);
                    v_isSharedCheck_1281_ = (!crate::leanh::lean_is_exclusive(v_rhs_1202_)) as u8;
                    if v_isSharedCheck_1281_ == 0 {
                        v_unused_1282_ = crate::leanh::lean_ctor_get(v_rhs_1202_, 0);
                        crate::leanh::lean_dec(v_unused_1282_);
                        v___x_1270_ = v_rhs_1202_;
                        v_isShared_1271_ = v_isSharedCheck_1281_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_rhs_1202_);
                        v___x_1270_ = crate::leanh::lean_box(0);
                        v_isShared_1271_ = v_isSharedCheck_1281_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                v_lhsVal_1242_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(v___x_1226_, v_lhs_1201_);
                crate::leanh::lean_dec_ref(v_lhs_1201_);
                v_rhsVal_1243_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(v___x_1226_, v_rhs_1202_);
                v_isSharedCheck_1266_ = (!crate::leanh::lean_is_exclusive(v_rhs_1202_)) as u8;
                if v_isSharedCheck_1266_ == 0 {
                    v_unused_1267_ = crate::leanh::lean_ctor_get(v_rhs_1202_, 0);
                    crate::leanh::lean_dec(v_unused_1267_);
                    v___x_1245_ = v_rhs_1202_;
                    v_isShared_1246_ = v_isSharedCheck_1266_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_rhs_1202_);
                    v___x_1245_ = crate::leanh::lean_box(0);
                    v_isShared_1246_ = v_isSharedCheck_1266_;
                    state = 9;
                    continue;
                }
            }
            5 => {
                v___x_1229_ = crate::leanh::lean_unsigned_to_nat(0);
                v_ref_1230_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v_ref_1230_, 0, v___x_1229_);
                crate::leanh::lean_ctor_set_uint8(
                    v_ref_1230_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___y_1228_,
                );
                v___x_1231_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1231_, 0, v___x_1226_);
                crate::leanh::lean_ctor_set(v___x_1231_, 1, v_ref_1230_);
                return v___x_1231_;
            }
            6 => {
                if v___y_1233_ == 0 {
                    crate::leanh::lean_dec(v_gate_1211_);
                    v___y_1228_ = v___y_1233_;
                    state = 5;
                    continue;
                } else {
                    v___x_1234_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1234_, 0, v_gate_1211_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1234_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_1212_,
                    );
                    v___x_1235_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1235_, 0, v___x_1226_);
                    crate::leanh::lean_ctor_set(v___x_1235_, 1, v___x_1234_);
                    return v___x_1235_;
                }
            }
            7 => {
                v___x_1237_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1237_, 0, v_gate_1213_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1237_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_1214_,
                );
                v___x_1238_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1238_, 0, v___x_1226_);
                crate::leanh::lean_ctor_set(v___x_1238_, 1, v___x_1237_);
                return v___x_1238_;
            }
            8 => {
                v_ref_1240_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0___closed__0;
                v___x_1241_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1241_, 0, v___x_1226_);
                crate::leanh::lean_ctor_set(v___x_1241_, 1, v_ref_1240_);
                return v___x_1241_;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_lhsVal_1242_) == 1 {
                    crate::leanh::lean_del_object(v___x_1245_);
                    crate::leanh::lean_dec_ref(v_decl_1223_);
                    crate::leanh::lean_dec(v_gate_1211_);
                    crate::leanh::lean_dec_ref(v_cache_1207_);
                    crate::leanh::lean_dec_ref(v_decls_1206_);
                    v_val_1247_ = crate::leanh::lean_ctor_get(v_lhsVal_1242_, 0);
                    crate::leanh::lean_inc(v_val_1247_);
                    crate::leanh::lean_dec_ref_known(v_lhsVal_1242_, 1);
                    v___x_1248_ = (crate::leanh::lean_unbox(v_val_1247_) as u8);
                    crate::leanh::lean_dec(v_val_1247_);
                    if v___x_1248_ == 0 {
                        crate::leanh::lean_dec(v_rhsVal_1243_);
                        crate::leanh::lean_dec(v_gate_1213_);
                        state = 8;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v_rhsVal_1243_) == 1 {
                            v_val_1249_ = crate::leanh::lean_ctor_get(v_rhsVal_1243_, 0);
                            crate::leanh::lean_inc(v_val_1249_);
                            crate::leanh::lean_dec_ref_known(v_rhsVal_1243_, 1);
                            v___x_1250_ = (crate::leanh::lean_unbox(v_val_1249_) as u8);
                            crate::leanh::lean_dec(v_val_1249_);
                            if v___x_1250_ == 0 {
                                crate::leanh::lean_dec(v_gate_1213_);
                                state = 8;
                                continue;
                            } else {
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_rhsVal_1243_);
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_lhsVal_1242_);
                    if crate::leanh::lean_obj_tag(v_rhsVal_1243_) == 1 {
                        crate::leanh::lean_dec_ref(v_decl_1223_);
                        crate::leanh::lean_dec(v_gate_1213_);
                        crate::leanh::lean_dec_ref(v_cache_1207_);
                        crate::leanh::lean_dec_ref(v_decls_1206_);
                        v_val_1251_ = crate::leanh::lean_ctor_get(v_rhsVal_1243_, 0);
                        crate::leanh::lean_inc(v_val_1251_);
                        crate::leanh::lean_dec_ref_known(v_rhsVal_1243_, 1);
                        v___x_1252_ = (crate::leanh::lean_unbox(v_val_1251_) as u8);
                        crate::leanh::lean_dec(v_val_1251_);
                        if v___x_1252_ == 0 {
                            crate::leanh::lean_del_object(v___x_1245_);
                            crate::leanh::lean_dec(v_gate_1211_);
                            state = 8;
                            continue;
                        } else {
                            if v_isShared_1246_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1245_, 0, v_gate_1211_);
                                v___x_1254_ = v___x_1245_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_1256_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1256_,
                                    0,
                                    v_gate_1211_,
                                );
                                v___x_1254_ = v_reuseFailAlloc_1256_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_rhsVal_1243_);
                        v___x_1257_ = lean_nat_dec_eq(v_gate_1211_, v_gate_1213_);
                        crate::leanh::lean_dec(v_gate_1213_);
                        if v___x_1257_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1226_);
                            crate::leanh::lean_dec(v_gate_1211_);
                            v_g_1258_ = lean_array_get_size(v_decls_1206_);
                            crate::leanh::lean_inc_ref(v_decl_1223_);
                            v_cache_1259_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(v_cache_1207_, v_decl_1223_, v_g_1258_);
                            v_decls_1260_ = lean_array_push(v_decls_1206_, v_decl_1223_);
                            v___x_1261_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1261_, 0, v_decls_1260_);
                            crate::leanh::lean_ctor_set(v___x_1261_, 1, v_cache_1259_);
                            if v_isShared_1246_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1245_, 0, v_g_1258_);
                                v___x_1263_ = v___x_1245_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_1265_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_g_1258_);
                                v___x_1263_ = v_reuseFailAlloc_1265_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1245_);
                            crate::leanh::lean_dec_ref(v_decl_1223_);
                            crate::leanh::lean_dec_ref(v_cache_1207_);
                            crate::leanh::lean_dec_ref(v_decls_1206_);
                            if v_invert_1212_ == 0 {
                                if v_invert_1214_ == 0 {
                                    v___y_1233_ = v___x_1257_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_gate_1211_);
                                    v___y_1228_ = v_invert_1212_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v___y_1233_ = v_invert_1214_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            10 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1254_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_1212_,
                );
                v___x_1255_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1255_, 0, v___x_1226_);
                crate::leanh::lean_ctor_set(v___x_1255_, 1, v___x_1254_);
                return v___x_1255_;
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1263_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1257_,
                );
                v___x_1264_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1264_, 0, v___x_1261_);
                crate::leanh::lean_ctor_set(v___x_1264_, 1, v___x_1263_);
                return v___x_1264_;
            }
            12 => {
                v_val_1272_ = crate::leanh::lean_ctor_get(v___x_1224_, 0);
                crate::leanh::lean_inc(v_val_1272_);
                crate::leanh::lean_dec_ref_known(v___x_1224_, 1);
                if v_isShared_1210_ == 0 {
                    v___x_1274_ = v___x_1209_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1280_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_decls_1206_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_cache_1207_);
                    v___x_1274_ = v_reuseFailAlloc_1280_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_1275_ = 0;
                if v_isShared_1271_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1270_, 0, v_val_1272_);
                    v___x_1277_ = v___x_1270_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1279_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_val_1272_);
                    v___x_1277_ = v_reuseFailAlloc_1279_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1277_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1275_,
                );
                v___x_1278_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1278_, 0, v___x_1274_);
                crate::leanh::lean_ctor_set(v___x_1278_, 1, v___x_1277_);
                return v___x_1278_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(
    mut v_aig_1286_: *mut crate::leanh::LeanObject,
    mut v_input_1287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1292_: u8 = 0;
    let mut v_gate_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: u8 = 0;
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1304_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_1288_ = crate::leanh::lean_ctor_get(v_input_1287_, 0);
                v_rhs_1289_ = crate::leanh::lean_ctor_get(v_input_1287_, 1);
                v_isSharedCheck_1304_ = (!crate::leanh::lean_is_exclusive(v_input_1287_)) as u8;
                if v_isSharedCheck_1304_ == 0 {
                    v___x_1291_ = v_input_1287_;
                    v_isShared_1292_ = v_isSharedCheck_1304_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_1289_);
                    crate::leanh::lean_inc(v_lhs_1288_);
                    crate::leanh::lean_dec(v_input_1287_);
                    v___x_1291_ = crate::leanh::lean_box(0);
                    v_isShared_1292_ = v_isSharedCheck_1304_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_1293_ = crate::leanh::lean_ctor_get(v_lhs_1288_, 0);
                v_gate_1294_ = crate::leanh::lean_ctor_get(v_rhs_1289_, 0);
                v___x_1295_ = lean_nat_dec_lt(v_gate_1293_, v_gate_1294_);
                if v___x_1295_ == 0 {
                    if v_isShared_1292_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1291_, 1, v_lhs_1288_);
                        crate::leanh::lean_ctor_set(v___x_1291_, 0, v_rhs_1289_);
                        v___x_1297_ = v___x_1291_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1299_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_rhs_1289_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_lhs_1288_);
                        v___x_1297_ = v_reuseFailAlloc_1299_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1292_ == 0 {
                        v___x_1301_ = v___x_1291_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1303_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_lhs_1288_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_rhs_1289_);
                        v___x_1301_ = v_reuseFailAlloc_1303_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1298_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0(v_aig_1286_, v___x_1297_);
                return v___x_1298_;
            }
            3 => {
                v___x_1302_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0(v_aig_1286_, v___x_1301_);
                return v___x_1302_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__2(
    mut v_aig_1305_: *mut crate::leanh::LeanObject,
    mut v_input_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1317_: u8 = 0;
    let mut v_gate_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1321_: u8 = 0;
    let mut v___x_1322_: u8 = 0;
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1326_: u8 = 0;
    let mut v_gate_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1330_: u8 = 0;
    let mut v___x_1331_: u8 = 0;
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1335_: u8 = 0;
    let mut v___y_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1338_: u8 = 0;
    let mut v___y_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1345_: u8 = 0;
    let mut v_aig_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1351_: u8 = 0;
    let mut v___x_1352_: u8 = 0;
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1356_: u8 = 0;
    let mut v_aig_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1362_: u8 = 0;
    let mut v___x_1363_: u8 = 0;
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1367_: u8 = 0;
    let mut v_lhs_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1372_: u8 = 0;
    let mut v_gate_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1374_: u8 = 0;
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1377_: u8 = 0;
    let mut v_gate_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1379_: u8 = 0;
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1382_: u8 = 0;
    let mut v___y_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: u8 = 0;
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: u8 = 0;
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: u8 = 0;
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: u8 = 0;
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1411_: u8 = 0;
    let mut v_isSharedCheck_1412_: u8 = 0;
    let mut v_isSharedCheck_1413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_1368_ = crate::leanh::lean_ctor_get(v_input_1306_, 0);
                v_rhs_1369_ = crate::leanh::lean_ctor_get(v_input_1306_, 1);
                v_isSharedCheck_1413_ = (!crate::leanh::lean_is_exclusive(v_input_1306_)) as u8;
                if v_isSharedCheck_1413_ == 0 {
                    v___x_1371_ = v_input_1306_;
                    v_isShared_1372_ = v_isSharedCheck_1413_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_1369_);
                    crate::leanh::lean_inc(v_lhs_1368_);
                    crate::leanh::lean_dec(v_input_1306_);
                    v___x_1371_ = crate::leanh::lean_box(0);
                    v_isShared_1372_ = v_isSharedCheck_1413_;
                    state = 12;
                    continue;
                }
            }
            1 => {
                v___x_1311_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1311_, 0, v___y_1308_);
                crate::leanh::lean_ctor_set(v___x_1311_, 1, v___y_1310_);
                v___x_1312_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v___y_1309_, v___x_1311_);
                return v___x_1312_;
            }
            2 => {
                v_invert_1317_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1314_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1317_ == 0 {
                    v_gate_1318_ = crate::leanh::lean_ctor_get(v___y_1314_, 0);
                    v_isSharedCheck_1326_ = (!crate::leanh::lean_is_exclusive(v___y_1314_)) as u8;
                    if v_isSharedCheck_1326_ == 0 {
                        v___x_1320_ = v___y_1314_;
                        v_isShared_1321_ = v_isSharedCheck_1326_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1318_);
                        crate::leanh::lean_dec(v___y_1314_);
                        v___x_1320_ = crate::leanh::lean_box(0);
                        v_isShared_1321_ = v_isSharedCheck_1326_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_gate_1327_ = crate::leanh::lean_ctor_get(v___y_1314_, 0);
                    v_isSharedCheck_1335_ = (!crate::leanh::lean_is_exclusive(v___y_1314_)) as u8;
                    if v_isSharedCheck_1335_ == 0 {
                        v___x_1329_ = v___y_1314_;
                        v_isShared_1330_ = v_isSharedCheck_1335_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1327_);
                        crate::leanh::lean_dec(v___y_1314_);
                        v___x_1329_ = crate::leanh::lean_box(0);
                        v_isShared_1330_ = v_isSharedCheck_1335_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1322_ = 1;
                if v_isShared_1321_ == 0 {
                    v___x_1324_ = v___x_1320_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1325_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_gate_1318_);
                    v___x_1324_ = v_reuseFailAlloc_1325_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1324_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1322_,
                );
                v___y_1308_ = v___y_1316_;
                v___y_1309_ = v___y_1315_;
                v___y_1310_ = v___x_1324_;
                state = 1;
                continue;
            }
            5 => {
                v___x_1331_ = 0;
                if v_isShared_1330_ == 0 {
                    v___x_1333_ = v___x_1329_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1334_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_gate_1327_);
                    v___x_1333_ = v_reuseFailAlloc_1334_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1333_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1331_,
                );
                v___y_1308_ = v___y_1316_;
                v___y_1309_ = v___y_1315_;
                v___y_1310_ = v___x_1333_;
                state = 1;
                continue;
            }
            7 => {
                v___x_1342_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1342_, 0, v___y_1337_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1342_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___y_1338_,
                );
                v___x_1343_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1343_, 0, v___y_1341_);
                crate::leanh::lean_ctor_set(v___x_1343_, 1, v___x_1342_);
                v_res_1344_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v___y_1339_, v___x_1343_);
                v_invert_1345_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1340_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1345_ == 0 {
                    v_aig_1346_ = crate::leanh::lean_ctor_get(v_res_1344_, 0);
                    crate::leanh::lean_inc_ref(v_aig_1346_);
                    v_ref_1347_ = crate::leanh::lean_ctor_get(v_res_1344_, 1);
                    crate::leanh::lean_inc_ref(v_ref_1347_);
                    crate::leanh::lean_dec_ref(v_res_1344_);
                    v_gate_1348_ = crate::leanh::lean_ctor_get(v___y_1340_, 0);
                    v_isSharedCheck_1356_ = (!crate::leanh::lean_is_exclusive(v___y_1340_)) as u8;
                    if v_isSharedCheck_1356_ == 0 {
                        v___x_1350_ = v___y_1340_;
                        v_isShared_1351_ = v_isSharedCheck_1356_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1348_);
                        crate::leanh::lean_dec(v___y_1340_);
                        v___x_1350_ = crate::leanh::lean_box(0);
                        v_isShared_1351_ = v_isSharedCheck_1356_;
                        state = 8;
                        continue;
                    }
                } else {
                    v_aig_1357_ = crate::leanh::lean_ctor_get(v_res_1344_, 0);
                    crate::leanh::lean_inc_ref(v_aig_1357_);
                    v_ref_1358_ = crate::leanh::lean_ctor_get(v_res_1344_, 1);
                    crate::leanh::lean_inc_ref(v_ref_1358_);
                    crate::leanh::lean_dec_ref(v_res_1344_);
                    v_gate_1359_ = crate::leanh::lean_ctor_get(v___y_1340_, 0);
                    v_isSharedCheck_1367_ = (!crate::leanh::lean_is_exclusive(v___y_1340_)) as u8;
                    if v_isSharedCheck_1367_ == 0 {
                        v___x_1361_ = v___y_1340_;
                        v_isShared_1362_ = v_isSharedCheck_1367_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1359_);
                        crate::leanh::lean_dec(v___y_1340_);
                        v___x_1361_ = crate::leanh::lean_box(0);
                        v_isShared_1362_ = v_isSharedCheck_1367_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_1352_ = 1;
                if v_isShared_1351_ == 0 {
                    v___x_1354_ = v___x_1350_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1355_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_gate_1348_);
                    v___x_1354_ = v_reuseFailAlloc_1355_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1354_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1352_,
                );
                v___y_1314_ = v_ref_1347_;
                v___y_1315_ = v_aig_1346_;
                v___y_1316_ = v___x_1354_;
                state = 2;
                continue;
            }
            10 => {
                v___x_1363_ = 0;
                if v_isShared_1362_ == 0 {
                    v___x_1365_ = v___x_1361_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1366_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_gate_1359_);
                    v___x_1365_ = v_reuseFailAlloc_1366_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1365_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1363_,
                );
                v___y_1314_ = v_ref_1358_;
                v___y_1315_ = v_aig_1357_;
                v___y_1316_ = v___x_1365_;
                state = 2;
                continue;
            }
            12 => {
                v_gate_1373_ = crate::leanh::lean_ctor_get(v_lhs_1368_, 0);
                v_invert_1374_ = crate::leanh::lean_ctor_get_uint8(
                    v_lhs_1368_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1412_ = (!crate::leanh::lean_is_exclusive(v_lhs_1368_)) as u8;
                if v_isSharedCheck_1412_ == 0 {
                    v___x_1376_ = v_lhs_1368_;
                    v_isShared_1377_ = v_isSharedCheck_1412_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_1373_);
                    crate::leanh::lean_dec(v_lhs_1368_);
                    v___x_1376_ = crate::leanh::lean_box(0);
                    v_isShared_1377_ = v_isSharedCheck_1412_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_gate_1378_ = crate::leanh::lean_ctor_get(v_rhs_1369_, 0);
                v_invert_1379_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_1369_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1411_ = (!crate::leanh::lean_is_exclusive(v_rhs_1369_)) as u8;
                if v_isSharedCheck_1411_ == 0 {
                    v___x_1381_ = v_rhs_1369_;
                    v_isShared_1382_ = v_isSharedCheck_1411_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_1378_);
                    crate::leanh::lean_dec(v_rhs_1369_);
                    v___x_1381_ = crate::leanh::lean_box(0);
                    v_isShared_1382_ = v_isSharedCheck_1411_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                crate::leanh::lean_inc(v_gate_1373_);
                if v_isShared_1377_ == 0 {
                    v___x_1399_ = v___x_1376_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1410_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_gate_1373_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1410_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_1374_,
                    );
                    v___x_1399_ = v_reuseFailAlloc_1410_;
                    state = 18;
                    continue;
                }
            }
            15 => {
                v_res_1385_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_1305_, v___y_1384_);
                if v_invert_1374_ == 0 {
                    v_aig_1386_ = crate::leanh::lean_ctor_get(v_res_1385_, 0);
                    crate::leanh::lean_inc_ref(v_aig_1386_);
                    v_ref_1387_ = crate::leanh::lean_ctor_get(v_res_1385_, 1);
                    crate::leanh::lean_inc_ref(v_ref_1387_);
                    crate::leanh::lean_dec_ref(v_res_1385_);
                    v___x_1388_ = 1;
                    if v_isShared_1382_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1381_, 0, v_gate_1373_);
                        v___x_1390_ = v___x_1381_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_1391_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_gate_1373_);
                        v___x_1390_ = v_reuseFailAlloc_1391_;
                        state = 16;
                        continue;
                    }
                } else {
                    v_aig_1392_ = crate::leanh::lean_ctor_get(v_res_1385_, 0);
                    crate::leanh::lean_inc_ref(v_aig_1392_);
                    v_ref_1393_ = crate::leanh::lean_ctor_get(v_res_1385_, 1);
                    crate::leanh::lean_inc_ref(v_ref_1393_);
                    crate::leanh::lean_dec_ref(v_res_1385_);
                    v___x_1394_ = 0;
                    if v_isShared_1382_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1381_, 0, v_gate_1373_);
                        v___x_1396_ = v___x_1381_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_1397_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_gate_1373_);
                        v___x_1396_ = v_reuseFailAlloc_1397_;
                        state = 17;
                        continue;
                    }
                }
            }
            16 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1390_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1388_,
                );
                v___y_1337_ = v_gate_1378_;
                v___y_1338_ = v_invert_1379_;
                v___y_1339_ = v_aig_1386_;
                v___y_1340_ = v_ref_1387_;
                v___y_1341_ = v___x_1390_;
                state = 7;
                continue;
            }
            17 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1396_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1394_,
                );
                v___y_1337_ = v_gate_1378_;
                v___y_1338_ = v_invert_1379_;
                v___y_1339_ = v_aig_1392_;
                v___y_1340_ = v_ref_1393_;
                v___y_1341_ = v___x_1396_;
                state = 7;
                continue;
            }
            18 => {
                if v_invert_1379_ == 0 {
                    v___x_1400_ = 1;
                    crate::leanh::lean_inc(v_gate_1378_);
                    v___x_1401_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1401_, 0, v_gate_1378_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1401_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1400_,
                    );
                    if v_isShared_1372_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1371_, 1, v___x_1401_);
                        crate::leanh::lean_ctor_set(v___x_1371_, 0, v___x_1399_);
                        v___x_1403_ = v___x_1371_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_1404_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1399_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1404_, 1, v___x_1401_);
                        v___x_1403_ = v_reuseFailAlloc_1404_;
                        state = 19;
                        continue;
                    }
                } else {
                    v___x_1405_ = 0;
                    crate::leanh::lean_inc(v_gate_1378_);
                    v___x_1406_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1406_, 0, v_gate_1378_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1406_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1405_,
                    );
                    if v_isShared_1372_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1371_, 1, v___x_1406_);
                        crate::leanh::lean_ctor_set(v___x_1371_, 0, v___x_1399_);
                        v___x_1408_ = v___x_1371_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_1409_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1399_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1409_, 1, v___x_1406_);
                        v___x_1408_ = v_reuseFailAlloc_1409_;
                        state = 20;
                        continue;
                    }
                }
            }
            19 => {
                v___y_1384_ = v___x_1403_;
                state = 15;
                continue;
            }
            20 => {
                v___y_1384_ = v___x_1408_;
                state = 15;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(
    mut v_aig_1414_: *mut crate::leanh::LeanObject,
    mut v_input_1415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1420_: u8 = 0;
    let mut v_aig_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1424_: u8 = 0;
    let mut v_gate_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1428_: u8 = 0;
    let mut v___x_1429_: u8 = 0;
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1436_: u8 = 0;
    let mut v_isSharedCheck_1437_: u8 = 0;
    let mut v_unused_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1442_: u8 = 0;
    let mut v_gate_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1446_: u8 = 0;
    let mut v___x_1447_: u8 = 0;
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1454_: u8 = 0;
    let mut v_isSharedCheck_1455_: u8 = 0;
    let mut v_unused_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1461_: u8 = 0;
    let mut v___y_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1464_: u8 = 0;
    let mut v_gate_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1468_: u8 = 0;
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1476_: u8 = 0;
    let mut v_gate_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1480_: u8 = 0;
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut v_invert_1489_: u8 = 0;
    let mut v_gate_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1493_: u8 = 0;
    let mut v___x_1494_: u8 = 0;
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1498_: u8 = 0;
    let mut v_gate_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1502_: u8 = 0;
    let mut v___x_1503_: u8 = 0;
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1507_: u8 = 0;
    let mut v_isSharedCheck_1508_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_1457_ = crate::leanh::lean_ctor_get(v_input_1415_, 0);
                v_rhs_1458_ = crate::leanh::lean_ctor_get(v_input_1415_, 1);
                v_isSharedCheck_1508_ = (!crate::leanh::lean_is_exclusive(v_input_1415_)) as u8;
                if v_isSharedCheck_1508_ == 0 {
                    v___x_1460_ = v_input_1415_;
                    v_isShared_1461_ = v_isSharedCheck_1508_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_1458_);
                    crate::leanh::lean_inc(v_lhs_1457_);
                    crate::leanh::lean_dec(v_input_1415_);
                    v___x_1460_ = crate::leanh::lean_box(0);
                    v_isShared_1461_ = v_isSharedCheck_1508_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v_res_1418_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_1414_, v___y_1417_);
                v_ref_1419_ = crate::leanh::lean_ctor_get(v_res_1418_, 1);
                crate::leanh::lean_inc_ref(v_ref_1419_);
                v_invert_1420_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_1419_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1420_ == 0 {
                    v_aig_1421_ = crate::leanh::lean_ctor_get(v_res_1418_, 0);
                    v_isSharedCheck_1437_ = (!crate::leanh::lean_is_exclusive(v_res_1418_)) as u8;
                    if v_isSharedCheck_1437_ == 0 {
                        v_unused_1438_ = crate::leanh::lean_ctor_get(v_res_1418_, 1);
                        crate::leanh::lean_dec(v_unused_1438_);
                        v___x_1423_ = v_res_1418_;
                        v_isShared_1424_ = v_isSharedCheck_1437_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_aig_1421_);
                        crate::leanh::lean_dec(v_res_1418_);
                        v___x_1423_ = crate::leanh::lean_box(0);
                        v_isShared_1424_ = v_isSharedCheck_1437_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_aig_1439_ = crate::leanh::lean_ctor_get(v_res_1418_, 0);
                    v_isSharedCheck_1455_ = (!crate::leanh::lean_is_exclusive(v_res_1418_)) as u8;
                    if v_isSharedCheck_1455_ == 0 {
                        v_unused_1456_ = crate::leanh::lean_ctor_get(v_res_1418_, 1);
                        crate::leanh::lean_dec(v_unused_1456_);
                        v___x_1441_ = v_res_1418_;
                        v_isShared_1442_ = v_isSharedCheck_1455_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_aig_1439_);
                        crate::leanh::lean_dec(v_res_1418_);
                        v___x_1441_ = crate::leanh::lean_box(0);
                        v_isShared_1442_ = v_isSharedCheck_1455_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_gate_1425_ = crate::leanh::lean_ctor_get(v_ref_1419_, 0);
                v_isSharedCheck_1436_ = (!crate::leanh::lean_is_exclusive(v_ref_1419_)) as u8;
                if v_isSharedCheck_1436_ == 0 {
                    v___x_1427_ = v_ref_1419_;
                    v_isShared_1428_ = v_isSharedCheck_1436_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_1425_);
                    crate::leanh::lean_dec(v_ref_1419_);
                    v___x_1427_ = crate::leanh::lean_box(0);
                    v_isShared_1428_ = v_isSharedCheck_1436_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1429_ = 1;
                if v_isShared_1428_ == 0 {
                    v___x_1431_ = v___x_1427_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1435_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_gate_1425_);
                    v___x_1431_ = v_reuseFailAlloc_1435_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1431_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1429_,
                );
                if v_isShared_1424_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1423_, 1, v___x_1431_);
                    v___x_1433_ = v___x_1423_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1434_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_aig_1421_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1434_, 1, v___x_1431_);
                    v___x_1433_ = v_reuseFailAlloc_1434_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1433_;
            }
            6 => {
                v_gate_1443_ = crate::leanh::lean_ctor_get(v_ref_1419_, 0);
                v_isSharedCheck_1454_ = (!crate::leanh::lean_is_exclusive(v_ref_1419_)) as u8;
                if v_isSharedCheck_1454_ == 0 {
                    v___x_1445_ = v_ref_1419_;
                    v_isShared_1446_ = v_isSharedCheck_1454_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_1443_);
                    crate::leanh::lean_dec(v_ref_1419_);
                    v___x_1445_ = crate::leanh::lean_box(0);
                    v_isShared_1446_ = v_isSharedCheck_1454_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1447_ = 0;
                if v_isShared_1446_ == 0 {
                    v___x_1449_ = v___x_1445_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1453_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_gate_1443_);
                    v___x_1449_ = v_reuseFailAlloc_1453_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1449_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1447_,
                );
                if v_isShared_1442_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1441_, 1, v___x_1449_);
                    v___x_1451_ = v___x_1441_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1452_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_aig_1439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 1, v___x_1449_);
                    v___x_1451_ = v_reuseFailAlloc_1452_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1451_;
            }
            10 => {
                v_invert_1489_ = crate::leanh::lean_ctor_get_uint8(
                    v_lhs_1457_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1489_ == 0 {
                    v_gate_1490_ = crate::leanh::lean_ctor_get(v_lhs_1457_, 0);
                    v_isSharedCheck_1498_ = (!crate::leanh::lean_is_exclusive(v_lhs_1457_)) as u8;
                    if v_isSharedCheck_1498_ == 0 {
                        v___x_1492_ = v_lhs_1457_;
                        v_isShared_1493_ = v_isSharedCheck_1498_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1490_);
                        crate::leanh::lean_dec(v_lhs_1457_);
                        v___x_1492_ = crate::leanh::lean_box(0);
                        v_isShared_1493_ = v_isSharedCheck_1498_;
                        state = 18;
                        continue;
                    }
                } else {
                    v_gate_1499_ = crate::leanh::lean_ctor_get(v_lhs_1457_, 0);
                    v_isSharedCheck_1507_ = (!crate::leanh::lean_is_exclusive(v_lhs_1457_)) as u8;
                    if v_isSharedCheck_1507_ == 0 {
                        v___x_1501_ = v_lhs_1457_;
                        v_isShared_1502_ = v_isSharedCheck_1507_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1499_);
                        crate::leanh::lean_dec(v_lhs_1457_);
                        v___x_1501_ = crate::leanh::lean_box(0);
                        v_isShared_1502_ = v_isSharedCheck_1507_;
                        state = 20;
                        continue;
                    }
                }
            }
            11 => {
                v_invert_1464_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_1458_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1464_ == 0 {
                    v_gate_1465_ = crate::leanh::lean_ctor_get(v_rhs_1458_, 0);
                    v_isSharedCheck_1476_ = (!crate::leanh::lean_is_exclusive(v_rhs_1458_)) as u8;
                    if v_isSharedCheck_1476_ == 0 {
                        v___x_1467_ = v_rhs_1458_;
                        v_isShared_1468_ = v_isSharedCheck_1476_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1465_);
                        crate::leanh::lean_dec(v_rhs_1458_);
                        v___x_1467_ = crate::leanh::lean_box(0);
                        v_isShared_1468_ = v_isSharedCheck_1476_;
                        state = 12;
                        continue;
                    }
                } else {
                    v_gate_1477_ = crate::leanh::lean_ctor_get(v_rhs_1458_, 0);
                    v_isSharedCheck_1488_ = (!crate::leanh::lean_is_exclusive(v_rhs_1458_)) as u8;
                    if v_isSharedCheck_1488_ == 0 {
                        v___x_1479_ = v_rhs_1458_;
                        v_isShared_1480_ = v_isSharedCheck_1488_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1477_);
                        crate::leanh::lean_dec(v_rhs_1458_);
                        v___x_1479_ = crate::leanh::lean_box(0);
                        v_isShared_1480_ = v_isSharedCheck_1488_;
                        state = 15;
                        continue;
                    }
                }
            }
            12 => {
                v___x_1469_ = 1;
                if v_isShared_1468_ == 0 {
                    v___x_1471_ = v___x_1467_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1475_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_gate_1465_);
                    v___x_1471_ = v_reuseFailAlloc_1475_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1471_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1469_,
                );
                if v_isShared_1461_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1460_, 1, v___x_1471_);
                    crate::leanh::lean_ctor_set(v___x_1460_, 0, v___y_1463_);
                    v___x_1473_ = v___x_1460_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1474_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___y_1463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1474_, 1, v___x_1471_);
                    v___x_1473_ = v_reuseFailAlloc_1474_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___y_1417_ = v___x_1473_;
                state = 1;
                continue;
            }
            15 => {
                v___x_1481_ = 0;
                if v_isShared_1480_ == 0 {
                    v___x_1483_ = v___x_1479_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1487_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_gate_1477_);
                    v___x_1483_ = v_reuseFailAlloc_1487_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1483_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1481_,
                );
                if v_isShared_1461_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1460_, 1, v___x_1483_);
                    crate::leanh::lean_ctor_set(v___x_1460_, 0, v___y_1463_);
                    v___x_1485_ = v___x_1460_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1486_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___y_1463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___x_1483_);
                    v___x_1485_ = v_reuseFailAlloc_1486_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___y_1417_ = v___x_1485_;
                state = 1;
                continue;
            }
            18 => {
                v___x_1494_ = 1;
                if v_isShared_1493_ == 0 {
                    v___x_1496_ = v___x_1492_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1497_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_gate_1490_);
                    v___x_1496_ = v_reuseFailAlloc_1497_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1496_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1494_,
                );
                v___y_1463_ = v___x_1496_;
                state = 11;
                continue;
            }
            20 => {
                v___x_1503_ = 0;
                if v_isShared_1502_ == 0 {
                    v___x_1505_ = v___x_1501_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1506_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_gate_1499_);
                    v___x_1505_ = v_reuseFailAlloc_1506_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1505_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1503_,
                );
                v___y_1463_ = v___x_1505_;
                state = 11;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__4(
    mut v_aig_1509_: *mut crate::leanh::LeanObject,
    mut v_input_1510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_discr_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1520_: u8 = 0;
    let mut v_gate_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1522_: u8 = 0;
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1525_: u8 = 0;
    let mut v_gate_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1527_: u8 = 0;
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1530_: u8 = 0;
    let mut v_aig_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1543_: u8 = 0;
    let mut v_gate_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1545_: u8 = 0;
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1548_: u8 = 0;
    let mut v_lhsRef_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1556_: u8 = 0;
    let mut v_isSharedCheck_1557_: u8 = 0;
    let mut v_reuseFailAlloc_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: u8 = 0;
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: u8 = 0;
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1568_: u8 = 0;
    let mut v_isSharedCheck_1569_: u8 = 0;
    let mut v_isSharedCheck_1570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_discr_1511_ = crate::leanh::lean_ctor_get(v_input_1510_, 0);
                crate::leanh::lean_inc_ref_n(v_discr_1511_, 2);
                v_lhs_1512_ = crate::leanh::lean_ctor_get(v_input_1510_, 1);
                crate::leanh::lean_inc_ref(v_lhs_1512_);
                v_rhs_1513_ = crate::leanh::lean_ctor_get(v_input_1510_, 2);
                crate::leanh::lean_inc_ref(v_rhs_1513_);
                crate::leanh::lean_dec_ref(v_input_1510_);
                v___x_1514_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1514_, 0, v_discr_1511_);
                crate::leanh::lean_ctor_set(v___x_1514_, 1, v_lhs_1512_);
                v_res_1515_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_1509_, v___x_1514_);
                v_aig_1516_ = crate::leanh::lean_ctor_get(v_res_1515_, 0);
                v_ref_1517_ = crate::leanh::lean_ctor_get(v_res_1515_, 1);
                v_isSharedCheck_1570_ = (!crate::leanh::lean_is_exclusive(v_res_1515_)) as u8;
                if v_isSharedCheck_1570_ == 0 {
                    v___x_1519_ = v_res_1515_;
                    v_isShared_1520_ = v_isSharedCheck_1570_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_1517_);
                    crate::leanh::lean_inc(v_aig_1516_);
                    crate::leanh::lean_dec(v_res_1515_);
                    v___x_1519_ = crate::leanh::lean_box(0);
                    v_isShared_1520_ = v_isSharedCheck_1570_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_1521_ = crate::leanh::lean_ctor_get(v_discr_1511_, 0);
                v_invert_1522_ = crate::leanh::lean_ctor_get_uint8(
                    v_discr_1511_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1569_ = (!crate::leanh::lean_is_exclusive(v_discr_1511_)) as u8;
                if v_isSharedCheck_1569_ == 0 {
                    v___x_1524_ = v_discr_1511_;
                    v_isShared_1525_ = v_isSharedCheck_1569_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_1521_);
                    crate::leanh::lean_dec(v_discr_1511_);
                    v___x_1524_ = crate::leanh::lean_box(0);
                    v_isShared_1525_ = v_isSharedCheck_1569_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_1526_ = crate::leanh::lean_ctor_get(v_rhs_1513_, 0);
                v_invert_1527_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_1513_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1568_ = (!crate::leanh::lean_is_exclusive(v_rhs_1513_)) as u8;
                if v_isSharedCheck_1568_ == 0 {
                    v___x_1529_ = v_rhs_1513_;
                    v_isShared_1530_ = v_isSharedCheck_1568_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_1526_);
                    crate::leanh::lean_dec(v_rhs_1513_);
                    v___x_1529_ = crate::leanh::lean_box(0);
                    v_isShared_1530_ = v_isSharedCheck_1568_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_invert_1522_ == 0 {
                    v___x_1560_ = 1;
                    if v_isShared_1525_ == 0 {
                        v___x_1562_ = v___x_1524_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1563_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_gate_1521_);
                        v___x_1562_ = v_reuseFailAlloc_1563_;
                        state = 11;
                        continue;
                    }
                } else {
                    v___x_1564_ = 0;
                    if v_isShared_1525_ == 0 {
                        v___x_1566_ = v___x_1524_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1567_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_gate_1521_);
                        v___x_1566_ = v_reuseFailAlloc_1567_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_1530_ == 0 {
                    v___x_1535_ = v___x_1529_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1559_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_gate_1526_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1559_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_1527_,
                    );
                    v___x_1535_ = v_reuseFailAlloc_1559_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1520_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1519_, 1, v___x_1535_);
                    crate::leanh::lean_ctor_set(v___x_1519_, 0, v_ref_1533_);
                    v___x_1537_ = v___x_1519_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1558_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_ref_1533_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 1, v___x_1535_);
                    v___x_1537_ = v_reuseFailAlloc_1558_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_res_1538_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_1532_, v___x_1537_);
                v_aig_1539_ = crate::leanh::lean_ctor_get(v_res_1538_, 0);
                v_ref_1540_ = crate::leanh::lean_ctor_get(v_res_1538_, 1);
                v_isSharedCheck_1557_ = (!crate::leanh::lean_is_exclusive(v_res_1538_)) as u8;
                if v_isSharedCheck_1557_ == 0 {
                    v___x_1542_ = v_res_1538_;
                    v_isShared_1543_ = v_isSharedCheck_1557_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_1540_);
                    crate::leanh::lean_inc(v_aig_1539_);
                    crate::leanh::lean_dec(v_res_1538_);
                    v___x_1542_ = crate::leanh::lean_box(0);
                    v_isShared_1543_ = v_isSharedCheck_1557_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_gate_1544_ = crate::leanh::lean_ctor_get(v_ref_1517_, 0);
                v_invert_1545_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_1517_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1556_ = (!crate::leanh::lean_is_exclusive(v_ref_1517_)) as u8;
                if v_isSharedCheck_1556_ == 0 {
                    v___x_1547_ = v_ref_1517_;
                    v_isShared_1548_ = v_isSharedCheck_1556_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_1544_);
                    crate::leanh::lean_dec(v_ref_1517_);
                    v___x_1547_ = crate::leanh::lean_box(0);
                    v_isShared_1548_ = v_isSharedCheck_1556_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_1548_ == 0 {
                    v_lhsRef_1550_ = v___x_1547_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1555_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_gate_1544_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1555_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_1545_,
                    );
                    v_lhsRef_1550_ = v_reuseFailAlloc_1555_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1543_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1542_, 0, v_lhsRef_1550_);
                    v___x_1552_ = v___x_1542_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1554_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_lhsRef_1550_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_ref_1540_);
                    v___x_1552_ = v_reuseFailAlloc_1554_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_1553_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(v_aig_1539_, v___x_1552_);
                return v___x_1553_;
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1562_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1560_,
                );
                v_aig_1532_ = v_aig_1516_;
                v_ref_1533_ = v___x_1562_;
                state = 4;
                continue;
            }
            12 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1566_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1564_,
                );
                v_aig_1532_ = v_aig_1516_;
                v_ref_1533_ = v___x_1566_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__1(
    mut v_aig_1571_: *mut crate::leanh::LeanObject,
    mut v_input_1572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1583_: u8 = 0;
    let mut v_gate_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1587_: u8 = 0;
    let mut v___x_1588_: u8 = 0;
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1592_: u8 = 0;
    let mut v_gate_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1596_: u8 = 0;
    let mut v___x_1597_: u8 = 0;
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1601_: u8 = 0;
    let mut v_res_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1608_: u8 = 0;
    let mut v_aig_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1614_: u8 = 0;
    let mut v___x_1615_: u8 = 0;
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1619_: u8 = 0;
    let mut v_aig_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1625_: u8 = 0;
    let mut v___x_1626_: u8 = 0;
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1630_: u8 = 0;
    let mut v_lhs_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1635_: u8 = 0;
    let mut v_gate_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1637_: u8 = 0;
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1640_: u8 = 0;
    let mut v_gate_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1642_: u8 = 0;
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1645_: u8 = 0;
    let mut v___y_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: u8 = 0;
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: u8 = 0;
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: u8 = 0;
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1670_: u8 = 0;
    let mut v_isSharedCheck_1671_: u8 = 0;
    let mut v_isSharedCheck_1672_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_input_1572_);
                v_res_1602_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_1571_, v_input_1572_);
                v_aig_1603_ = crate::leanh::lean_ctor_get(v_res_1602_, 0);
                crate::leanh::lean_inc_ref(v_aig_1603_);
                v_ref_1604_ = crate::leanh::lean_ctor_get(v_res_1602_, 1);
                crate::leanh::lean_inc_ref(v_ref_1604_);
                crate::leanh::lean_dec_ref(v_res_1602_);
                v_lhs_1631_ = crate::leanh::lean_ctor_get(v_input_1572_, 0);
                v_rhs_1632_ = crate::leanh::lean_ctor_get(v_input_1572_, 1);
                v_isSharedCheck_1672_ = (!crate::leanh::lean_is_exclusive(v_input_1572_)) as u8;
                if v_isSharedCheck_1672_ == 0 {
                    v___x_1634_ = v_input_1572_;
                    v_isShared_1635_ = v_isSharedCheck_1672_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_1632_);
                    crate::leanh::lean_inc(v_lhs_1631_);
                    crate::leanh::lean_dec(v_input_1572_);
                    v___x_1634_ = crate::leanh::lean_box(0);
                    v_isShared_1635_ = v_isSharedCheck_1672_;
                    state = 12;
                    continue;
                }
            }
            1 => {
                v___x_1577_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1577_, 0, v___y_1574_);
                crate::leanh::lean_ctor_set(v___x_1577_, 1, v___y_1576_);
                v___x_1578_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v___y_1575_, v___x_1577_);
                return v___x_1578_;
            }
            2 => {
                v_invert_1583_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1580_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1583_ == 0 {
                    v_gate_1584_ = crate::leanh::lean_ctor_get(v___y_1580_, 0);
                    v_isSharedCheck_1592_ = (!crate::leanh::lean_is_exclusive(v___y_1580_)) as u8;
                    if v_isSharedCheck_1592_ == 0 {
                        v___x_1586_ = v___y_1580_;
                        v_isShared_1587_ = v_isSharedCheck_1592_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1584_);
                        crate::leanh::lean_dec(v___y_1580_);
                        v___x_1586_ = crate::leanh::lean_box(0);
                        v_isShared_1587_ = v_isSharedCheck_1592_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_gate_1593_ = crate::leanh::lean_ctor_get(v___y_1580_, 0);
                    v_isSharedCheck_1601_ = (!crate::leanh::lean_is_exclusive(v___y_1580_)) as u8;
                    if v_isSharedCheck_1601_ == 0 {
                        v___x_1595_ = v___y_1580_;
                        v_isShared_1596_ = v_isSharedCheck_1601_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1593_);
                        crate::leanh::lean_dec(v___y_1580_);
                        v___x_1595_ = crate::leanh::lean_box(0);
                        v_isShared_1596_ = v_isSharedCheck_1601_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1588_ = 1;
                if v_isShared_1587_ == 0 {
                    v___x_1590_ = v___x_1586_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1591_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_gate_1584_);
                    v___x_1590_ = v_reuseFailAlloc_1591_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1590_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1588_,
                );
                v___y_1574_ = v___y_1582_;
                v___y_1575_ = v___y_1581_;
                v___y_1576_ = v___x_1590_;
                state = 1;
                continue;
            }
            5 => {
                v___x_1597_ = 0;
                if v_isShared_1596_ == 0 {
                    v___x_1599_ = v___x_1595_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1600_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_gate_1593_);
                    v___x_1599_ = v_reuseFailAlloc_1600_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1599_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1597_,
                );
                v___y_1574_ = v___y_1582_;
                v___y_1575_ = v___y_1581_;
                v___y_1576_ = v___x_1599_;
                state = 1;
                continue;
            }
            7 => {
                v_res_1607_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_1603_, v___y_1606_);
                v_invert_1608_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_1604_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_1608_ == 0 {
                    v_aig_1609_ = crate::leanh::lean_ctor_get(v_res_1607_, 0);
                    crate::leanh::lean_inc_ref(v_aig_1609_);
                    v_ref_1610_ = crate::leanh::lean_ctor_get(v_res_1607_, 1);
                    crate::leanh::lean_inc_ref(v_ref_1610_);
                    crate::leanh::lean_dec_ref(v_res_1607_);
                    v_gate_1611_ = crate::leanh::lean_ctor_get(v_ref_1604_, 0);
                    v_isSharedCheck_1619_ = (!crate::leanh::lean_is_exclusive(v_ref_1604_)) as u8;
                    if v_isSharedCheck_1619_ == 0 {
                        v___x_1613_ = v_ref_1604_;
                        v_isShared_1614_ = v_isSharedCheck_1619_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1611_);
                        crate::leanh::lean_dec(v_ref_1604_);
                        v___x_1613_ = crate::leanh::lean_box(0);
                        v_isShared_1614_ = v_isSharedCheck_1619_;
                        state = 8;
                        continue;
                    }
                } else {
                    v_aig_1620_ = crate::leanh::lean_ctor_get(v_res_1607_, 0);
                    crate::leanh::lean_inc_ref(v_aig_1620_);
                    v_ref_1621_ = crate::leanh::lean_ctor_get(v_res_1607_, 1);
                    crate::leanh::lean_inc_ref(v_ref_1621_);
                    crate::leanh::lean_dec_ref(v_res_1607_);
                    v_gate_1622_ = crate::leanh::lean_ctor_get(v_ref_1604_, 0);
                    v_isSharedCheck_1630_ = (!crate::leanh::lean_is_exclusive(v_ref_1604_)) as u8;
                    if v_isSharedCheck_1630_ == 0 {
                        v___x_1624_ = v_ref_1604_;
                        v_isShared_1625_ = v_isSharedCheck_1630_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_gate_1622_);
                        crate::leanh::lean_dec(v_ref_1604_);
                        v___x_1624_ = crate::leanh::lean_box(0);
                        v_isShared_1625_ = v_isSharedCheck_1630_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_1615_ = 1;
                if v_isShared_1614_ == 0 {
                    v___x_1617_ = v___x_1613_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1618_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_gate_1611_);
                    v___x_1617_ = v_reuseFailAlloc_1618_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1617_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1615_,
                );
                v___y_1580_ = v_ref_1610_;
                v___y_1581_ = v_aig_1609_;
                v___y_1582_ = v___x_1617_;
                state = 2;
                continue;
            }
            10 => {
                v___x_1626_ = 0;
                if v_isShared_1625_ == 0 {
                    v___x_1628_ = v___x_1624_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1629_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_gate_1622_);
                    v___x_1628_ = v_reuseFailAlloc_1629_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1628_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1626_,
                );
                v___y_1580_ = v_ref_1621_;
                v___y_1581_ = v_aig_1620_;
                v___y_1582_ = v___x_1628_;
                state = 2;
                continue;
            }
            12 => {
                v_gate_1636_ = crate::leanh::lean_ctor_get(v_lhs_1631_, 0);
                v_invert_1637_ = crate::leanh::lean_ctor_get_uint8(
                    v_lhs_1631_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1671_ = (!crate::leanh::lean_is_exclusive(v_lhs_1631_)) as u8;
                if v_isSharedCheck_1671_ == 0 {
                    v___x_1639_ = v_lhs_1631_;
                    v_isShared_1640_ = v_isSharedCheck_1671_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_1636_);
                    crate::leanh::lean_dec(v_lhs_1631_);
                    v___x_1639_ = crate::leanh::lean_box(0);
                    v_isShared_1640_ = v_isSharedCheck_1671_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_gate_1641_ = crate::leanh::lean_ctor_get(v_rhs_1632_, 0);
                v_invert_1642_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_1632_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1670_ = (!crate::leanh::lean_is_exclusive(v_rhs_1632_)) as u8;
                if v_isSharedCheck_1670_ == 0 {
                    v___x_1644_ = v_rhs_1632_;
                    v_isShared_1645_ = v_isSharedCheck_1670_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_1641_);
                    crate::leanh::lean_dec(v_rhs_1632_);
                    v___x_1644_ = crate::leanh::lean_box(0);
                    v_isShared_1645_ = v_isSharedCheck_1670_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_invert_1637_ == 0 {
                    v___x_1662_ = 1;
                    if v_isShared_1640_ == 0 {
                        v___x_1664_ = v___x_1639_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_1665_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_gate_1636_);
                        v___x_1664_ = v_reuseFailAlloc_1665_;
                        state = 20;
                        continue;
                    }
                } else {
                    v___x_1666_ = 0;
                    if v_isShared_1640_ == 0 {
                        v___x_1668_ = v___x_1639_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_1669_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_gate_1636_);
                        v___x_1668_ = v_reuseFailAlloc_1669_;
                        state = 21;
                        continue;
                    }
                }
            }
            15 => {
                if v_invert_1642_ == 0 {
                    v___x_1648_ = 1;
                    if v_isShared_1645_ == 0 {
                        v___x_1650_ = v___x_1644_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_1654_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_gate_1641_);
                        v___x_1650_ = v_reuseFailAlloc_1654_;
                        state = 16;
                        continue;
                    }
                } else {
                    v___x_1655_ = 0;
                    if v_isShared_1645_ == 0 {
                        v___x_1657_ = v___x_1644_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_1661_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_gate_1641_);
                        v___x_1657_ = v_reuseFailAlloc_1661_;
                        state = 18;
                        continue;
                    }
                }
            }
            16 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1650_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1648_,
                );
                if v_isShared_1635_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1634_, 1, v___x_1650_);
                    crate::leanh::lean_ctor_set(v___x_1634_, 0, v___y_1647_);
                    v___x_1652_ = v___x_1634_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1653_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___y_1647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1653_, 1, v___x_1650_);
                    v___x_1652_ = v_reuseFailAlloc_1653_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___y_1606_ = v___x_1652_;
                state = 7;
                continue;
            }
            18 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1657_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1655_,
                );
                if v_isShared_1635_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1634_, 1, v___x_1657_);
                    crate::leanh::lean_ctor_set(v___x_1634_, 0, v___y_1647_);
                    v___x_1659_ = v___x_1634_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1660_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___y_1647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1660_, 1, v___x_1657_);
                    v___x_1659_ = v_reuseFailAlloc_1660_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___y_1606_ = v___x_1659_;
                state = 7;
                continue;
            }
            20 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1664_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1662_,
                );
                v___y_1647_ = v___x_1664_;
                state = 15;
                continue;
            }
            21 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1668_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1666_,
                );
                v___y_1647_ = v___x_1668_;
                state = 15;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(
    mut v_aig_1673_: *mut crate::leanh::LeanObject,
    mut v_expr_1674_: *mut crate::leanh::LeanObject,
    mut v_cache_1675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1679_: u8 = 0;
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1688_: u8 = 0;
    let mut v_cache_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1692_: u8 = 0;
    let mut v_aig_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1696_: u8 = 0;
    let mut v_gate_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1700_: u8 = 0;
    let mut v___x_1701_: u8 = 0;
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1711_: u8 = 0;
    let mut v_isSharedCheck_1712_: u8 = 0;
    let mut v_unused_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1714_: u8 = 0;
    let mut v_unused_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1719_: u8 = 0;
    let mut v_aig_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1723_: u8 = 0;
    let mut v_gate_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1727_: u8 = 0;
    let mut v___x_1728_: u8 = 0;
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1738_: u8 = 0;
    let mut v_isSharedCheck_1739_: u8 = 0;
    let mut v_unused_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1741_: u8 = 0;
    let mut v_unused_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1743_: u8 = 0;
    let mut v_a_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1756_: u8 = 0;
    let mut v_aig_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1761_: u8 = 0;
    let mut v_gate_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1763_: u8 = 0;
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1766_: u8 = 0;
    let mut v_lhsRef_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ret_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ret_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ret_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ret_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1789_: u8 = 0;
    let mut v_isSharedCheck_1790_: u8 = 0;
    let mut v_isSharedCheck_1791_: u8 = 0;
    let mut v_a_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1813_: u8 = 0;
    let mut v_aig_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1817_: u8 = 0;
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1820_: u8 = 0;
    let mut v_gate_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_1822_: u8 = 0;
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1825_: u8 = 0;
    let mut v_discrRef_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsRef_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ret_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1839_: u8 = 0;
    let mut v_isSharedCheck_1840_: u8 = 0;
    let mut v_isSharedCheck_1841_: u8 = 0;
    let mut v_isSharedCheck_1842_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_expr_1674_) {
                0 => {
                    v_a_1676_ = crate::leanh::lean_ctor_get(v_expr_1674_, 0);
                    crate::leanh::lean_inc(v_a_1676_);
                    crate::leanh::lean_dec_ref_known(v_expr_1674_, 1);
                    v___x_1677_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1677_, 0, v_a_1676_);
                    crate::leanh::lean_ctor_set(v___x_1677_, 1, v_cache_1675_);
                    v___x_1678_ = l_Std_Tactic_BVDecide_BVPred_bitblast(v_aig_1673_, v___x_1677_);
                    return v___x_1678_;
                }
                1 => {
                    v_a_1679_ = crate::leanh::lean_ctor_get_uint8(v_expr_1674_, 0 as u32);
                    crate::leanh::lean_dec_ref_known(v_expr_1674_, 0);
                    v___x_1680_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1681_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1681_, 0, v___x_1680_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1681_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_a_1679_,
                    );
                    v___x_1682_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1682_, 0, v_aig_1673_);
                    crate::leanh::lean_ctor_set(v___x_1682_, 1, v___x_1681_);
                    v___x_1683_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1683_, 0, v___x_1682_);
                    crate::leanh::lean_ctor_set(v___x_1683_, 1, v_cache_1675_);
                    return v___x_1683_;
                }
                2 => {
                    v_a_1684_ = crate::leanh::lean_ctor_get(v_expr_1674_, 0);
                    crate::leanh::lean_inc_ref(v_a_1684_);
                    crate::leanh::lean_dec_ref_known(v_expr_1674_, 1);
                    v___x_1685_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(
                        v_aig_1673_,
                        v_a_1684_,
                        v_cache_1675_,
                    );
                    v_result_1686_ = crate::leanh::lean_ctor_get(v___x_1685_, 0);
                    crate::leanh::lean_inc_ref(v_result_1686_);
                    v_ref_1687_ = crate::leanh::lean_ctor_get(v_result_1686_, 1);
                    crate::leanh::lean_inc_ref(v_ref_1687_);
                    v_invert_1688_ = crate::leanh::lean_ctor_get_uint8(
                        v_ref_1687_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_invert_1688_ == 0 {
                        v_cache_1689_ = crate::leanh::lean_ctor_get(v___x_1685_, 1);
                        v_isSharedCheck_1714_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1685_)) as u8;
                        if v_isSharedCheck_1714_ == 0 {
                            v_unused_1715_ = crate::leanh::lean_ctor_get(v___x_1685_, 0);
                            crate::leanh::lean_dec(v_unused_1715_);
                            v___x_1691_ = v___x_1685_;
                            v_isShared_1692_ = v_isSharedCheck_1714_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_cache_1689_);
                            crate::leanh::lean_dec(v___x_1685_);
                            v___x_1691_ = crate::leanh::lean_box(0);
                            v_isShared_1692_ = v_isSharedCheck_1714_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_cache_1716_ = crate::leanh::lean_ctor_get(v___x_1685_, 1);
                        v_isSharedCheck_1741_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1685_)) as u8;
                        if v_isSharedCheck_1741_ == 0 {
                            v_unused_1742_ = crate::leanh::lean_ctor_get(v___x_1685_, 0);
                            crate::leanh::lean_dec(v_unused_1742_);
                            v___x_1718_ = v___x_1685_;
                            v_isShared_1719_ = v_isSharedCheck_1741_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_cache_1716_);
                            crate::leanh::lean_dec(v___x_1685_);
                            v___x_1718_ = crate::leanh::lean_box(0);
                            v_isShared_1719_ = v_isSharedCheck_1741_;
                            state = 7;
                            continue;
                        }
                    }
                }
                3 => {
                    v_a_1743_ = crate::leanh::lean_ctor_get_uint8(
                        v_expr_1674_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v_a_1744_ = crate::leanh::lean_ctor_get(v_expr_1674_, 0);
                    crate::leanh::lean_inc_ref(v_a_1744_);
                    v_a_1745_ = crate::leanh::lean_ctor_get(v_expr_1674_, 1);
                    crate::leanh::lean_inc_ref(v_a_1745_);
                    crate::leanh::lean_dec_ref_known(v_expr_1674_, 2);
                    v___x_1746_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(
                        v_aig_1673_,
                        v_a_1744_,
                        v_cache_1675_,
                    );
                    v_result_1747_ = crate::leanh::lean_ctor_get(v___x_1746_, 0);
                    crate::leanh::lean_inc_ref(v_result_1747_);
                    v_cache_1748_ = crate::leanh::lean_ctor_get(v___x_1746_, 1);
                    crate::leanh::lean_inc_ref(v_cache_1748_);
                    crate::leanh::lean_dec_ref(v___x_1746_);
                    v_aig_1749_ = crate::leanh::lean_ctor_get(v_result_1747_, 0);
                    crate::leanh::lean_inc_ref(v_aig_1749_);
                    v_ref_1750_ = crate::leanh::lean_ctor_get(v_result_1747_, 1);
                    crate::leanh::lean_inc_ref(v_ref_1750_);
                    crate::leanh::lean_dec_ref(v_result_1747_);
                    v___x_1751_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(
                        v_aig_1749_,
                        v_a_1745_,
                        v_cache_1748_,
                    );
                    v_result_1752_ = crate::leanh::lean_ctor_get(v___x_1751_, 0);
                    v_cache_1753_ = crate::leanh::lean_ctor_get(v___x_1751_, 1);
                    v_isSharedCheck_1791_ = (!crate::leanh::lean_is_exclusive(v___x_1751_)) as u8;
                    if v_isSharedCheck_1791_ == 0 {
                        v___x_1755_ = v___x_1751_;
                        v_isShared_1756_ = v_isSharedCheck_1791_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cache_1753_);
                        crate::leanh::lean_inc(v_result_1752_);
                        crate::leanh::lean_dec(v___x_1751_);
                        v___x_1755_ = crate::leanh::lean_box(0);
                        v_isShared_1756_ = v_isSharedCheck_1791_;
                        state = 13;
                        continue;
                    }
                }
                _ => {
                    v_a_1792_ = crate::leanh::lean_ctor_get(v_expr_1674_, 0);
                    v_a_1793_ = crate::leanh::lean_ctor_get(v_expr_1674_, 1);
                    v_a_1794_ = crate::leanh::lean_ctor_get(v_expr_1674_, 2);
                    v_isSharedCheck_1842_ = (!crate::leanh::lean_is_exclusive(v_expr_1674_)) as u8;
                    if v_isSharedCheck_1842_ == 0 {
                        v___x_1796_ = v_expr_1674_;
                        v_isShared_1797_ = v_isSharedCheck_1842_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1794_);
                        crate::leanh::lean_inc(v_a_1793_);
                        crate::leanh::lean_inc(v_a_1792_);
                        crate::leanh::lean_dec(v_expr_1674_);
                        v___x_1796_ = crate::leanh::lean_box(0);
                        v_isShared_1797_ = v_isSharedCheck_1842_;
                        state = 22;
                        continue;
                    }
                }
            },
            1 => {
                v_aig_1693_ = crate::leanh::lean_ctor_get(v_result_1686_, 0);
                v_isSharedCheck_1712_ = (!crate::leanh::lean_is_exclusive(v_result_1686_)) as u8;
                if v_isSharedCheck_1712_ == 0 {
                    v_unused_1713_ = crate::leanh::lean_ctor_get(v_result_1686_, 1);
                    crate::leanh::lean_dec(v_unused_1713_);
                    v___x_1695_ = v_result_1686_;
                    v_isShared_1696_ = v_isSharedCheck_1712_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_aig_1693_);
                    crate::leanh::lean_dec(v_result_1686_);
                    v___x_1695_ = crate::leanh::lean_box(0);
                    v_isShared_1696_ = v_isSharedCheck_1712_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_1697_ = crate::leanh::lean_ctor_get(v_ref_1687_, 0);
                v_isSharedCheck_1711_ = (!crate::leanh::lean_is_exclusive(v_ref_1687_)) as u8;
                if v_isSharedCheck_1711_ == 0 {
                    v___x_1699_ = v_ref_1687_;
                    v_isShared_1700_ = v_isSharedCheck_1711_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_1697_);
                    crate::leanh::lean_dec(v_ref_1687_);
                    v___x_1699_ = crate::leanh::lean_box(0);
                    v_isShared_1700_ = v_isSharedCheck_1711_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1701_ = 1;
                if v_isShared_1700_ == 0 {
                    v___x_1703_ = v___x_1699_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1710_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_gate_1697_);
                    v___x_1703_ = v_reuseFailAlloc_1710_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1703_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1701_,
                );
                if v_isShared_1696_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1695_, 1, v___x_1703_);
                    v___x_1705_ = v___x_1695_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1709_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_aig_1693_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1709_, 1, v___x_1703_);
                    v___x_1705_ = v_reuseFailAlloc_1709_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1692_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1691_, 0, v___x_1705_);
                    v___x_1707_ = v___x_1691_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1708_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_cache_1689_);
                    v___x_1707_ = v_reuseFailAlloc_1708_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1707_;
            }
            7 => {
                v_aig_1720_ = crate::leanh::lean_ctor_get(v_result_1686_, 0);
                v_isSharedCheck_1739_ = (!crate::leanh::lean_is_exclusive(v_result_1686_)) as u8;
                if v_isSharedCheck_1739_ == 0 {
                    v_unused_1740_ = crate::leanh::lean_ctor_get(v_result_1686_, 1);
                    crate::leanh::lean_dec(v_unused_1740_);
                    v___x_1722_ = v_result_1686_;
                    v_isShared_1723_ = v_isSharedCheck_1739_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_aig_1720_);
                    crate::leanh::lean_dec(v_result_1686_);
                    v___x_1722_ = crate::leanh::lean_box(0);
                    v_isShared_1723_ = v_isSharedCheck_1739_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_gate_1724_ = crate::leanh::lean_ctor_get(v_ref_1687_, 0);
                v_isSharedCheck_1738_ = (!crate::leanh::lean_is_exclusive(v_ref_1687_)) as u8;
                if v_isSharedCheck_1738_ == 0 {
                    v___x_1726_ = v_ref_1687_;
                    v_isShared_1727_ = v_isSharedCheck_1738_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_1724_);
                    crate::leanh::lean_dec(v_ref_1687_);
                    v___x_1726_ = crate::leanh::lean_box(0);
                    v_isShared_1727_ = v_isSharedCheck_1738_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1728_ = 0;
                if v_isShared_1727_ == 0 {
                    v___x_1730_ = v___x_1726_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1737_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_gate_1724_);
                    v___x_1730_ = v_reuseFailAlloc_1737_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1730_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1728_,
                );
                if v_isShared_1723_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1722_, 1, v___x_1730_);
                    v___x_1732_ = v___x_1722_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1736_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_aig_1720_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___x_1730_);
                    v___x_1732_ = v_reuseFailAlloc_1736_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1719_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1718_, 0, v___x_1732_);
                    v___x_1734_ = v___x_1718_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1735_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_cache_1716_);
                    v___x_1734_ = v_reuseFailAlloc_1735_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1734_;
            }
            13 => {
                v_aig_1757_ = crate::leanh::lean_ctor_get(v_result_1752_, 0);
                v_ref_1758_ = crate::leanh::lean_ctor_get(v_result_1752_, 1);
                v_isSharedCheck_1790_ = (!crate::leanh::lean_is_exclusive(v_result_1752_)) as u8;
                if v_isSharedCheck_1790_ == 0 {
                    v___x_1760_ = v_result_1752_;
                    v_isShared_1761_ = v_isSharedCheck_1790_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_1758_);
                    crate::leanh::lean_inc(v_aig_1757_);
                    crate::leanh::lean_dec(v_result_1752_);
                    v___x_1760_ = crate::leanh::lean_box(0);
                    v_isShared_1761_ = v_isSharedCheck_1790_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v_gate_1762_ = crate::leanh::lean_ctor_get(v_ref_1750_, 0);
                v_invert_1763_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_1750_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1789_ = (!crate::leanh::lean_is_exclusive(v_ref_1750_)) as u8;
                if v_isSharedCheck_1789_ == 0 {
                    v___x_1765_ = v_ref_1750_;
                    v_isShared_1766_ = v_isSharedCheck_1789_;
                    state = 15;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_1762_);
                    crate::leanh::lean_dec(v_ref_1750_);
                    v___x_1765_ = crate::leanh::lean_box(0);
                    v_isShared_1766_ = v_isSharedCheck_1789_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1766_ == 0 {
                    v_lhsRef_1768_ = v___x_1765_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1788_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_gate_1762_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1788_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_1763_,
                    );
                    v_lhsRef_1768_ = v_reuseFailAlloc_1788_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_1761_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1760_, 0, v_lhsRef_1768_);
                    v_input_1770_ = v___x_1760_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1787_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_lhsRef_1768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_ref_1758_);
                    v_input_1770_ = v_reuseFailAlloc_1787_;
                    state = 17;
                    continue;
                }
            }
            17 => match v_a_1743_ {
                0 => {
                    v_ret_1771_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_1757_, v_input_1770_);
                    if v_isShared_1756_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1755_, 0, v_ret_1771_);
                        v___x_1773_ = v___x_1755_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_1774_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_ret_1771_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_cache_1753_);
                        v___x_1773_ = v_reuseFailAlloc_1774_;
                        state = 18;
                        continue;
                    }
                }
                1 => {
                    v_ret_1775_ = l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__1(v_aig_1757_, v_input_1770_);
                    if v_isShared_1756_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1755_, 0, v_ret_1775_);
                        v___x_1777_ = v___x_1755_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_1778_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_ret_1775_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_cache_1753_);
                        v___x_1777_ = v_reuseFailAlloc_1778_;
                        state = 19;
                        continue;
                    }
                }
                2 => {
                    v_ret_1779_ = l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__2(v_aig_1757_, v_input_1770_);
                    if v_isShared_1756_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1755_, 0, v_ret_1779_);
                        v___x_1781_ = v___x_1755_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_1782_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_ret_1779_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_cache_1753_);
                        v___x_1781_ = v_reuseFailAlloc_1782_;
                        state = 20;
                        continue;
                    }
                }
                _ => {
                    v_ret_1783_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(v_aig_1757_, v_input_1770_);
                    if v_isShared_1756_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1755_, 0, v_ret_1783_);
                        v___x_1785_ = v___x_1755_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_1786_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_ret_1783_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_cache_1753_);
                        v___x_1785_ = v_reuseFailAlloc_1786_;
                        state = 21;
                        continue;
                    }
                }
            },
            18 => {
                return v___x_1773_;
            }
            19 => {
                return v___x_1777_;
            }
            20 => {
                return v___x_1781_;
            }
            21 => {
                return v___x_1785_;
            }
            22 => {
                v___x_1798_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(
                    v_aig_1673_,
                    v_a_1792_,
                    v_cache_1675_,
                );
                v_result_1799_ = crate::leanh::lean_ctor_get(v___x_1798_, 0);
                crate::leanh::lean_inc_ref(v_result_1799_);
                v_cache_1800_ = crate::leanh::lean_ctor_get(v___x_1798_, 1);
                crate::leanh::lean_inc_ref(v_cache_1800_);
                crate::leanh::lean_dec_ref(v___x_1798_);
                v_aig_1801_ = crate::leanh::lean_ctor_get(v_result_1799_, 0);
                crate::leanh::lean_inc_ref(v_aig_1801_);
                v_ref_1802_ = crate::leanh::lean_ctor_get(v_result_1799_, 1);
                crate::leanh::lean_inc_ref(v_ref_1802_);
                crate::leanh::lean_dec_ref(v_result_1799_);
                v___x_1803_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(
                    v_aig_1801_,
                    v_a_1793_,
                    v_cache_1800_,
                );
                v_result_1804_ = crate::leanh::lean_ctor_get(v___x_1803_, 0);
                crate::leanh::lean_inc_ref(v_result_1804_);
                v_cache_1805_ = crate::leanh::lean_ctor_get(v___x_1803_, 1);
                crate::leanh::lean_inc_ref(v_cache_1805_);
                crate::leanh::lean_dec_ref(v___x_1803_);
                v_aig_1806_ = crate::leanh::lean_ctor_get(v_result_1804_, 0);
                crate::leanh::lean_inc_ref(v_aig_1806_);
                v_ref_1807_ = crate::leanh::lean_ctor_get(v_result_1804_, 1);
                crate::leanh::lean_inc_ref(v_ref_1807_);
                crate::leanh::lean_dec_ref(v_result_1804_);
                v___x_1808_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(
                    v_aig_1806_,
                    v_a_1794_,
                    v_cache_1805_,
                );
                v_result_1809_ = crate::leanh::lean_ctor_get(v___x_1808_, 0);
                v_cache_1810_ = crate::leanh::lean_ctor_get(v___x_1808_, 1);
                v_isSharedCheck_1841_ = (!crate::leanh::lean_is_exclusive(v___x_1808_)) as u8;
                if v_isSharedCheck_1841_ == 0 {
                    v___x_1812_ = v___x_1808_;
                    v_isShared_1813_ = v_isSharedCheck_1841_;
                    state = 23;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cache_1810_);
                    crate::leanh::lean_inc(v_result_1809_);
                    crate::leanh::lean_dec(v___x_1808_);
                    v___x_1812_ = crate::leanh::lean_box(0);
                    v_isShared_1813_ = v_isSharedCheck_1841_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v_aig_1814_ = crate::leanh::lean_ctor_get(v_result_1809_, 0);
                crate::leanh::lean_inc_ref(v_aig_1814_);
                v_ref_1815_ = crate::leanh::lean_ctor_get(v_result_1809_, 1);
                crate::leanh::lean_inc_ref(v_ref_1815_);
                crate::leanh::lean_dec_ref(v_result_1809_);
                v_gate_1816_ = crate::leanh::lean_ctor_get(v_ref_1802_, 0);
                v_invert_1817_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_1802_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1840_ = (!crate::leanh::lean_is_exclusive(v_ref_1802_)) as u8;
                if v_isSharedCheck_1840_ == 0 {
                    v___x_1819_ = v_ref_1802_;
                    v_isShared_1820_ = v_isSharedCheck_1840_;
                    state = 24;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_1816_);
                    crate::leanh::lean_dec(v_ref_1802_);
                    v___x_1819_ = crate::leanh::lean_box(0);
                    v_isShared_1820_ = v_isSharedCheck_1840_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v_gate_1821_ = crate::leanh::lean_ctor_get(v_ref_1807_, 0);
                v_invert_1822_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_1807_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1839_ = (!crate::leanh::lean_is_exclusive(v_ref_1807_)) as u8;
                if v_isSharedCheck_1839_ == 0 {
                    v___x_1824_ = v_ref_1807_;
                    v_isShared_1825_ = v_isSharedCheck_1839_;
                    state = 25;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_1821_);
                    crate::leanh::lean_dec(v_ref_1807_);
                    v___x_1824_ = crate::leanh::lean_box(0);
                    v_isShared_1825_ = v_isSharedCheck_1839_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_1825_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1824_, 0, v_gate_1816_);
                    v_discrRef_1827_ = v___x_1824_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1838_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_gate_1816_);
                    v_discrRef_1827_ = v_reuseFailAlloc_1838_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_discrRef_1827_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_1817_,
                );
                if v_isShared_1820_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1819_, 0, v_gate_1821_);
                    v_lhsRef_1829_ = v___x_1819_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1837_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_gate_1821_);
                    v_lhsRef_1829_ = v_reuseFailAlloc_1837_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_lhsRef_1829_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_1822_,
                );
                if v_isShared_1797_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1796_, 0);
                    crate::leanh::lean_ctor_set(v___x_1796_, 2, v_ref_1815_);
                    crate::leanh::lean_ctor_set(v___x_1796_, 1, v_lhsRef_1829_);
                    crate::leanh::lean_ctor_set(v___x_1796_, 0, v_discrRef_1827_);
                    v_input_1831_ = v___x_1796_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1836_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_discrRef_1827_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_lhsRef_1829_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1836_, 2, v_ref_1815_);
                    v_input_1831_ = v_reuseFailAlloc_1836_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v_ret_1832_ = l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__4(v_aig_1814_, v_input_1831_);
                if v_isShared_1813_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1812_, 0, v_ret_1832_);
                    v___x_1834_ = v___x_1812_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_1835_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_ret_1832_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_cache_1810_);
                    v___x_1834_ = v_reuseFailAlloc_1835_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_1834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1843_: *mut crate::leanh::LeanObject,
    mut v_m_1844_: *mut crate::leanh::LeanObject,
    mut v_a_1845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1846_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(v_m_1844_, v_a_1845_);
    return v___x_1846_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1847_: *mut crate::leanh::LeanObject,
    mut v_m_1848_: *mut crate::leanh::LeanObject,
    mut v_a_1849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1850_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1(v_00_u03b2_1847_, v_m_1848_, v_a_1849_);
    crate::leanh::lean_dec_ref(v_m_1848_);
    return v_res_1850_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3(
    mut v_00_u03b2_1851_: *mut crate::leanh::LeanObject,
    mut v_m_1852_: *mut crate::leanh::LeanObject,
    mut v_a_1853_: *mut crate::leanh::LeanObject,
    mut v_b_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1855_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(v_m_1852_, v_a_1853_, v_b_1854_);
    return v___x_1855_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7(
    mut v_00_u03b2_1856_: *mut crate::leanh::LeanObject,
    mut v_a_1857_: *mut crate::leanh::LeanObject,
    mut v_x_1858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1859_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7___redArg(v_a_1857_, v_x_1858_);
    return v___x_1859_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10(
    mut v_00_u03b2_1860_: *mut crate::leanh::LeanObject,
    mut v_a_1861_: *mut crate::leanh::LeanObject,
    mut v_x_1862_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1863_: u8 = 0;
    v___x_1863_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(v_a_1861_, v_x_1862_);
    return v___x_1863_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___boxed(
    mut v_00_u03b2_1864_: *mut crate::leanh::LeanObject,
    mut v_a_1865_: *mut crate::leanh::LeanObject,
    mut v_x_1866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1867_: u8 = 0;
    let mut v_r_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1867_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_1864_, v_a_1865_, v_x_1866_);
    v_r_1868_ = crate::leanh::lean_box((v_res_1867_) as usize);
    return v_r_1868_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11(
    mut v_00_u03b2_1869_: *mut crate::leanh::LeanObject,
    mut v_data_1870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1871_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11___redArg(v_data_1870_);
    return v___x_1871_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12(
    mut v_00_u03b2_1872_: *mut crate::leanh::LeanObject,
    mut v_a_1873_: *mut crate::leanh::LeanObject,
    mut v_b_1874_: *mut crate::leanh::LeanObject,
    mut v_x_1875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1876_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12___redArg(v_a_1873_, v_b_1874_, v_x_1875_);
    return v___x_1876_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12(
    mut v_00_u03b2_1877_: *mut crate::leanh::LeanObject,
    mut v_i_1878_: *mut crate::leanh::LeanObject,
    mut v_source_1879_: *mut crate::leanh::LeanObject,
    mut v_target_1880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1881_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(v_i_1878_, v_source_1879_, v_target_1880_);
    return v___x_1881_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(
    mut v_00_u03b2_1882_: *mut crate::leanh::LeanObject,
    mut v_x_1883_: *mut crate::leanh::LeanObject,
    mut v_x_1884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1885_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_x_1883_, v_x_1884_);
    return v___x_1885_;
}
pub unsafe fn _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1890_ = crate::leanh::lean_box(0);
    v___x_1891_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1892_ = lean_mk_array(v___x_1891_, v___x_1890_);
    return v___x_1892_;
}
pub unsafe fn _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1893_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1), core::ptr::addr_of_mut!(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1_once), _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1);
    v___x_1894_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1895_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1895_, 0, v___x_1894_);
    crate::leanh::lean_ctor_set(v___x_1895_, 1, v___x_1893_);
    return v___x_1895_;
}
pub unsafe fn _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1896_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2), core::ptr::addr_of_mut!(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2_once), _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2);
    v___x_1897_ =
        l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0;
    v___x_1898_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1898_, 0, v___x_1897_);
    crate::leanh::lean_ctor_set(v___x_1898_, 1, v___x_1896_);
    return v___x_1898_;
}
pub unsafe fn _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1899_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3), core::ptr::addr_of_mut!(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3_once), _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3);
    return v___x_1899_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1900_ = crate::leanh::lean_box(0);
    v___x_1901_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1902_ = lean_mk_array(v___x_1901_, v___x_1900_);
    return v___x_1902_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1903_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0_once),
        _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0,
    );
    v___x_1904_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1905_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1905_, 0, v___x_1904_);
    crate::leanh::lean_ctor_set(v___x_1905_, 1, v___x_1903_);
    return v___x_1905_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(
    mut v_expr_1906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1907_ = l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
    v___x_1908_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1_once),
        _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1,
    );
    v___x_1909_ =
        l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v___x_1907_, v_expr_1906_, v___x_1908_);
    v_result_1910_ = crate::leanh::lean_ctor_get(v___x_1909_, 0);
    crate::leanh::lean_inc_ref(v_result_1910_);
    crate::leanh::lean_dec_ref(v___x_1909_);
    return v_result_1910_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter___redArg(
    mut v_expr_1911_: *mut crate::leanh::LeanObject,
    mut v_h__1_1912_: *mut crate::leanh::LeanObject,
    mut v_h__2_1913_: *mut crate::leanh::LeanObject,
    mut v_h__3_1914_: *mut crate::leanh::LeanObject,
    mut v_h__4_1915_: *mut crate::leanh::LeanObject,
    mut v_h__5_1916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_expr_1911_) {
        0 => {
            let mut v_a_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1916_);
            crate::leanh::lean_dec(v_h__4_1915_);
            crate::leanh::lean_dec(v_h__3_1914_);
            crate::leanh::lean_dec(v_h__2_1913_);
            v_a_1917_ = crate::leanh::lean_ctor_get(v_expr_1911_, 0);
            crate::leanh::lean_inc(v_a_1917_);
            crate::leanh::lean_dec_ref_known(v_expr_1911_, 1);
            v___x_1918_ = crate::leanh::lean_apply_1(v_h__1_1912_, v_a_1917_);
            return v___x_1918_;
        }
        1 => {
            let mut v_a_1919_: u8 = 0;
            let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1916_);
            crate::leanh::lean_dec(v_h__4_1915_);
            crate::leanh::lean_dec(v_h__3_1914_);
            crate::leanh::lean_dec(v_h__1_1912_);
            v_a_1919_ = crate::leanh::lean_ctor_get_uint8(v_expr_1911_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_expr_1911_, 0);
            v___x_1920_ = crate::leanh::lean_box((v_a_1919_) as usize);
            v___x_1921_ = crate::leanh::lean_apply_1(v_h__2_1913_, v___x_1920_);
            return v___x_1921_;
        }
        2 => {
            let mut v_a_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1916_);
            crate::leanh::lean_dec(v_h__4_1915_);
            crate::leanh::lean_dec(v_h__2_1913_);
            crate::leanh::lean_dec(v_h__1_1912_);
            v_a_1922_ = crate::leanh::lean_ctor_get(v_expr_1911_, 0);
            crate::leanh::lean_inc_ref(v_a_1922_);
            crate::leanh::lean_dec_ref_known(v_expr_1911_, 1);
            v___x_1923_ = crate::leanh::lean_apply_1(v_h__3_1914_, v_a_1922_);
            return v___x_1923_;
        }
        3 => {
            let mut v_a_1924_: u8 = 0;
            let mut v_a_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1915_);
            crate::leanh::lean_dec(v_h__3_1914_);
            crate::leanh::lean_dec(v_h__2_1913_);
            crate::leanh::lean_dec(v_h__1_1912_);
            v_a_1924_ = crate::leanh::lean_ctor_get_uint8(
                v_expr_1911_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
            );
            v_a_1925_ = crate::leanh::lean_ctor_get(v_expr_1911_, 0);
            crate::leanh::lean_inc_ref(v_a_1925_);
            v_a_1926_ = crate::leanh::lean_ctor_get(v_expr_1911_, 1);
            crate::leanh::lean_inc_ref(v_a_1926_);
            crate::leanh::lean_dec_ref_known(v_expr_1911_, 2);
            v___x_1927_ = crate::leanh::lean_box((v_a_1924_) as usize);
            v___x_1928_ =
                crate::leanh::lean_apply_3(v_h__5_1916_, v___x_1927_, v_a_1925_, v_a_1926_);
            return v___x_1928_;
        }
        _ => {
            let mut v_a_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1916_);
            crate::leanh::lean_dec(v_h__3_1914_);
            crate::leanh::lean_dec(v_h__2_1913_);
            crate::leanh::lean_dec(v_h__1_1912_);
            v_a_1929_ = crate::leanh::lean_ctor_get(v_expr_1911_, 0);
            crate::leanh::lean_inc_ref(v_a_1929_);
            v_a_1930_ = crate::leanh::lean_ctor_get(v_expr_1911_, 1);
            crate::leanh::lean_inc_ref(v_a_1930_);
            v_a_1931_ = crate::leanh::lean_ctor_get(v_expr_1911_, 2);
            crate::leanh::lean_inc_ref(v_a_1931_);
            crate::leanh::lean_dec_ref_known(v_expr_1911_, 3);
            v___x_1932_ = crate::leanh::lean_apply_3(v_h__4_1915_, v_a_1929_, v_a_1930_, v_a_1931_);
            return v___x_1932_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter(
    mut v_motive_1933_: *mut crate::leanh::LeanObject,
    mut v_expr_1934_: *mut crate::leanh::LeanObject,
    mut v_h__1_1935_: *mut crate::leanh::LeanObject,
    mut v_h__2_1936_: *mut crate::leanh::LeanObject,
    mut v_h__3_1937_: *mut crate::leanh::LeanObject,
    mut v_h__4_1938_: *mut crate::leanh::LeanObject,
    mut v_h__5_1939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_expr_1934_) {
        0 => {
            let mut v_a_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1939_);
            crate::leanh::lean_dec(v_h__4_1938_);
            crate::leanh::lean_dec(v_h__3_1937_);
            crate::leanh::lean_dec(v_h__2_1936_);
            v_a_1940_ = crate::leanh::lean_ctor_get(v_expr_1934_, 0);
            crate::leanh::lean_inc(v_a_1940_);
            crate::leanh::lean_dec_ref_known(v_expr_1934_, 1);
            v___x_1941_ = crate::leanh::lean_apply_1(v_h__1_1935_, v_a_1940_);
            return v___x_1941_;
        }
        1 => {
            let mut v_a_1942_: u8 = 0;
            let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1939_);
            crate::leanh::lean_dec(v_h__4_1938_);
            crate::leanh::lean_dec(v_h__3_1937_);
            crate::leanh::lean_dec(v_h__1_1935_);
            v_a_1942_ = crate::leanh::lean_ctor_get_uint8(v_expr_1934_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_expr_1934_, 0);
            v___x_1943_ = crate::leanh::lean_box((v_a_1942_) as usize);
            v___x_1944_ = crate::leanh::lean_apply_1(v_h__2_1936_, v___x_1943_);
            return v___x_1944_;
        }
        2 => {
            let mut v_a_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1939_);
            crate::leanh::lean_dec(v_h__4_1938_);
            crate::leanh::lean_dec(v_h__2_1936_);
            crate::leanh::lean_dec(v_h__1_1935_);
            v_a_1945_ = crate::leanh::lean_ctor_get(v_expr_1934_, 0);
            crate::leanh::lean_inc_ref(v_a_1945_);
            crate::leanh::lean_dec_ref_known(v_expr_1934_, 1);
            v___x_1946_ = crate::leanh::lean_apply_1(v_h__3_1937_, v_a_1945_);
            return v___x_1946_;
        }
        3 => {
            let mut v_a_1947_: u8 = 0;
            let mut v_a_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1938_);
            crate::leanh::lean_dec(v_h__3_1937_);
            crate::leanh::lean_dec(v_h__2_1936_);
            crate::leanh::lean_dec(v_h__1_1935_);
            v_a_1947_ = crate::leanh::lean_ctor_get_uint8(
                v_expr_1934_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
            );
            v_a_1948_ = crate::leanh::lean_ctor_get(v_expr_1934_, 0);
            crate::leanh::lean_inc_ref(v_a_1948_);
            v_a_1949_ = crate::leanh::lean_ctor_get(v_expr_1934_, 1);
            crate::leanh::lean_inc_ref(v_a_1949_);
            crate::leanh::lean_dec_ref_known(v_expr_1934_, 2);
            v___x_1950_ = crate::leanh::lean_box((v_a_1947_) as usize);
            v___x_1951_ =
                crate::leanh::lean_apply_3(v_h__5_1939_, v___x_1950_, v_a_1948_, v_a_1949_);
            return v___x_1951_;
        }
        _ => {
            let mut v_a_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1939_);
            crate::leanh::lean_dec(v_h__3_1937_);
            crate::leanh::lean_dec(v_h__2_1936_);
            crate::leanh::lean_dec(v_h__1_1935_);
            v_a_1952_ = crate::leanh::lean_ctor_get(v_expr_1934_, 0);
            crate::leanh::lean_inc_ref(v_a_1952_);
            v_a_1953_ = crate::leanh::lean_ctor_get(v_expr_1934_, 1);
            crate::leanh::lean_inc_ref(v_a_1953_);
            v_a_1954_ = crate::leanh::lean_ctor_get(v_expr_1934_, 2);
            crate::leanh::lean_inc_ref(v_a_1954_);
            crate::leanh::lean_dec_ref_known(v_expr_1934_, 3);
            v___x_1955_ = crate::leanh::lean_apply_3(v_h__4_1938_, v_a_1952_, v_a_1953_, v_a_1954_);
            return v___x_1955_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___redArg(
    mut v_x_1956_: *mut crate::leanh::LeanObject,
    mut v_h__1_1957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_result_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_result_1958_ = crate::leanh::lean_ctor_get(v_x_1956_, 0);
    crate::leanh::lean_inc_ref(v_result_1958_);
    v_cache_1959_ = crate::leanh::lean_ctor_get(v_x_1956_, 1);
    crate::leanh::lean_inc_ref(v_cache_1959_);
    crate::leanh::lean_dec_ref(v_x_1956_);
    v_aig_1960_ = crate::leanh::lean_ctor_get(v_result_1958_, 0);
    crate::leanh::lean_inc_ref(v_aig_1960_);
    v_ref_1961_ = crate::leanh::lean_ctor_get(v_result_1958_, 1);
    crate::leanh::lean_inc_ref(v_ref_1961_);
    crate::leanh::lean_dec_ref(v_result_1958_);
    v___x_1962_ = crate::leanh::lean_apply_4(
        v_h__1_1957_,
        v_aig_1960_,
        v_ref_1961_,
        crate::leanh::lean_box(0),
        v_cache_1959_,
    );
    return v___x_1962_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter(
    mut v_aig_1963_: *mut crate::leanh::LeanObject,
    mut v_motive_1964_: *mut crate::leanh::LeanObject,
    mut v_x_1965_: *mut crate::leanh::LeanObject,
    mut v_h__1_1966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_result_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_result_1967_ = crate::leanh::lean_ctor_get(v_x_1965_, 0);
    crate::leanh::lean_inc_ref(v_result_1967_);
    v_cache_1968_ = crate::leanh::lean_ctor_get(v_x_1965_, 1);
    crate::leanh::lean_inc_ref(v_cache_1968_);
    crate::leanh::lean_dec_ref(v_x_1965_);
    v_aig_1969_ = crate::leanh::lean_ctor_get(v_result_1967_, 0);
    crate::leanh::lean_inc_ref(v_aig_1969_);
    v_ref_1970_ = crate::leanh::lean_ctor_get(v_result_1967_, 1);
    crate::leanh::lean_inc_ref(v_ref_1970_);
    crate::leanh::lean_dec_ref(v_result_1967_);
    v___x_1971_ = crate::leanh::lean_apply_4(
        v_h__1_1966_,
        v_aig_1969_,
        v_ref_1970_,
        crate::leanh::lean_box(0),
        v_cache_1968_,
    );
    return v___x_1971_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___boxed(
    mut v_aig_1972_: *mut crate::leanh::LeanObject,
    mut v_motive_1973_: *mut crate::leanh::LeanObject,
    mut v_x_1974_: *mut crate::leanh::LeanObject,
    mut v_h__1_1975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1976_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter(v_aig_1972_, v_motive_1973_, v_x_1974_, v_h__1_1975_);
    crate::leanh::lean_dec_ref(v_aig_1972_);
    return v_res_1976_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(
    mut v_g_1977_: u8,
    mut v_h__1_1978_: *mut crate::leanh::LeanObject,
    mut v_h__2_1979_: *mut crate::leanh::LeanObject,
    mut v_h__3_1980_: *mut crate::leanh::LeanObject,
    mut v_h__4_1981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_g_1977_ {
        0 => {
            let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1981_);
            crate::leanh::lean_dec(v_h__3_1980_);
            crate::leanh::lean_dec(v_h__2_1979_);
            v___x_1982_ = crate::leanh::lean_box(0);
            v___x_1983_ = crate::leanh::lean_apply_1(v_h__1_1978_, v___x_1982_);
            return v___x_1983_;
        }
        1 => {
            let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1981_);
            crate::leanh::lean_dec(v_h__3_1980_);
            crate::leanh::lean_dec(v_h__1_1978_);
            v___x_1984_ = crate::leanh::lean_box(0);
            v___x_1985_ = crate::leanh::lean_apply_1(v_h__2_1979_, v___x_1984_);
            return v___x_1985_;
        }
        2 => {
            let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1981_);
            crate::leanh::lean_dec(v_h__2_1979_);
            crate::leanh::lean_dec(v_h__1_1978_);
            v___x_1986_ = crate::leanh::lean_box(0);
            v___x_1987_ = crate::leanh::lean_apply_1(v_h__3_1980_, v___x_1986_);
            return v___x_1987_;
        }
        _ => {
            let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1980_);
            crate::leanh::lean_dec(v_h__2_1979_);
            crate::leanh::lean_dec(v_h__1_1978_);
            v___x_1988_ = crate::leanh::lean_box(0);
            v___x_1989_ = crate::leanh::lean_apply_1(v_h__4_1981_, v___x_1988_);
            return v___x_1989_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg___boxed(
    mut v_g_1990_: *mut crate::leanh::LeanObject,
    mut v_h__1_1991_: *mut crate::leanh::LeanObject,
    mut v_h__2_1992_: *mut crate::leanh::LeanObject,
    mut v_h__3_1993_: *mut crate::leanh::LeanObject,
    mut v_h__4_1994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_g_46__boxed_1995_: u8 = 0;
    let mut v_res_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_g_46__boxed_1995_ = (crate::leanh::lean_unbox(v_g_1990_) as u8);
    v_res_1996_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(v_g_46__boxed_1995_, v_h__1_1991_, v_h__2_1992_, v_h__3_1993_, v_h__4_1994_);
    return v_res_1996_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(
    mut v_motive_1997_: *mut crate::leanh::LeanObject,
    mut v_g_1998_: u8,
    mut v_h__1_1999_: *mut crate::leanh::LeanObject,
    mut v_h__2_2000_: *mut crate::leanh::LeanObject,
    mut v_h__3_2001_: *mut crate::leanh::LeanObject,
    mut v_h__4_2002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_g_1998_ {
        0 => {
            let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_2002_);
            crate::leanh::lean_dec(v_h__3_2001_);
            crate::leanh::lean_dec(v_h__2_2000_);
            v___x_2003_ = crate::leanh::lean_box(0);
            v___x_2004_ = crate::leanh::lean_apply_1(v_h__1_1999_, v___x_2003_);
            return v___x_2004_;
        }
        1 => {
            let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_2002_);
            crate::leanh::lean_dec(v_h__3_2001_);
            crate::leanh::lean_dec(v_h__1_1999_);
            v___x_2005_ = crate::leanh::lean_box(0);
            v___x_2006_ = crate::leanh::lean_apply_1(v_h__2_2000_, v___x_2005_);
            return v___x_2006_;
        }
        2 => {
            let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_2002_);
            crate::leanh::lean_dec(v_h__2_2000_);
            crate::leanh::lean_dec(v_h__1_1999_);
            v___x_2007_ = crate::leanh::lean_box(0);
            v___x_2008_ = crate::leanh::lean_apply_1(v_h__3_2001_, v___x_2007_);
            return v___x_2008_;
        }
        _ => {
            let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_2001_);
            crate::leanh::lean_dec(v_h__2_2000_);
            crate::leanh::lean_dec(v_h__1_1999_);
            v___x_2009_ = crate::leanh::lean_box(0);
            v___x_2010_ = crate::leanh::lean_apply_1(v_h__4_2002_, v___x_2009_);
            return v___x_2010_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___boxed(
    mut v_motive_2011_: *mut crate::leanh::LeanObject,
    mut v_g_2012_: *mut crate::leanh::LeanObject,
    mut v_h__1_2013_: *mut crate::leanh::LeanObject,
    mut v_h__2_2014_: *mut crate::leanh::LeanObject,
    mut v_h__3_2015_: *mut crate::leanh::LeanObject,
    mut v_h__4_2016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_g_65__boxed_2017_: u8 = 0;
    let mut v_res_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_g_65__boxed_2017_ = (crate::leanh::lean_unbox(v_g_2012_) as u8);
    v_res_2018_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(v_motive_2011_, v_g_65__boxed_2017_, v_h__1_2013_, v_h__2_2014_, v_h__3_2015_, v_h__4_2016_);
    return v_res_2018_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0 =
        _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0();
    crate::leanh::lean_mark_persistent(
        l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(builtin);
}
