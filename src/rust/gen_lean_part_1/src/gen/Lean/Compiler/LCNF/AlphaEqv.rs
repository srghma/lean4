// Lean compiler output
// Module: Lean.Compiler.LCNF.AlphaEqv
// Imports: Lean.Compiler.LCNF.Basic Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fswap, lean_array_get_size,
    lean_array_size, lean_array_uget_borrowed, lean_expr_eqv, lean_level_eq, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_shiftr, lean_nat_sub,
    lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    initialize_Lean_Compiler_LCNF_Basic, l_Lean_Compiler_LCNF_instBEqCtorInfo_beq,
    l_Lean_Compiler_LCNF_instBEqLitValue_beq, runtime_initialize_Lean_Compiler_LCNF_Basic,
};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_lt,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_instBEqFVarId_beq,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg,
};
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0___redArg(
    mut v_t_1083_: *mut leanh::LeanObject,
    mut v_k_1084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: u8 = 0;
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1083_) == 0 {
                    v_k_1085_ = leanh::lean_ctor_get(v_t_1083_, 1);
                    v_v_1086_ = leanh::lean_ctor_get(v_t_1083_, 2);
                    v_l_1087_ = leanh::lean_ctor_get(v_t_1083_, 3);
                    v_r_1088_ = leanh::lean_ctor_get(v_t_1083_, 4);
                    v___x_1089_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1084_, v_k_1085_);
                    match v___x_1089_ {
                        0 => {
                            v_t_1083_ = v_l_1087_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            leanh::lean_inc(v_v_1086_);
                            v___x_1091_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1091_, 0, v_v_1086_);
                            return v___x_1091_;
                        }
                        _ => {
                            v_t_1083_ = v_r_1088_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1093_ = leanh::lean_box(0);
                    return v___x_1093_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0___redArg___boxed(
    mut v_t_1094_: *mut leanh::LeanObject,
    mut v_k_1095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1096_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0___redArg(v_t_1094_, v_k_1095_);
    leanh::lean_dec(v_k_1095_);
    leanh::lean_dec(v_t_1094_);
    return v_res_1096_;
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
    mut v_fvarId_u2081_1097_: *mut leanh::LeanObject,
    mut v_fvarId_u2082_1098_: *mut leanh::LeanObject,
    mut v_a_1099_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1100_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0___redArg(v_a_1099_, v_fvarId_u2082_1098_);
    if leanh::lean_obj_tag(v___x_1100_) == 0 {
        let mut v___x_1101_: u8 = 0;
        v___x_1101_ = l_Lean_instBEqFVarId_beq(v_fvarId_u2081_1097_, v_fvarId_u2082_1098_);
        return v___x_1101_;
    } else {
        let mut v_val_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1103_: u8 = 0;
        v_val_1102_ = leanh::lean_ctor_get(v___x_1100_, 0);
        leanh::lean_inc(v_val_1102_);
        leanh::lean_dec_ref_known(v___x_1100_, 1);
        v___x_1103_ = l_Lean_instBEqFVarId_beq(v_fvarId_u2081_1097_, v_val_1102_);
        leanh::lean_dec(v_val_1102_);
        return v___x_1103_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar___boxed(
    mut v_fvarId_u2081_1104_: *mut leanh::LeanObject,
    mut v_fvarId_u2082_1105_: *mut leanh::LeanObject,
    mut v_a_1106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1107_: u8 = 0;
    let mut v_r_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1107_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
        v_fvarId_u2081_1104_,
        v_fvarId_u2082_1105_,
        v_a_1106_,
    );
    leanh::lean_dec(v_a_1106_);
    leanh::lean_dec(v_fvarId_u2082_1105_);
    leanh::lean_dec(v_fvarId_u2081_1104_);
    v_r_1108_ = leanh::lean_box((v_res_1107_) as usize);
    return v_r_1108_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0(
    mut v_00_u03b4_1109_: *mut leanh::LeanObject,
    mut v_t_1110_: *mut leanh::LeanObject,
    mut v_k_1111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1112_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0___redArg(v_t_1110_, v_k_1111_);
    return v___x_1112_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0___boxed(
    mut v_00_u03b4_1113_: *mut leanh::LeanObject,
    mut v_t_1114_: *mut leanh::LeanObject,
    mut v_k_1115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1116_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0(v_00_u03b4_1113_, v_t_1114_, v_k_1115_);
    leanh::lean_dec(v_k_1115_);
    leanh::lean_dec(v_t_1114_);
    return v_res_1116_;
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_eqvType(
    mut v_e_u2081_1117_: *mut leanh::LeanObject,
    mut v_e_u2082_1118_: *mut leanh::LeanObject,
    mut v_a_1119_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fn_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: u8 = 0;
    let mut v___x_1126_: u8 = 0;
    let mut v_fvarId_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: u8 = 0;
    let mut v___x_1130_: u8 = 0;
    let mut v_binderType_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: u8 = 0;
    let mut v___x_1137_: u8 = 0;
    let mut v___x_1138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_u2081_1117_) {
                5 => {
                    if leanh::lean_obj_tag(v_e_u2082_1118_) == 5 {
                        v_fn_1120_ = leanh::lean_ctor_get(v_e_u2081_1117_, 0);
                        v_arg_1121_ = leanh::lean_ctor_get(v_e_u2081_1117_, 1);
                        v_fn_1122_ = leanh::lean_ctor_get(v_e_u2082_1118_, 0);
                        v_arg_1123_ = leanh::lean_ctor_get(v_e_u2082_1118_, 1);
                        v___x_1124_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(
                            v_arg_1121_,
                            v_arg_1123_,
                            v_a_1119_,
                        );
                        if v___x_1124_ == 0 {
                            return v___x_1124_;
                        } else {
                            v_e_u2081_1117_ = v_fn_1120_;
                            v_e_u2082_1118_ = v_fn_1122_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_1126_ = lean_expr_eqv(v_e_u2081_1117_, v_e_u2082_1118_);
                        return v___x_1126_;
                    }
                }
                1 => {
                    if leanh::lean_obj_tag(v_e_u2082_1118_) == 1 {
                        v_fvarId_1127_ = leanh::lean_ctor_get(v_e_u2081_1117_, 0);
                        v_fvarId_1128_ = leanh::lean_ctor_get(v_e_u2082_1118_, 0);
                        v___x_1129_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                            v_fvarId_1127_,
                            v_fvarId_1128_,
                            v_a_1119_,
                        );
                        return v___x_1129_;
                    } else {
                        v___x_1130_ = lean_expr_eqv(v_e_u2081_1117_, v_e_u2082_1118_);
                        return v___x_1130_;
                    }
                }
                7 => {
                    if leanh::lean_obj_tag(v_e_u2082_1118_) == 7 {
                        v_binderType_1131_ = leanh::lean_ctor_get(v_e_u2081_1117_, 1);
                        v_body_1132_ = leanh::lean_ctor_get(v_e_u2081_1117_, 2);
                        v_binderType_1133_ = leanh::lean_ctor_get(v_e_u2082_1118_, 1);
                        v_body_1134_ = leanh::lean_ctor_get(v_e_u2082_1118_, 2);
                        v___x_1135_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(
                            v_binderType_1131_,
                            v_binderType_1133_,
                            v_a_1119_,
                        );
                        if v___x_1135_ == 0 {
                            return v___x_1135_;
                        } else {
                            v_e_u2081_1117_ = v_body_1132_;
                            v_e_u2082_1118_ = v_body_1134_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_1137_ = lean_expr_eqv(v_e_u2081_1117_, v_e_u2082_1118_);
                        return v___x_1137_;
                    }
                }
                _ => {
                    v___x_1138_ = lean_expr_eqv(v_e_u2081_1117_, v_e_u2082_1118_);
                    return v___x_1138_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_eqvType___boxed(
    mut v_e_u2081_1139_: *mut leanh::LeanObject,
    mut v_e_u2082_1140_: *mut leanh::LeanObject,
    mut v_a_1141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1142_: u8 = 0;
    let mut v_r_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1142_ =
        l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_e_u2081_1139_, v_e_u2082_1140_, v_a_1141_);
    leanh::lean_dec(v_a_1141_);
    leanh::lean_dec_ref(v_e_u2082_1140_);
    leanh::lean_dec_ref(v_e_u2081_1139_);
    v_r_1143_ = leanh::lean_box((v_res_1142_) as usize);
    return v_r_1143_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvTypes_spec__0(
    mut v_as_1144_: *mut leanh::LeanObject,
    mut v_sz_1145_: usize,
    mut v_i_1146_: usize,
    mut v_b_1147_: *mut leanh::LeanObject,
    mut v___y_1148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1149_: u8 = 0;
    let mut v_snd_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1153_: u8 = 0;
    let mut v_array_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: u8 = 0;
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1164_: u8 = 0;
    let mut v_a_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: u8 = 0;
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: usize = 0;
    let mut v___x_1180_: usize = 0;
    let mut v_reuseFailAlloc_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1184_: u8 = 0;
    let mut v_unused_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1188_: u8 = 0;
    let mut v_unused_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1149_ = lean_usize_dec_lt(v_i_1146_, v_sz_1145_);
                if v___x_1149_ == 0 {
                    return v_b_1147_;
                } else {
                    v_snd_1150_ = leanh::lean_ctor_get(v_b_1147_, 1);
                    v_isSharedCheck_1188_ = (!leanh::lean_is_exclusive(v_b_1147_)) as u8;
                    if v_isSharedCheck_1188_ == 0 {
                        v_unused_1189_ = leanh::lean_ctor_get(v_b_1147_, 0);
                        leanh::lean_dec(v_unused_1189_);
                        v___x_1152_ = v_b_1147_;
                        v_isShared_1153_ = v_isSharedCheck_1188_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1150_);
                        leanh::lean_dec(v_b_1147_);
                        v___x_1152_ = leanh::lean_box(0);
                        v_isShared_1153_ = v_isSharedCheck_1188_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_array_1154_ = leanh::lean_ctor_get(v_snd_1150_, 0);
                v_start_1155_ = leanh::lean_ctor_get(v_snd_1150_, 1);
                v_stop_1156_ = leanh::lean_ctor_get(v_snd_1150_, 2);
                v___x_1157_ = leanh::lean_box(0);
                v___x_1158_ = lean_nat_dec_lt(v_start_1155_, v_stop_1156_);
                if v___x_1158_ == 0 {
                    if v_isShared_1153_ == 0 {
                        leanh::lean_ctor_set(v___x_1152_, 0, v___x_1157_);
                        v___x_1160_ = v___x_1152_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1161_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1157_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_snd_1150_);
                        v___x_1160_ = v_reuseFailAlloc_1161_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_stop_1156_);
                    leanh::lean_inc(v_start_1155_);
                    leanh::lean_inc_ref(v_array_1154_);
                    v_isSharedCheck_1184_ = (!leanh::lean_is_exclusive(v_snd_1150_)) as u8;
                    if v_isSharedCheck_1184_ == 0 {
                        v_unused_1185_ = leanh::lean_ctor_get(v_snd_1150_, 2);
                        leanh::lean_dec(v_unused_1185_);
                        v_unused_1186_ = leanh::lean_ctor_get(v_snd_1150_, 1);
                        leanh::lean_dec(v_unused_1186_);
                        v_unused_1187_ = leanh::lean_ctor_get(v_snd_1150_, 0);
                        leanh::lean_dec(v_unused_1187_);
                        v___x_1163_ = v_snd_1150_;
                        v_isShared_1164_ = v_isSharedCheck_1184_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_snd_1150_);
                        v___x_1163_ = leanh::lean_box(0);
                        v_isShared_1164_ = v_isSharedCheck_1184_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1160_;
            }
            3 => {
                v_a_1165_ = lean_array_uget_borrowed(v_as_1144_, v_i_1146_);
                v___x_1166_ = lean_array_fget(v_array_1154_, v_start_1155_);
                v___x_1167_ = leanh::lean_unsigned_to_nat(1);
                v___x_1168_ = lean_nat_add(v_start_1155_, v___x_1167_);
                leanh::lean_dec(v_start_1155_);
                if v_isShared_1164_ == 0 {
                    leanh::lean_ctor_set(v___x_1163_, 1, v___x_1168_);
                    v___x_1170_ = v___x_1163_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1183_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_array_1154_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 1, v___x_1168_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 2, v_stop_1156_);
                    v___x_1170_ = v_reuseFailAlloc_1183_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1171_ =
                    l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_a_1165_, v___x_1166_, v___y_1148_);
                leanh::lean_dec(v___x_1166_);
                if v___x_1171_ == 0 {
                    v___x_1172_ = leanh::lean_box((v___x_1171_) as usize);
                    v___x_1173_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1173_, 0, v___x_1172_);
                    if v_isShared_1153_ == 0 {
                        leanh::lean_ctor_set(v___x_1152_, 1, v___x_1170_);
                        leanh::lean_ctor_set(v___x_1152_, 0, v___x_1173_);
                        v___x_1175_ = v___x_1152_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1176_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1176_, 1, v___x_1170_);
                        v___x_1175_ = v_reuseFailAlloc_1176_;
                        state = 5;
                        continue;
                    }
                } else {
                    if v_isShared_1153_ == 0 {
                        leanh::lean_ctor_set(v___x_1152_, 1, v___x_1170_);
                        leanh::lean_ctor_set(v___x_1152_, 0, v___x_1157_);
                        v___x_1178_ = v___x_1152_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1182_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1157_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1182_, 1, v___x_1170_);
                        v___x_1178_ = v_reuseFailAlloc_1182_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_1175_;
            }
            6 => {
                v___x_1179_ = 1usize;
                v___x_1180_ = lean_usize_add(v_i_1146_, v___x_1179_);
                v_i_1146_ = v___x_1180_;
                v_b_1147_ = v___x_1178_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvTypes_spec__0___boxed(
    mut v_as_1190_: *mut leanh::LeanObject,
    mut v_sz_1191_: *mut leanh::LeanObject,
    mut v_i_1192_: *mut leanh::LeanObject,
    mut v_b_1193_: *mut leanh::LeanObject,
    mut v___y_1194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1195_: usize = 0;
    let mut v_i_boxed_1196_: usize = 0;
    let mut v_res_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1195_ = leanh::lean_unbox_usize(v_sz_1191_);
    leanh::lean_dec(v_sz_1191_);
    v_i_boxed_1196_ = leanh::lean_unbox_usize(v_i_1192_);
    leanh::lean_dec(v_i_1192_);
    v_res_1197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvTypes_spec__0(v_as_1190_, v_sz_boxed_1195_, v_i_boxed_1196_, v_b_1193_, v___y_1194_);
    leanh::lean_dec(v___y_1194_);
    leanh::lean_dec_ref(v_as_1190_);
    return v_res_1197_;
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_eqvTypes(
    mut v_es_u2081_1198_: *mut leanh::LeanObject,
    mut v_es_u2082_1199_: *mut leanh::LeanObject,
    mut v_a_1200_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: u8 = 0;
    v___x_1201_ = lean_array_get_size(v_es_u2081_1198_);
    v___x_1202_ = lean_array_get_size(v_es_u2082_1199_);
    v___x_1203_ = lean_nat_dec_eq(v___x_1201_, v___x_1202_);
    if v___x_1203_ == 0 {
        leanh::lean_dec_ref(v_es_u2082_1199_);
        return v___x_1203_;
    } else {
        let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_1208_: usize = 0;
        let mut v___x_1209_: usize = 0;
        let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1204_ = leanh::lean_unsigned_to_nat(0);
        v___x_1205_ = l_Array_toSubarray___redArg(v_es_u2082_1199_, v___x_1204_, v___x_1202_);
        v___x_1206_ = leanh::lean_box(0);
        v___x_1207_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1207_, 0, v___x_1206_);
        leanh::lean_ctor_set(v___x_1207_, 1, v___x_1205_);
        v_sz_1208_ = lean_array_size(v_es_u2081_1198_);
        v___x_1209_ = 0usize;
        v___x_1210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvTypes_spec__0(v_es_u2081_1198_, v_sz_1208_, v___x_1209_, v___x_1207_, v_a_1200_);
        v_fst_1211_ = leanh::lean_ctor_get(v___x_1210_, 0);
        leanh::lean_inc(v_fst_1211_);
        leanh::lean_dec_ref(v___x_1210_);
        if leanh::lean_obj_tag(v_fst_1211_) == 0 {
            return v___x_1203_;
        } else {
            let mut v_val_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1213_: u8 = 0;
            v_val_1212_ = leanh::lean_ctor_get(v_fst_1211_, 0);
            leanh::lean_inc(v_val_1212_);
            leanh::lean_dec_ref_known(v_fst_1211_, 1);
            v___x_1213_ = (leanh::lean_unbox(v_val_1212_) as u8);
            leanh::lean_dec(v_val_1212_);
            return v___x_1213_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_eqvTypes___boxed(
    mut v_es_u2081_1214_: *mut leanh::LeanObject,
    mut v_es_u2082_1215_: *mut leanh::LeanObject,
    mut v_a_1216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1217_: u8 = 0;
    let mut v_r_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1217_ =
        l_Lean_Compiler_LCNF_AlphaEqv_eqvTypes(v_es_u2081_1214_, v_es_u2082_1215_, v_a_1216_);
    leanh::lean_dec(v_a_1216_);
    leanh::lean_dec_ref(v_es_u2081_1214_);
    v_r_1218_ = leanh::lean_box((v_res_1217_) as usize);
    return v_r_1218_;
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(
    mut v_a_u2081_1219_: *mut leanh::LeanObject,
    mut v_a_u2082_1220_: *mut leanh::LeanObject,
    mut v_a_1221_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_a_u2081_1219_) {
        0 => {
            if leanh::lean_obj_tag(v_a_u2082_1220_) == 0 {
                let mut v___x_1222_: u8 = 0;
                v___x_1222_ = 1;
                return v___x_1222_;
            } else {
                let mut v___x_1223_: u8 = 0;
                v___x_1223_ = 0;
                return v___x_1223_;
            }
        }
        1 => {
            if leanh::lean_obj_tag(v_a_u2082_1220_) == 1 {
                let mut v_fvarId_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_fvarId_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1226_: u8 = 0;
                v_fvarId_1224_ = leanh::lean_ctor_get(v_a_u2081_1219_, 0);
                v_fvarId_1225_ = leanh::lean_ctor_get(v_a_u2082_1220_, 0);
                v___x_1226_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                    v_fvarId_1224_,
                    v_fvarId_1225_,
                    v_a_1221_,
                );
                return v___x_1226_;
            } else {
                let mut v___x_1227_: u8 = 0;
                v___x_1227_ = 0;
                return v___x_1227_;
            }
        }
        _ => {
            if leanh::lean_obj_tag(v_a_u2082_1220_) == 2 {
                let mut v_expr_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_expr_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1230_: u8 = 0;
                v_expr_1228_ = leanh::lean_ctor_get(v_a_u2081_1219_, 0);
                v_expr_1229_ = leanh::lean_ctor_get(v_a_u2082_1220_, 0);
                v___x_1230_ =
                    l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_expr_1228_, v_expr_1229_, v_a_1221_);
                return v___x_1230_;
            } else {
                let mut v___x_1231_: u8 = 0;
                v___x_1231_ = 0;
                return v___x_1231_;
            }
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg___boxed(
    mut v_a_u2081_1232_: *mut leanh::LeanObject,
    mut v_a_u2082_1233_: *mut leanh::LeanObject,
    mut v_a_1234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1235_: u8 = 0;
    let mut v_r_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1235_ =
        l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(v_a_u2081_1232_, v_a_u2082_1233_, v_a_1234_);
    leanh::lean_dec(v_a_1234_);
    leanh::lean_dec(v_a_u2082_1233_);
    leanh::lean_dec(v_a_u2081_1232_);
    v_r_1236_ = leanh::lean_box((v_res_1235_) as usize);
    return v_r_1236_;
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_eqvArg(
    mut v_pu_1237_: u8,
    mut v_a_u2081_1238_: *mut leanh::LeanObject,
    mut v_a_u2082_1239_: *mut leanh::LeanObject,
    mut v_a_1240_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1241_: u8 = 0;
    v___x_1241_ =
        l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(v_a_u2081_1238_, v_a_u2082_1239_, v_a_1240_);
    return v___x_1241_;
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___boxed(
    mut v_pu_1242_: *mut leanh::LeanObject,
    mut v_a_u2081_1243_: *mut leanh::LeanObject,
    mut v_a_u2082_1244_: *mut leanh::LeanObject,
    mut v_a_1245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1246_: u8 = 0;
    let mut v_res_1247_: u8 = 0;
    let mut v_r_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1246_ = (leanh::lean_unbox(v_pu_1242_) as u8);
    v_res_1247_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg(
        v_pu_boxed_1246_,
        v_a_u2081_1243_,
        v_a_u2082_1244_,
        v_a_1245_,
    );
    leanh::lean_dec(v_a_1245_);
    leanh::lean_dec(v_a_u2082_1244_);
    leanh::lean_dec(v_a_u2081_1243_);
    v_r_1248_ = leanh::lean_box((v_res_1247_) as usize);
    return v_r_1248_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg(
    mut v_as_1249_: *mut leanh::LeanObject,
    mut v_sz_1250_: usize,
    mut v_i_1251_: usize,
    mut v_b_1252_: *mut leanh::LeanObject,
    mut v___y_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1254_: u8 = 0;
    let mut v_snd_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1258_: u8 = 0;
    let mut v_array_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: u8 = 0;
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1269_: u8 = 0;
    let mut v_a_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: u8 = 0;
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: usize = 0;
    let mut v___x_1285_: usize = 0;
    let mut v_reuseFailAlloc_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1289_: u8 = 0;
    let mut v_unused_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1293_: u8 = 0;
    let mut v_unused_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1254_ = lean_usize_dec_lt(v_i_1251_, v_sz_1250_);
                if v___x_1254_ == 0 {
                    return v_b_1252_;
                } else {
                    v_snd_1255_ = leanh::lean_ctor_get(v_b_1252_, 1);
                    v_isSharedCheck_1293_ = (!leanh::lean_is_exclusive(v_b_1252_)) as u8;
                    if v_isSharedCheck_1293_ == 0 {
                        v_unused_1294_ = leanh::lean_ctor_get(v_b_1252_, 0);
                        leanh::lean_dec(v_unused_1294_);
                        v___x_1257_ = v_b_1252_;
                        v_isShared_1258_ = v_isSharedCheck_1293_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1255_);
                        leanh::lean_dec(v_b_1252_);
                        v___x_1257_ = leanh::lean_box(0);
                        v_isShared_1258_ = v_isSharedCheck_1293_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_array_1259_ = leanh::lean_ctor_get(v_snd_1255_, 0);
                v_start_1260_ = leanh::lean_ctor_get(v_snd_1255_, 1);
                v_stop_1261_ = leanh::lean_ctor_get(v_snd_1255_, 2);
                v___x_1262_ = leanh::lean_box(0);
                v___x_1263_ = lean_nat_dec_lt(v_start_1260_, v_stop_1261_);
                if v___x_1263_ == 0 {
                    if v_isShared_1258_ == 0 {
                        leanh::lean_ctor_set(v___x_1257_, 0, v___x_1262_);
                        v___x_1265_ = v___x_1257_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1266_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1262_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_snd_1255_);
                        v___x_1265_ = v_reuseFailAlloc_1266_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_stop_1261_);
                    leanh::lean_inc(v_start_1260_);
                    leanh::lean_inc_ref(v_array_1259_);
                    v_isSharedCheck_1289_ = (!leanh::lean_is_exclusive(v_snd_1255_)) as u8;
                    if v_isSharedCheck_1289_ == 0 {
                        v_unused_1290_ = leanh::lean_ctor_get(v_snd_1255_, 2);
                        leanh::lean_dec(v_unused_1290_);
                        v_unused_1291_ = leanh::lean_ctor_get(v_snd_1255_, 1);
                        leanh::lean_dec(v_unused_1291_);
                        v_unused_1292_ = leanh::lean_ctor_get(v_snd_1255_, 0);
                        leanh::lean_dec(v_unused_1292_);
                        v___x_1268_ = v_snd_1255_;
                        v_isShared_1269_ = v_isSharedCheck_1289_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_snd_1255_);
                        v___x_1268_ = leanh::lean_box(0);
                        v_isShared_1269_ = v_isSharedCheck_1289_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1265_;
            }
            3 => {
                v_a_1270_ = lean_array_uget_borrowed(v_as_1249_, v_i_1251_);
                v___x_1271_ = lean_array_fget(v_array_1259_, v_start_1260_);
                v___x_1272_ = leanh::lean_unsigned_to_nat(1);
                v___x_1273_ = lean_nat_add(v_start_1260_, v___x_1272_);
                leanh::lean_dec(v_start_1260_);
                if v_isShared_1269_ == 0 {
                    leanh::lean_ctor_set(v___x_1268_, 1, v___x_1273_);
                    v___x_1275_ = v___x_1268_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1288_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_array_1259_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1288_, 1, v___x_1273_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1288_, 2, v_stop_1261_);
                    v___x_1275_ = v_reuseFailAlloc_1288_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1276_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(
                    v_a_1270_,
                    v___x_1271_,
                    v___y_1253_,
                );
                leanh::lean_dec(v___x_1271_);
                if v___x_1276_ == 0 {
                    v___x_1277_ = leanh::lean_box((v___x_1276_) as usize);
                    v___x_1278_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1278_, 0, v___x_1277_);
                    if v_isShared_1258_ == 0 {
                        leanh::lean_ctor_set(v___x_1257_, 1, v___x_1275_);
                        leanh::lean_ctor_set(v___x_1257_, 0, v___x_1278_);
                        v___x_1280_ = v___x_1257_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1281_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1281_, 1, v___x_1275_);
                        v___x_1280_ = v_reuseFailAlloc_1281_;
                        state = 5;
                        continue;
                    }
                } else {
                    if v_isShared_1258_ == 0 {
                        leanh::lean_ctor_set(v___x_1257_, 1, v___x_1275_);
                        leanh::lean_ctor_set(v___x_1257_, 0, v___x_1262_);
                        v___x_1283_ = v___x_1257_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1287_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1262_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 1, v___x_1275_);
                        v___x_1283_ = v_reuseFailAlloc_1287_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_1280_;
            }
            6 => {
                v___x_1284_ = 1usize;
                v___x_1285_ = lean_usize_add(v_i_1251_, v___x_1284_);
                v_i_1251_ = v___x_1285_;
                v_b_1252_ = v___x_1283_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg___boxed(
    mut v_as_1295_: *mut leanh::LeanObject,
    mut v_sz_1296_: *mut leanh::LeanObject,
    mut v_i_1297_: *mut leanh::LeanObject,
    mut v_b_1298_: *mut leanh::LeanObject,
    mut v___y_1299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1300_: usize = 0;
    let mut v_i_boxed_1301_: usize = 0;
    let mut v_res_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1300_ = leanh::lean_unbox_usize(v_sz_1296_);
    leanh::lean_dec(v_sz_1296_);
    v_i_boxed_1301_ = leanh::lean_unbox_usize(v_i_1297_);
    leanh::lean_dec(v_i_1297_);
    v_res_1302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg(v_as_1295_, v_sz_boxed_1300_, v_i_boxed_1301_, v_b_1298_, v___y_1299_);
    leanh::lean_dec(v___y_1299_);
    leanh::lean_dec_ref(v_as_1295_);
    return v_res_1302_;
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(
    mut v_pu_1303_: u8,
    mut v_as_u2081_1304_: *mut leanh::LeanObject,
    mut v_as_u2082_1305_: *mut leanh::LeanObject,
    mut v_a_1306_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: u8 = 0;
    v___x_1307_ = lean_array_get_size(v_as_u2081_1304_);
    v___x_1308_ = lean_array_get_size(v_as_u2082_1305_);
    v___x_1309_ = lean_nat_dec_eq(v___x_1307_, v___x_1308_);
    if v___x_1309_ == 0 {
        leanh::lean_dec_ref(v_as_u2082_1305_);
        return v___x_1309_;
    } else {
        let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_1314_: usize = 0;
        let mut v___x_1315_: usize = 0;
        let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1310_ = leanh::lean_unsigned_to_nat(0);
        v___x_1311_ = l_Array_toSubarray___redArg(v_as_u2082_1305_, v___x_1310_, v___x_1308_);
        v___x_1312_ = leanh::lean_box(0);
        v___x_1313_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1313_, 0, v___x_1312_);
        leanh::lean_ctor_set(v___x_1313_, 1, v___x_1311_);
        v_sz_1314_ = lean_array_size(v_as_u2081_1304_);
        v___x_1315_ = 0usize;
        v___x_1316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg(v_as_u2081_1304_, v_sz_1314_, v___x_1315_, v___x_1313_, v_a_1306_);
        v_fst_1317_ = leanh::lean_ctor_get(v___x_1316_, 0);
        leanh::lean_inc(v_fst_1317_);
        leanh::lean_dec_ref(v___x_1316_);
        if leanh::lean_obj_tag(v_fst_1317_) == 0 {
            return v___x_1309_;
        } else {
            let mut v_val_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1319_: u8 = 0;
            v_val_1318_ = leanh::lean_ctor_get(v_fst_1317_, 0);
            leanh::lean_inc(v_val_1318_);
            leanh::lean_dec_ref_known(v_fst_1317_, 1);
            v___x_1319_ = (leanh::lean_unbox(v_val_1318_) as u8);
            leanh::lean_dec(v_val_1318_);
            return v___x_1319_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs___boxed(
    mut v_pu_1320_: *mut leanh::LeanObject,
    mut v_as_u2081_1321_: *mut leanh::LeanObject,
    mut v_as_u2082_1322_: *mut leanh::LeanObject,
    mut v_a_1323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1324_: u8 = 0;
    let mut v_res_1325_: u8 = 0;
    let mut v_r_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1324_ = (leanh::lean_unbox(v_pu_1320_) as u8);
    v_res_1325_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(
        v_pu_boxed_1324_,
        v_as_u2081_1321_,
        v_as_u2082_1322_,
        v_a_1323_,
    );
    leanh::lean_dec(v_a_1323_);
    leanh::lean_dec_ref(v_as_u2081_1321_);
    v_r_1326_ = leanh::lean_box((v_res_1325_) as usize);
    return v_r_1326_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0(
    mut v_pu_1327_: u8,
    mut v_as_1328_: *mut leanh::LeanObject,
    mut v_sz_1329_: usize,
    mut v_i_1330_: usize,
    mut v_b_1331_: *mut leanh::LeanObject,
    mut v___y_1332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg(v_as_1328_, v_sz_1329_, v_i_1330_, v_b_1331_, v___y_1332_);
    return v___x_1333_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___boxed(
    mut v_pu_1334_: *mut leanh::LeanObject,
    mut v_as_1335_: *mut leanh::LeanObject,
    mut v_sz_1336_: *mut leanh::LeanObject,
    mut v_i_1337_: *mut leanh::LeanObject,
    mut v_b_1338_: *mut leanh::LeanObject,
    mut v___y_1339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1340_: u8 = 0;
    let mut v_sz_boxed_1341_: usize = 0;
    let mut v_i_boxed_1342_: usize = 0;
    let mut v_res_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1340_ = (leanh::lean_unbox(v_pu_1334_) as u8);
    v_sz_boxed_1341_ = leanh::lean_unbox_usize(v_sz_1336_);
    leanh::lean_dec(v_sz_1336_);
    v_i_boxed_1342_ = leanh::lean_unbox_usize(v_i_1337_);
    leanh::lean_dec(v_i_1337_);
    v_res_1343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0(v_pu_boxed_1340_, v_as_1335_, v_sz_boxed_1341_, v_i_boxed_1342_, v_b_1338_, v___y_1339_);
    leanh::lean_dec(v___y_1339_);
    leanh::lean_dec_ref(v_as_1335_);
    return v_res_1343_;
}
pub unsafe fn l_List_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqvLetValue_spec__0(
    mut v_x_1344_: *mut leanh::LeanObject,
    mut v_x_1345_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1346_: u8 = 0;
    let mut v___x_1347_: u8 = 0;
    let mut v___x_1348_: u8 = 0;
    let mut v_head_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1344_) == 0 {
                    if leanh::lean_obj_tag(v_x_1345_) == 0 {
                        v___x_1346_ = 1;
                        return v___x_1346_;
                    } else {
                        v___x_1347_ = 0;
                        return v___x_1347_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_x_1345_) == 0 {
                        v___x_1348_ = 0;
                        return v___x_1348_;
                    } else {
                        v_head_1349_ = leanh::lean_ctor_get(v_x_1344_, 0);
                        v_tail_1350_ = leanh::lean_ctor_get(v_x_1344_, 1);
                        v_head_1351_ = leanh::lean_ctor_get(v_x_1345_, 0);
                        v_tail_1352_ = leanh::lean_ctor_get(v_x_1345_, 1);
                        v___x_1353_ = lean_level_eq(v_head_1349_, v_head_1351_);
                        if v___x_1353_ == 0 {
                            return v___x_1353_;
                        } else {
                            v_x_1344_ = v_tail_1350_;
                            v_x_1345_ = v_tail_1352_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqvLetValue_spec__0___boxed(
    mut v_x_1355_: *mut leanh::LeanObject,
    mut v_x_1356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1357_: u8 = 0;
    let mut v_r_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1357_ =
        l_List_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqvLetValue_spec__0(v_x_1355_, v_x_1356_);
    leanh::lean_dec(v_x_1356_);
    leanh::lean_dec(v_x_1355_);
    v_r_1358_ = leanh::lean_box((v_res_1357_) as usize);
    return v_r_1358_;
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue(
    mut v_pu_1359_: u8,
    mut v_e_u2081_1360_: *mut leanh::LeanObject,
    mut v_e_u2082_1361_: *mut leanh::LeanObject,
    mut v_a_1362_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_i_u2081_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_u2081_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_u2082_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_u2082_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: u8 = 0;
    let mut v___x_1370_: u8 = 0;
    let mut v_f_u2081_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_as_u2081_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_u2082_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_as_u2082_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: u8 = 0;
    let mut v___x_1378_: u8 = 0;
    let mut v_value_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: u8 = 0;
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: u8 = 0;
    let mut v___x_1384_: u8 = 0;
    let mut v_typeName_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1392_: u8 = 0;
    let mut v___x_1393_: u8 = 0;
    let mut v___x_1394_: u8 = 0;
    let mut v___x_1395_: u8 = 0;
    let mut v___x_1396_: u8 = 0;
    let mut v_declName_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1404_: u8 = 0;
    let mut v___x_1405_: u8 = 0;
    let mut v___x_1406_: u8 = 0;
    let mut v___x_1407_: u8 = 0;
    let mut v___x_1408_: u8 = 0;
    let mut v_fvarId_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: u8 = 0;
    let mut v___x_1414_: u8 = 0;
    let mut v___x_1415_: u8 = 0;
    let mut v_i_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: u8 = 0;
    let mut v___x_1421_: u8 = 0;
    let mut v___x_1422_: u8 = 0;
    let mut v_i_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: u8 = 0;
    let mut v_i_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: u8 = 0;
    let mut v_n_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1440_: u8 = 0;
    let mut v___x_1441_: u8 = 0;
    let mut v___x_1442_: u8 = 0;
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1444_: u8 = 0;
    let mut v_fn_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    let mut v_fn_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: u8 = 0;
    let mut v_n_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: u8 = 0;
    let mut v_var_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_updateHeader_1462_: u8 = 0;
    let mut v_args_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_updateHeader_1466_: u8 = 0;
    let mut v_args_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1469_: u8 = 0;
    let mut v___x_1470_: u8 = 0;
    let mut v___x_1471_: u8 = 0;
    let mut v___x_1472_: u8 = 0;
    let mut v___x_1473_: u8 = 0;
    let mut v_ty_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: u8 = 0;
    let mut v___x_1479_: u8 = 0;
    let mut v___x_1480_: u8 = 0;
    let mut v_fvarId_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: u8 = 0;
    let mut v___x_1484_: u8 = 0;
    let mut v_fvarId_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: u8 = 0;
    let mut v___x_1488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_u2081_1360_) {
                0 => {
                    if leanh::lean_obj_tag(v_e_u2082_1361_) == 0 {
                        v_value_1379_ = leanh::lean_ctor_get(v_e_u2081_1360_, 0);
                        v_value_1380_ = leanh::lean_ctor_get(v_e_u2082_1361_, 0);
                        leanh::lean_inc_ref(v_value_1380_);
                        leanh::lean_dec_ref_known(v_e_u2082_1361_, 1);
                        v___x_1381_ =
                            l_Lean_Compiler_LCNF_instBEqLitValue_beq(v_value_1379_, v_value_1380_);
                        leanh::lean_dec_ref(v_value_1380_);
                        return v___x_1381_;
                    } else {
                        leanh::lean_dec(v_e_u2082_1361_);
                        v___x_1382_ = 0;
                        return v___x_1382_;
                    }
                }
                1 => {
                    if leanh::lean_obj_tag(v_e_u2082_1361_) == 1 {
                        v___x_1383_ = 1;
                        return v___x_1383_;
                    } else {
                        leanh::lean_dec(v_e_u2082_1361_);
                        v___x_1384_ = 0;
                        return v___x_1384_;
                    }
                }
                2 => {
                    if leanh::lean_obj_tag(v_e_u2082_1361_) == 2 {
                        v_typeName_1385_ = leanh::lean_ctor_get(v_e_u2081_1360_, 0);
                        v_idx_1386_ = leanh::lean_ctor_get(v_e_u2081_1360_, 1);
                        v_struct_1387_ = leanh::lean_ctor_get(v_e_u2081_1360_, 2);
                        v_typeName_1388_ = leanh::lean_ctor_get(v_e_u2082_1361_, 0);
                        leanh::lean_inc(v_typeName_1388_);
                        v_idx_1389_ = leanh::lean_ctor_get(v_e_u2082_1361_, 1);
                        leanh::lean_inc(v_idx_1389_);
                        v_struct_1390_ = leanh::lean_ctor_get(v_e_u2082_1361_, 2);
                        leanh::lean_inc(v_struct_1390_);
                        leanh::lean_dec_ref_known(v_e_u2082_1361_, 3);
                        v___x_1394_ = lean_name_eq(v_typeName_1385_, v_typeName_1388_);
                        leanh::lean_dec(v_typeName_1388_);
                        if v___x_1394_ == 0 {
                            leanh::lean_dec(v_idx_1389_);
                            v___y_1392_ = v___x_1394_;
                            state = 3;
                            continue;
                        } else {
                            v___x_1395_ = lean_nat_dec_eq(v_idx_1386_, v_idx_1389_);
                            leanh::lean_dec(v_idx_1389_);
                            v___y_1392_ = v___x_1395_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_e_u2082_1361_);
                        v___x_1396_ = 0;
                        return v___x_1396_;
                    }
                }
                3 => {
                    if leanh::lean_obj_tag(v_e_u2082_1361_) == 3 {
                        v_declName_1397_ = leanh::lean_ctor_get(v_e_u2081_1360_, 0);
                        v_us_1398_ = leanh::lean_ctor_get(v_e_u2081_1360_, 1);
                        v_args_1399_ = leanh::lean_ctor_get(v_e_u2081_1360_, 2);
                        v_declName_1400_ = leanh::lean_ctor_get(v_e_u2082_1361_, 0);
                        leanh::lean_inc(v_declName_1400_);
                        v_us_1401_ = leanh::lean_ctor_get(v_e_u2082_1361_, 1);
                        leanh::lean_inc(v_us_1401_);
                        v_args_1402_ = leanh::lean_ctor_get(v_e_u2082_1361_, 2);
                        leanh::lean_inc_ref(v_args_1402_);
                        leanh::lean_dec_ref_known(v_e_u2082_1361_, 3);
                        v___x_1406_ = lean_name_eq(v_declName_1397_, v_declName_1400_);
                        leanh::lean_dec(v_declName_1400_);
                        if v___x_1406_ == 0 {
                            leanh::lean_dec(v_us_1401_);
                            v___y_1404_ = v___x_1406_;
                            state = 4;
                            continue;
                        } else {
                            v___x_1407_ =
                                l_List_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqvLetValue_spec__0(
                                    v_us_1398_, v_us_1401_,
                                );
                            leanh::lean_dec(v_us_1401_);
                            v___y_1404_ = v___x_1407_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_e_u2082_1361_);
                        v___x_1408_ = 0;
                        return v___x_1408_;
                    }
                }
                4 => {
                    if leanh::lean_obj_tag(v_e_u2082_1361_) == 4 {
                        v_fvarId_1409_ = leanh::lean_ctor_get(v_e_u2081_1360_, 0);
                        v_args_1410_ = leanh::lean_ctor_get(v_e_u2081_1360_, 1);
                        v_fvarId_1411_ = leanh::lean_ctor_get(v_e_u2082_1361_, 0);
                        leanh::lean_inc(v_fvarId_1411_);
                        v_args_1412_ = leanh::lean_ctor_get(v_e_u2082_1361_, 1);
                        leanh::lean_inc_ref(v_args_1412_);
                        leanh::lean_dec_ref_known(v_e_u2082_1361_, 2);
                        v___x_1413_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                            v_fvarId_1409_,
                            v_fvarId_1411_,
                            v_a_1362_,
                        );
                        leanh::lean_dec(v_fvarId_1411_);
                        if v___x_1413_ == 0 {
                            leanh::lean_dec_ref(v_args_1412_);
                            return v___x_1413_;
                        } else {
                            v___x_1414_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(
                                v_pu_1359_,
                                v_args_1410_,
                                v_args_1412_,
                                v_a_1362_,
                            );
                            return v___x_1414_;
                        }
                    } else {
                        leanh::lean_dec(v_e_u2082_1361_);
                        v___x_1415_ = 0;
                        return v___x_1415_;
                    }
                }
                5 => {
                    if leanh::lean_obj_tag(v_e_u2082_1361_) == 5 {
                        v_i_1416_ = leanh::lean_ctor_get(v_e_u2081_1360_, 0);
                        v_args_1417_ = leanh::lean_ctor_get(v_e_u2081_1360_, 1);
                        v_i_1418_ = leanh::lean_ctor_get(v_e_u2082_1361_, 0);
                        leanh::lean_inc_ref(v_i_1418_);
                        v_args_1419_ = leanh::lean_ctor_get(v_e_u2082_1361_, 1);
                        leanh::lean_inc_ref(v_args_1419_);
                        leanh::lean_dec_ref_known(v_e_u2082_1361_, 2);
                        v___x_1420_ =
                            l_Lean_Compiler_LCNF_instBEqCtorInfo_beq(v_i_1416_, v_i_1418_);
                        leanh::lean_dec_ref(v_i_1418_);
                        if v___x_1420_ == 0 {
                            leanh::lean_dec_ref(v_args_1419_);
                            return v___x_1420_;
                        } else {
                            v___x_1421_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(
                                v_pu_1359_,
                                v_args_1417_,
                                v_args_1419_,
                                v_a_1362_,
                            );
                            return v___x_1421_;
                        }
                    } else {
                        leanh::lean_dec(v_e_u2082_1361_);
                        v___x_1422_ = 0;
                        return v___x_1422_;
                    }
                }
                6 => {
                    if leanh::lean_obj_tag(v_e_u2082_1361_) == 6 {
                        v_i_1423_ = leanh::lean_ctor_get(v_e_u2081_1360_, 0);
                        v_var_1424_ = leanh::lean_ctor_get(v_e_u2081_1360_, 1);
                        v_i_1425_ = leanh::lean_ctor_get(v_e_u2082_1361_, 0);
                        leanh::lean_inc(v_i_1425_);
                        v_var_1426_ = leanh::lean_ctor_get(v_e_u2082_1361_, 1);
                        leanh::lean_inc(v_var_1426_);
                        leanh::lean_dec_ref_known(v_e_u2082_1361_, 2);
                        v_i_u2081_1364_ = v_i_1423_;
                        v_v_u2081_1365_ = v_var_1424_;
                        v_i_u2082_1366_ = v_i_1425_;
                        v_v_u2082_1367_ = v_var_1426_;
                        v___y_1368_ = v_a_1362_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_e_u2082_1361_);
                        v___x_1427_ = 0;
                        return v___x_1427_;
                    }
                }
                7 => {
                    if leanh::lean_obj_tag(v_e_u2082_1361_) == 7 {
                        v_i_1428_ = leanh::lean_ctor_get(v_e_u2081_1360_, 0);
                        v_var_1429_ = leanh::lean_ctor_get(v_e_u2081_1360_, 1);
                        v_i_1430_ = leanh::lean_ctor_get(v_e_u2082_1361_, 0);
                        leanh::lean_inc(v_i_1430_);
                        v_var_1431_ = leanh::lean_ctor_get(v_e_u2082_1361_, 1);
                        leanh::lean_inc(v_var_1431_);
                        leanh::lean_dec_ref_known(v_e_u2082_1361_, 2);
                        v_i_u2081_1364_ = v_i_1428_;
                        v_v_u2081_1365_ = v_var_1429_;
                        v_i_u2082_1366_ = v_i_1430_;
                        v_v_u2082_1367_ = v_var_1431_;
                        v___y_1368_ = v_a_1362_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_e_u2082_1361_);
                        v___x_1432_ = 0;
                        return v___x_1432_;
                    }
                }
                8 => {
                    if leanh::lean_obj_tag(v_e_u2082_1361_) == 8 {
                        v_n_1433_ = leanh::lean_ctor_get(v_e_u2081_1360_, 0);
                        v_offset_1434_ = leanh::lean_ctor_get(v_e_u2081_1360_, 1);
                        v_var_1435_ = leanh::lean_ctor_get(v_e_u2081_1360_, 2);
                        v_n_1436_ = leanh::lean_ctor_get(v_e_u2082_1361_, 0);
                        leanh::lean_inc(v_n_1436_);
                        v_offset_1437_ = leanh::lean_ctor_get(v_e_u2082_1361_, 1);
                        leanh::lean_inc(v_offset_1437_);
                        v_var_1438_ = leanh::lean_ctor_get(v_e_u2082_1361_, 2);
                        leanh::lean_inc(v_var_1438_);
                        leanh::lean_dec_ref_known(v_e_u2082_1361_, 3);
                        v___x_1442_ = lean_nat_dec_eq(v_n_1433_, v_n_1436_);
                        leanh::lean_dec(v_n_1436_);
                        if v___x_1442_ == 0 {
                            leanh::lean_dec(v_offset_1437_);
                            v___y_1440_ = v___x_1442_;
                            state = 5;
                            continue;
                        } else {
                            v___x_1443_ = lean_nat_dec_eq(v_offset_1434_, v_offset_1437_);
                            leanh::lean_dec(v_offset_1437_);
                            v___y_1440_ = v___x_1443_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_e_u2082_1361_);
                        v___x_1444_ = 0;
                        return v___x_1444_;
                    }
                }
                9 => {
                    if leanh::lean_obj_tag(v_e_u2082_1361_) == 9 {
                        v_fn_1445_ = leanh::lean_ctor_get(v_e_u2081_1360_, 0);
                        v_args_1446_ = leanh::lean_ctor_get(v_e_u2081_1360_, 1);
                        v_fn_1447_ = leanh::lean_ctor_get(v_e_u2082_1361_, 0);
                        leanh::lean_inc(v_fn_1447_);
                        v_args_1448_ = leanh::lean_ctor_get(v_e_u2082_1361_, 1);
                        leanh::lean_inc_ref(v_args_1448_);
                        leanh::lean_dec_ref_known(v_e_u2082_1361_, 2);
                        v_f_u2081_1372_ = v_fn_1445_;
                        v_as_u2081_1373_ = v_args_1446_;
                        v_f_u2082_1374_ = v_fn_1447_;
                        v_as_u2082_1375_ = v_args_1448_;
                        v___y_1376_ = v_a_1362_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_e_u2082_1361_);
                        v___x_1449_ = 0;
                        return v___x_1449_;
                    }
                }
                10 => {
                    if leanh::lean_obj_tag(v_e_u2082_1361_) == 10 {
                        v_fn_1450_ = leanh::lean_ctor_get(v_e_u2081_1360_, 0);
                        v_args_1451_ = leanh::lean_ctor_get(v_e_u2081_1360_, 1);
                        v_fn_1452_ = leanh::lean_ctor_get(v_e_u2082_1361_, 0);
                        leanh::lean_inc(v_fn_1452_);
                        v_args_1453_ = leanh::lean_ctor_get(v_e_u2082_1361_, 1);
                        leanh::lean_inc_ref(v_args_1453_);
                        leanh::lean_dec_ref_known(v_e_u2082_1361_, 2);
                        v_f_u2081_1372_ = v_fn_1450_;
                        v_as_u2081_1373_ = v_args_1451_;
                        v_f_u2082_1374_ = v_fn_1452_;
                        v_as_u2082_1375_ = v_args_1453_;
                        v___y_1376_ = v_a_1362_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_e_u2082_1361_);
                        v___x_1454_ = 0;
                        return v___x_1454_;
                    }
                }
                11 => {
                    if leanh::lean_obj_tag(v_e_u2082_1361_) == 11 {
                        v_n_1455_ = leanh::lean_ctor_get(v_e_u2081_1360_, 0);
                        v_var_1456_ = leanh::lean_ctor_get(v_e_u2081_1360_, 1);
                        v_n_1457_ = leanh::lean_ctor_get(v_e_u2082_1361_, 0);
                        leanh::lean_inc(v_n_1457_);
                        v_var_1458_ = leanh::lean_ctor_get(v_e_u2082_1361_, 1);
                        leanh::lean_inc(v_var_1458_);
                        leanh::lean_dec_ref_known(v_e_u2082_1361_, 2);
                        v_i_u2081_1364_ = v_n_1455_;
                        v_v_u2081_1365_ = v_var_1456_;
                        v_i_u2082_1366_ = v_n_1457_;
                        v_v_u2082_1367_ = v_var_1458_;
                        v___y_1368_ = v_a_1362_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_e_u2082_1361_);
                        v___x_1459_ = 0;
                        return v___x_1459_;
                    }
                }
                12 => {
                    if leanh::lean_obj_tag(v_e_u2082_1361_) == 12 {
                        v_var_1460_ = leanh::lean_ctor_get(v_e_u2081_1360_, 0);
                        v_i_1461_ = leanh::lean_ctor_get(v_e_u2081_1360_, 1);
                        v_updateHeader_1462_ = leanh::lean_ctor_get_uint8(
                            v_e_u2081_1360_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v_args_1463_ = leanh::lean_ctor_get(v_e_u2081_1360_, 2);
                        v_var_1464_ = leanh::lean_ctor_get(v_e_u2082_1361_, 0);
                        leanh::lean_inc(v_var_1464_);
                        v_i_1465_ = leanh::lean_ctor_get(v_e_u2082_1361_, 1);
                        leanh::lean_inc_ref(v_i_1465_);
                        v_updateHeader_1466_ = leanh::lean_ctor_get_uint8(
                            v_e_u2082_1361_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v_args_1467_ = leanh::lean_ctor_get(v_e_u2082_1361_, 2);
                        leanh::lean_inc_ref(v_args_1467_);
                        leanh::lean_dec_ref_known(v_e_u2082_1361_, 3);
                        v___x_1472_ =
                            l_Lean_Compiler_LCNF_instBEqCtorInfo_beq(v_i_1461_, v_i_1465_);
                        leanh::lean_dec_ref(v_i_1465_);
                        if v___x_1472_ == 0 {
                            v___y_1469_ = v___x_1472_;
                            state = 6;
                            continue;
                        } else {
                            if v_updateHeader_1462_ == 0 {
                                if v_updateHeader_1466_ == 0 {
                                    v___y_1469_ = v___x_1472_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_args_1467_);
                                    leanh::lean_dec(v_var_1464_);
                                    return v_updateHeader_1462_;
                                }
                            } else {
                                v___y_1469_ = v_updateHeader_1466_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_e_u2082_1361_);
                        v___x_1473_ = 0;
                        return v___x_1473_;
                    }
                }
                13 => {
                    if leanh::lean_obj_tag(v_e_u2082_1361_) == 13 {
                        v_ty_1474_ = leanh::lean_ctor_get(v_e_u2081_1360_, 0);
                        v_fvarId_1475_ = leanh::lean_ctor_get(v_e_u2081_1360_, 1);
                        v_ty_1476_ = leanh::lean_ctor_get(v_e_u2082_1361_, 0);
                        leanh::lean_inc_ref(v_ty_1476_);
                        v_fvarId_1477_ = leanh::lean_ctor_get(v_e_u2082_1361_, 1);
                        leanh::lean_inc(v_fvarId_1477_);
                        leanh::lean_dec_ref_known(v_e_u2082_1361_, 2);
                        v___x_1478_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(
                            v_ty_1474_, v_ty_1476_, v_a_1362_,
                        );
                        leanh::lean_dec_ref(v_ty_1476_);
                        if v___x_1478_ == 0 {
                            leanh::lean_dec(v_fvarId_1477_);
                            return v___x_1478_;
                        } else {
                            v___x_1479_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                                v_fvarId_1475_,
                                v_fvarId_1477_,
                                v_a_1362_,
                            );
                            leanh::lean_dec(v_fvarId_1477_);
                            return v___x_1479_;
                        }
                    } else {
                        leanh::lean_dec(v_e_u2082_1361_);
                        v___x_1480_ = 0;
                        return v___x_1480_;
                    }
                }
                14 => {
                    if leanh::lean_obj_tag(v_e_u2082_1361_) == 14 {
                        v_fvarId_1481_ = leanh::lean_ctor_get(v_e_u2081_1360_, 0);
                        v_fvarId_1482_ = leanh::lean_ctor_get(v_e_u2082_1361_, 0);
                        leanh::lean_inc(v_fvarId_1482_);
                        leanh::lean_dec_ref_known(v_e_u2082_1361_, 1);
                        v___x_1483_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                            v_fvarId_1481_,
                            v_fvarId_1482_,
                            v_a_1362_,
                        );
                        leanh::lean_dec(v_fvarId_1482_);
                        return v___x_1483_;
                    } else {
                        leanh::lean_dec(v_e_u2082_1361_);
                        v___x_1484_ = 0;
                        return v___x_1484_;
                    }
                }
                _ => {
                    if leanh::lean_obj_tag(v_e_u2082_1361_) == 15 {
                        v_fvarId_1485_ = leanh::lean_ctor_get(v_e_u2081_1360_, 0);
                        v_fvarId_1486_ = leanh::lean_ctor_get(v_e_u2082_1361_, 0);
                        leanh::lean_inc(v_fvarId_1486_);
                        leanh::lean_dec_ref_known(v_e_u2082_1361_, 1);
                        v___x_1487_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                            v_fvarId_1485_,
                            v_fvarId_1486_,
                            v_a_1362_,
                        );
                        leanh::lean_dec(v_fvarId_1486_);
                        return v___x_1487_;
                    } else {
                        leanh::lean_dec(v_e_u2082_1361_);
                        v___x_1488_ = 0;
                        return v___x_1488_;
                    }
                }
            },
            1 => {
                v___x_1369_ = lean_nat_dec_eq(v_i_u2081_1364_, v_i_u2082_1366_);
                leanh::lean_dec(v_i_u2082_1366_);
                if v___x_1369_ == 0 {
                    leanh::lean_dec(v_v_u2082_1367_);
                    return v___x_1369_;
                } else {
                    v___x_1370_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                        v_v_u2081_1365_,
                        v_v_u2082_1367_,
                        v___y_1368_,
                    );
                    leanh::lean_dec(v_v_u2082_1367_);
                    return v___x_1370_;
                }
            }
            2 => {
                v___x_1377_ = lean_name_eq(v_f_u2081_1372_, v_f_u2082_1374_);
                leanh::lean_dec(v_f_u2082_1374_);
                if v___x_1377_ == 0 {
                    leanh::lean_dec_ref(v_as_u2082_1375_);
                    return v___x_1377_;
                } else {
                    v___x_1378_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(
                        v_pu_1359_,
                        v_as_u2081_1373_,
                        v_as_u2082_1375_,
                        v___y_1376_,
                    );
                    return v___x_1378_;
                }
            }
            3 => {
                if v___y_1392_ == 0 {
                    leanh::lean_dec(v_struct_1390_);
                    return v___y_1392_;
                } else {
                    v___x_1393_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                        v_struct_1387_,
                        v_struct_1390_,
                        v_a_1362_,
                    );
                    leanh::lean_dec(v_struct_1390_);
                    return v___x_1393_;
                }
            }
            4 => {
                if v___y_1404_ == 0 {
                    leanh::lean_dec_ref(v_args_1402_);
                    return v___y_1404_;
                } else {
                    v___x_1405_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(
                        v_pu_1359_,
                        v_args_1399_,
                        v_args_1402_,
                        v_a_1362_,
                    );
                    return v___x_1405_;
                }
            }
            5 => {
                if v___y_1440_ == 0 {
                    leanh::lean_dec(v_var_1438_);
                    return v___y_1440_;
                } else {
                    v___x_1441_ =
                        l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_var_1435_, v_var_1438_, v_a_1362_);
                    leanh::lean_dec(v_var_1438_);
                    return v___x_1441_;
                }
            }
            6 => {
                if v___y_1469_ == 0 {
                    leanh::lean_dec_ref(v_args_1467_);
                    leanh::lean_dec(v_var_1464_);
                    return v___y_1469_;
                } else {
                    v___x_1470_ =
                        l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_var_1460_, v_var_1464_, v_a_1362_);
                    leanh::lean_dec(v_var_1464_);
                    if v___x_1470_ == 0 {
                        leanh::lean_dec_ref(v_args_1467_);
                        return v___x_1470_;
                    } else {
                        v___x_1471_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(
                            v_pu_1359_,
                            v_args_1463_,
                            v_args_1467_,
                            v_a_1362_,
                        );
                        return v___x_1471_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue___boxed(
    mut v_pu_1489_: *mut leanh::LeanObject,
    mut v_e_u2081_1490_: *mut leanh::LeanObject,
    mut v_e_u2082_1491_: *mut leanh::LeanObject,
    mut v_a_1492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1493_: u8 = 0;
    let mut v_res_1494_: u8 = 0;
    let mut v_r_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1493_ = (leanh::lean_unbox(v_pu_1489_) as u8);
    v_res_1494_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue(
        v_pu_boxed_1493_,
        v_e_u2081_1490_,
        v_e_u2082_1491_,
        v_a_1492_,
    );
    leanh::lean_dec(v_a_1492_);
    leanh::lean_dec(v_e_u2081_1490_);
    v_r_1495_ = leanh::lean_box((v_res_1494_) as usize);
    return v_r_1495_;
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_withFVar___redArg(
    mut v_fvarId_u2081_1496_: *mut leanh::LeanObject,
    mut v_fvarId_u2082_1497_: *mut leanh::LeanObject,
    mut v_x_1498_: *mut leanh::LeanObject,
    mut v_a_1499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1499_);
    v___x_1500_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_u2082_1497_, v_fvarId_u2081_1496_, v_a_1499_);
    v___x_1501_ = leanh::lean_apply_1(v_x_1498_, v___x_1500_);
    return v___x_1501_;
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_withFVar___redArg___boxed(
    mut v_fvarId_u2081_1502_: *mut leanh::LeanObject,
    mut v_fvarId_u2082_1503_: *mut leanh::LeanObject,
    mut v_x_1504_: *mut leanh::LeanObject,
    mut v_a_1505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1506_ = l_Lean_Compiler_LCNF_AlphaEqv_withFVar___redArg(
        v_fvarId_u2081_1502_,
        v_fvarId_u2082_1503_,
        v_x_1504_,
        v_a_1505_,
    );
    leanh::lean_dec(v_a_1505_);
    return v_res_1506_;
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_withFVar(
    mut v_00_u03b1_1507_: *mut leanh::LeanObject,
    mut v_fvarId_u2081_1508_: *mut leanh::LeanObject,
    mut v_fvarId_u2082_1509_: *mut leanh::LeanObject,
    mut v_x_1510_: *mut leanh::LeanObject,
    mut v_a_1511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1511_);
    v___x_1512_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_u2082_1509_, v_fvarId_u2081_1508_, v_a_1511_);
    v___x_1513_ = leanh::lean_apply_1(v_x_1510_, v___x_1512_);
    return v___x_1513_;
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_withFVar___boxed(
    mut v_00_u03b1_1514_: *mut leanh::LeanObject,
    mut v_fvarId_u2081_1515_: *mut leanh::LeanObject,
    mut v_fvarId_u2082_1516_: *mut leanh::LeanObject,
    mut v_x_1517_: *mut leanh::LeanObject,
    mut v_a_1518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1519_ = l_Lean_Compiler_LCNF_AlphaEqv_withFVar(
        v_00_u03b1_1514_,
        v_fvarId_u2081_1515_,
        v_fvarId_u2082_1516_,
        v_x_1517_,
        v_a_1518_,
    );
    leanh::lean_dec(v_a_1518_);
    return v_res_1519_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(
    mut v_params_u2081_1520_: *mut leanh::LeanObject,
    mut v_params_u2082_1521_: *mut leanh::LeanObject,
    mut v_x_1522_: *mut leanh::LeanObject,
    mut v_i_1523_: *mut leanh::LeanObject,
    mut v_a_1524_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: u8 = 0;
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: u8 = 0;
    let mut v_p_u2081_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_u2082_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: u8 = 0;
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1525_ = lean_array_get_size(v_params_u2081_1520_);
                v___x_1526_ = lean_nat_dec_lt(v_i_1523_, v___x_1525_);
                if v___x_1526_ == 0 {
                    leanh::lean_dec(v_i_1523_);
                    v___x_1527_ = leanh::lean_apply_1(v_x_1522_, v_a_1524_);
                    v___x_1528_ = (leanh::lean_unbox(v___x_1527_) as u8);
                    return v___x_1528_;
                } else {
                    v_p_u2081_1529_ = lean_array_fget_borrowed(v_params_u2081_1520_, v_i_1523_);
                    v_fvarId_1530_ = leanh::lean_ctor_get(v_p_u2081_1529_, 0);
                    v_type_1531_ = leanh::lean_ctor_get(v_p_u2081_1529_, 2);
                    v_p_u2082_1532_ = lean_array_fget_borrowed(v_params_u2082_1521_, v_i_1523_);
                    v_fvarId_1533_ = leanh::lean_ctor_get(v_p_u2082_1532_, 0);
                    v_type_1534_ = leanh::lean_ctor_get(v_p_u2082_1532_, 2);
                    v___x_1535_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(
                        v_type_1531_,
                        v_type_1534_,
                        v_a_1524_,
                    );
                    if v___x_1535_ == 0 {
                        leanh::lean_dec(v_a_1524_);
                        leanh::lean_dec(v_i_1523_);
                        leanh::lean_dec_ref(v_x_1522_);
                        return v___x_1535_;
                    } else {
                        v___x_1536_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1537_ = lean_nat_add(v_i_1523_, v___x_1536_);
                        leanh::lean_dec(v_i_1523_);
                        leanh::lean_inc(v_fvarId_1530_);
                        leanh::lean_inc(v_fvarId_1533_);
                        v___x_1538_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1533_, v_fvarId_1530_, v_a_1524_);
                        v_i_1523_ = v___x_1537_;
                        v_a_1524_ = v___x_1538_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg___boxed(
    mut v_params_u2081_1540_: *mut leanh::LeanObject,
    mut v_params_u2082_1541_: *mut leanh::LeanObject,
    mut v_x_1542_: *mut leanh::LeanObject,
    mut v_i_1543_: *mut leanh::LeanObject,
    mut v_a_1544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1545_: u8 = 0;
    let mut v_r_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1545_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_1540_, v_params_u2082_1541_, v_x_1542_, v_i_1543_, v_a_1544_);
    leanh::lean_dec_ref(v_params_u2082_1541_);
    leanh::lean_dec_ref(v_params_u2081_1540_);
    v_r_1546_ = leanh::lean_box((v_res_1545_) as usize);
    return v_r_1546_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go(
    mut v_pu_1547_: u8,
    mut v_params_u2081_1548_: *mut leanh::LeanObject,
    mut v_params_u2082_1549_: *mut leanh::LeanObject,
    mut v_x_1550_: *mut leanh::LeanObject,
    mut v_h_1551_: *mut leanh::LeanObject,
    mut v_i_1552_: *mut leanh::LeanObject,
    mut v_a_1553_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1554_: u8 = 0;
    leanh::lean_inc(v_a_1553_);
    v___x_1554_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_1548_, v_params_u2082_1549_, v_x_1550_, v_i_1552_, v_a_1553_);
    return v___x_1554_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___boxed(
    mut v_pu_1555_: *mut leanh::LeanObject,
    mut v_params_u2081_1556_: *mut leanh::LeanObject,
    mut v_params_u2082_1557_: *mut leanh::LeanObject,
    mut v_x_1558_: *mut leanh::LeanObject,
    mut v_h_1559_: *mut leanh::LeanObject,
    mut v_i_1560_: *mut leanh::LeanObject,
    mut v_a_1561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1562_: u8 = 0;
    let mut v_res_1563_: u8 = 0;
    let mut v_r_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1562_ = (leanh::lean_unbox(v_pu_1555_) as u8);
    v_res_1563_ =
        l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go(
            v_pu_boxed_1562_,
            v_params_u2081_1556_,
            v_params_u2082_1557_,
            v_x_1558_,
            v_h_1559_,
            v_i_1560_,
            v_a_1561_,
        );
    leanh::lean_dec(v_a_1561_);
    leanh::lean_dec_ref(v_params_u2082_1557_);
    leanh::lean_dec_ref(v_params_u2081_1556_);
    v_r_1564_ = leanh::lean_box((v_res_1563_) as usize);
    return v_r_1564_;
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg(
    mut v_params_u2081_1565_: *mut leanh::LeanObject,
    mut v_params_u2082_1566_: *mut leanh::LeanObject,
    mut v_x_1567_: *mut leanh::LeanObject,
    mut v_a_1568_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    v___x_1569_ = lean_array_get_size(v_params_u2082_1566_);
    v___x_1570_ = lean_array_get_size(v_params_u2081_1565_);
    v___x_1571_ = lean_nat_dec_eq(v___x_1569_, v___x_1570_);
    if v___x_1571_ == 0 {
        leanh::lean_dec_ref(v_x_1567_);
        return v___x_1571_;
    } else {
        let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1573_: u8 = 0;
        v___x_1572_ = leanh::lean_unsigned_to_nat(0);
        leanh::lean_inc(v_a_1568_);
        v___x_1573_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_1565_, v_params_u2082_1566_, v_x_1567_, v___x_1572_, v_a_1568_);
        return v___x_1573_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg___boxed(
    mut v_params_u2081_1574_: *mut leanh::LeanObject,
    mut v_params_u2082_1575_: *mut leanh::LeanObject,
    mut v_x_1576_: *mut leanh::LeanObject,
    mut v_a_1577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1578_: u8 = 0;
    let mut v_r_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1578_ = l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg(
        v_params_u2081_1574_,
        v_params_u2082_1575_,
        v_x_1576_,
        v_a_1577_,
    );
    leanh::lean_dec(v_a_1577_);
    leanh::lean_dec_ref(v_params_u2082_1575_);
    leanh::lean_dec_ref(v_params_u2081_1574_);
    v_r_1579_ = leanh::lean_box((v_res_1578_) as usize);
    return v_r_1579_;
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_withParams(
    mut v_pu_1580_: u8,
    mut v_params_u2081_1581_: *mut leanh::LeanObject,
    mut v_params_u2082_1582_: *mut leanh::LeanObject,
    mut v_x_1583_: *mut leanh::LeanObject,
    mut v_a_1584_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: u8 = 0;
    v___x_1585_ = lean_array_get_size(v_params_u2082_1582_);
    v___x_1586_ = lean_array_get_size(v_params_u2081_1581_);
    v___x_1587_ = lean_nat_dec_eq(v___x_1585_, v___x_1586_);
    if v___x_1587_ == 0 {
        leanh::lean_dec_ref(v_x_1583_);
        return v___x_1587_;
    } else {
        let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1589_: u8 = 0;
        v___x_1588_ = leanh::lean_unsigned_to_nat(0);
        leanh::lean_inc(v_a_1584_);
        v___x_1589_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_1581_, v_params_u2082_1582_, v_x_1583_, v___x_1588_, v_a_1584_);
        return v___x_1589_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_withParams___boxed(
    mut v_pu_1590_: *mut leanh::LeanObject,
    mut v_params_u2081_1591_: *mut leanh::LeanObject,
    mut v_params_u2082_1592_: *mut leanh::LeanObject,
    mut v_x_1593_: *mut leanh::LeanObject,
    mut v_a_1594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1595_: u8 = 0;
    let mut v_res_1596_: u8 = 0;
    let mut v_r_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1595_ = (leanh::lean_unbox(v_pu_1590_) as u8);
    v_res_1596_ = l_Lean_Compiler_LCNF_AlphaEqv_withParams(
        v_pu_boxed_1595_,
        v_params_u2081_1591_,
        v_params_u2082_1592_,
        v_x_1593_,
        v_a_1594_,
    );
    leanh::lean_dec(v_a_1594_);
    leanh::lean_dec_ref(v_params_u2082_1592_);
    leanh::lean_dec_ref(v_params_u2081_1591_);
    v_r_1597_ = leanh::lean_box((v_res_1596_) as usize);
    return v_r_1597_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(
    mut v_hi_1598_: *mut leanh::LeanObject,
    mut v_pivot_1599_: *mut leanh::LeanObject,
    mut v_as_1600_: *mut leanh::LeanObject,
    mut v_i_1601_: *mut leanh::LeanObject,
    mut v_k_1602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1614_: u8 = 0;
    let mut v___x_1615_: u8 = 0;
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: u8 = 0;
    let mut v_info_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1615_ = lean_nat_dec_lt(v_k_1602_, v_hi_1598_);
                if v___x_1615_ == 0 {
                    leanh::lean_dec(v_k_1602_);
                    v___x_1616_ = lean_array_fswap(v_as_1600_, v_i_1601_, v_hi_1598_);
                    v___x_1617_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1617_, 0, v_i_1601_);
                    leanh::lean_ctor_set(v___x_1617_, 1, v___x_1616_);
                    return v___x_1617_;
                } else {
                    v___x_1618_ = lean_array_fget_borrowed(v_as_1600_, v_k_1602_);
                    match leanh::lean_obj_tag(v___x_1618_) {
                        0 => match leanh::lean_obj_tag(v_pivot_1599_) {
                            2 => {
                                state = 2;
                                continue;
                            }
                            0 => {
                                v_ctorName_1619_ = leanh::lean_ctor_get(v___x_1618_, 0);
                                v_ctorName_1620_ = leanh::lean_ctor_get(v_pivot_1599_, 0);
                                v___x_1621_ = l_Lean_Name_lt(v_ctorName_1619_, v_ctorName_1620_);
                                v___y_1614_ = v___x_1621_;
                                state = 3;
                                continue;
                            }
                            _ => {
                                state = 1;
                                continue;
                            }
                        },
                        1 => match leanh::lean_obj_tag(v_pivot_1599_) {
                            2 => {
                                state = 2;
                                continue;
                            }
                            1 => {
                                v_info_1622_ = leanh::lean_ctor_get(v___x_1618_, 0);
                                v_info_1623_ = leanh::lean_ctor_get(v_pivot_1599_, 0);
                                v_name_1624_ = leanh::lean_ctor_get(v_info_1622_, 0);
                                v_name_1625_ = leanh::lean_ctor_get(v_info_1623_, 0);
                                v___x_1626_ = l_Lean_Name_lt(v_name_1624_, v_name_1625_);
                                v___y_1614_ = v___x_1626_;
                                state = 3;
                                continue;
                            }
                            _ => {
                                state = 1;
                                continue;
                            }
                        },
                        _ => {
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1604_ = leanh::lean_unsigned_to_nat(1);
                v___x_1605_ = lean_nat_add(v_k_1602_, v___x_1604_);
                leanh::lean_dec(v_k_1602_);
                v_k_1602_ = v___x_1605_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1608_ = lean_array_fswap(v_as_1600_, v_i_1601_, v_k_1602_);
                v___x_1609_ = leanh::lean_unsigned_to_nat(1);
                v___x_1610_ = lean_nat_add(v_i_1601_, v___x_1609_);
                leanh::lean_dec(v_i_1601_);
                v___x_1611_ = lean_nat_add(v_k_1602_, v___x_1609_);
                leanh::lean_dec(v_k_1602_);
                v_as_1600_ = v___x_1608_;
                v_i_1601_ = v___x_1610_;
                v_k_1602_ = v___x_1611_;
                state = 0;
                continue;
            }
            3 => {
                if v___y_1614_ == 0 {
                    state = 1;
                    continue;
                } else {
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg___boxed(
    mut v_hi_1627_: *mut leanh::LeanObject,
    mut v_pivot_1628_: *mut leanh::LeanObject,
    mut v_as_1629_: *mut leanh::LeanObject,
    mut v_i_1630_: *mut leanh::LeanObject,
    mut v_k_1631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1632_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(v_hi_1627_, v_pivot_1628_, v_as_1629_, v_i_1630_, v_k_1631_);
    leanh::lean_dec_ref(v_pivot_1628_);
    leanh::lean_dec(v_hi_1627_);
    return v_res_1632_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(
    mut v___x_1633_: u8,
    mut v_x_1634_: *mut leanh::LeanObject,
    mut v_x_1635_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_x_1634_) {
        0 => match leanh::lean_obj_tag(v_x_1635_) {
            2 => {
                return v___x_1633_;
            }
            0 => {
                let mut v_ctorName_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ctorName_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1638_: u8 = 0;
                v_ctorName_1636_ = leanh::lean_ctor_get(v_x_1634_, 0);
                v_ctorName_1637_ = leanh::lean_ctor_get(v_x_1635_, 0);
                v___x_1638_ = l_Lean_Name_lt(v_ctorName_1636_, v_ctorName_1637_);
                return v___x_1638_;
            }
            _ => {
                let mut v___x_1639_: u8 = 0;
                v___x_1639_ = 0;
                return v___x_1639_;
            }
        },
        1 => match leanh::lean_obj_tag(v_x_1635_) {
            2 => {
                return v___x_1633_;
            }
            1 => {
                let mut v_info_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_info_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_name_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_name_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1644_: u8 = 0;
                v_info_1640_ = leanh::lean_ctor_get(v_x_1634_, 0);
                v_info_1641_ = leanh::lean_ctor_get(v_x_1635_, 0);
                v_name_1642_ = leanh::lean_ctor_get(v_info_1640_, 0);
                v_name_1643_ = leanh::lean_ctor_get(v_info_1641_, 0);
                v___x_1644_ = l_Lean_Name_lt(v_name_1642_, v_name_1643_);
                return v___x_1644_;
            }
            _ => {
                let mut v___x_1645_: u8 = 0;
                v___x_1645_ = 0;
                return v___x_1645_;
            }
        },
        _ => {
            let mut v___x_1646_: u8 = 0;
            v___x_1646_ = 0;
            return v___x_1646_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0___boxed(
    mut v___x_1647_: *mut leanh::LeanObject,
    mut v_x_1648_: *mut leanh::LeanObject,
    mut v_x_1649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_429__boxed_1650_: u8 = 0;
    let mut v_res_1651_: u8 = 0;
    let mut v_r_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_429__boxed_1650_ = (leanh::lean_unbox(v___x_1647_) as u8);
    v_res_1651_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_429__boxed_1650_, v_x_1648_, v_x_1649_);
    leanh::lean_dec_ref(v_x_1649_);
    leanh::lean_dec_ref(v_x_1648_);
    v_r_1652_ = leanh::lean_box((v_res_1651_) as usize);
    return v_r_1652_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(
    mut v_n_1653_: *mut leanh::LeanObject,
    mut v_as_1654_: *mut leanh::LeanObject,
    mut v_lo_1655_: *mut leanh::LeanObject,
    mut v_hi_1656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: u8 = 0;
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: u8 = 0;
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: u8 = 0;
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: u8 = 0;
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1668_ = lean_nat_dec_lt(v_lo_1655_, v_hi_1656_);
                if v___x_1668_ == 0 {
                    leanh::lean_dec(v_lo_1655_);
                    return v_as_1654_;
                } else {
                    v___x_1669_ = lean_nat_add(v_lo_1655_, v_hi_1656_);
                    v___x_1670_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_1671_ = lean_nat_shiftr(v___x_1669_, v___x_1670_);
                    leanh::lean_dec(v___x_1669_);
                    v___x_1684_ = lean_array_fget_borrowed(v_as_1654_, v_mid_1671_);
                    v___x_1685_ = lean_array_fget_borrowed(v_as_1654_, v_lo_1655_);
                    v___x_1686_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_1668_, v___x_1684_, v___x_1685_);
                    if v___x_1686_ == 0 {
                        v___y_1679_ = v_as_1654_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1687_ = lean_array_fswap(v_as_1654_, v_lo_1655_, v_mid_1671_);
                        v___y_1679_ = v___x_1687_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_1659_ = lean_array_fget(v___y_1658_, v_hi_1656_);
                leanh::lean_inc_n(v_lo_1655_, 2);
                v___x_1660_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(v_hi_1656_, v_pivot_1659_, v___y_1658_, v_lo_1655_, v_lo_1655_);
                leanh::lean_dec(v_pivot_1659_);
                v_fst_1661_ = leanh::lean_ctor_get(v___x_1660_, 0);
                leanh::lean_inc(v_fst_1661_);
                v_snd_1662_ = leanh::lean_ctor_get(v___x_1660_, 1);
                leanh::lean_inc(v_snd_1662_);
                leanh::lean_dec_ref(v___x_1660_);
                v___x_1663_ = lean_nat_dec_le(v_hi_1656_, v_fst_1661_);
                if v___x_1663_ == 0 {
                    v___x_1664_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_n_1653_, v_snd_1662_, v_lo_1655_, v_fst_1661_);
                    v___x_1665_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1666_ = lean_nat_add(v_fst_1661_, v___x_1665_);
                    leanh::lean_dec(v_fst_1661_);
                    v_as_1654_ = v___x_1664_;
                    v_lo_1655_ = v___x_1666_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_1661_);
                    leanh::lean_dec(v_lo_1655_);
                    return v_snd_1662_;
                }
            }
            2 => {
                v___x_1674_ = lean_array_fget_borrowed(v___y_1673_, v_mid_1671_);
                v___x_1675_ = lean_array_fget_borrowed(v___y_1673_, v_hi_1656_);
                v___x_1676_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_1668_, v___x_1674_, v___x_1675_);
                if v___x_1676_ == 0 {
                    leanh::lean_dec(v_mid_1671_);
                    v___y_1658_ = v___y_1673_;
                    state = 1;
                    continue;
                } else {
                    v___x_1677_ = lean_array_fswap(v___y_1673_, v_mid_1671_, v_hi_1656_);
                    leanh::lean_dec(v_mid_1671_);
                    v___y_1658_ = v___x_1677_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1680_ = lean_array_fget_borrowed(v___y_1679_, v_hi_1656_);
                v___x_1681_ = lean_array_fget_borrowed(v___y_1679_, v_lo_1655_);
                v___x_1682_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_1668_, v___x_1680_, v___x_1681_);
                if v___x_1682_ == 0 {
                    v___y_1673_ = v___y_1679_;
                    state = 2;
                    continue;
                } else {
                    v___x_1683_ = lean_array_fswap(v___y_1679_, v_lo_1655_, v_hi_1656_);
                    v___y_1673_ = v___x_1683_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___boxed(
    mut v_n_1688_: *mut leanh::LeanObject,
    mut v_as_1689_: *mut leanh::LeanObject,
    mut v_lo_1690_: *mut leanh::LeanObject,
    mut v_hi_1691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1692_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_n_1688_, v_as_1689_, v_lo_1690_, v_hi_1691_);
    leanh::lean_dec(v_hi_1691_);
    leanh::lean_dec(v_n_1688_);
    return v_res_1692_;
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(
    mut v_alts_1693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: u8 = 0;
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: u8 = 0;
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1694_ = lean_array_get_size(v_alts_1693_);
                v___x_1695_ = leanh::lean_unsigned_to_nat(0);
                v___x_1696_ = lean_nat_dec_eq(v___x_1694_, v___x_1695_);
                if v___x_1696_ == 0 {
                    v___x_1697_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1698_ = lean_nat_sub(v___x_1694_, v___x_1697_);
                    v___x_1704_ = lean_nat_dec_le(v___x_1695_, v___x_1698_);
                    if v___x_1704_ == 0 {
                        leanh::lean_inc(v___x_1698_);
                        v___y_1700_ = v___x_1698_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1700_ = v___x_1695_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_alts_1693_;
                }
            }
            1 => {
                v___x_1701_ = lean_nat_dec_le(v___y_1700_, v___x_1698_);
                if v___x_1701_ == 0 {
                    leanh::lean_dec(v___x_1698_);
                    leanh::lean_inc(v___y_1700_);
                    v___x_1702_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v___x_1694_, v_alts_1693_, v___y_1700_, v___y_1700_);
                    leanh::lean_dec(v___y_1700_);
                    return v___x_1702_;
                } else {
                    v___x_1703_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v___x_1694_, v_alts_1693_, v___y_1700_, v___x_1698_);
                    leanh::lean_dec(v___x_1698_);
                    return v___x_1703_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_sortAlts(
    mut v_pu_1705_: u8,
    mut v_alts_1706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1707_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_1706_);
    return v___x_1707_;
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___boxed(
    mut v_pu_1708_: *mut leanh::LeanObject,
    mut v_alts_1709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1710_: u8 = 0;
    let mut v_res_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1710_ = (leanh::lean_unbox(v_pu_1708_) as u8);
    v_res_1711_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts(v_pu_boxed_1710_, v_alts_1709_);
    return v_res_1711_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0(
    mut v_n_1712_: *mut leanh::LeanObject,
    mut v_as_1713_: *mut leanh::LeanObject,
    mut v_lo_1714_: *mut leanh::LeanObject,
    mut v_hi_1715_: *mut leanh::LeanObject,
    mut v_w_1716_: *mut leanh::LeanObject,
    mut v_hlo_1717_: *mut leanh::LeanObject,
    mut v_hhi_1718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1719_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_n_1712_, v_as_1713_, v_lo_1714_, v_hi_1715_);
    return v___x_1719_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___boxed(
    mut v_n_1720_: *mut leanh::LeanObject,
    mut v_as_1721_: *mut leanh::LeanObject,
    mut v_lo_1722_: *mut leanh::LeanObject,
    mut v_hi_1723_: *mut leanh::LeanObject,
    mut v_w_1724_: *mut leanh::LeanObject,
    mut v_hlo_1725_: *mut leanh::LeanObject,
    mut v_hhi_1726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1727_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0(v_n_1720_, v_as_1721_, v_lo_1722_, v_hi_1723_, v_w_1724_, v_hlo_1725_, v_hhi_1726_);
    leanh::lean_dec(v_hi_1723_);
    leanh::lean_dec(v_n_1720_);
    return v_res_1727_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0(
    mut v_n_1728_: *mut leanh::LeanObject,
    mut v_lo_1729_: *mut leanh::LeanObject,
    mut v_hi_1730_: *mut leanh::LeanObject,
    mut v_hhi_1731_: *mut leanh::LeanObject,
    mut v_pivot_1732_: *mut leanh::LeanObject,
    mut v_as_1733_: *mut leanh::LeanObject,
    mut v_i_1734_: *mut leanh::LeanObject,
    mut v_k_1735_: *mut leanh::LeanObject,
    mut v_ilo_1736_: *mut leanh::LeanObject,
    mut v_ik_1737_: *mut leanh::LeanObject,
    mut v_w_1738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1739_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(v_hi_1730_, v_pivot_1732_, v_as_1733_, v_i_1734_, v_k_1735_);
    return v___x_1739_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___boxed(
    mut v_n_1740_: *mut leanh::LeanObject,
    mut v_lo_1741_: *mut leanh::LeanObject,
    mut v_hi_1742_: *mut leanh::LeanObject,
    mut v_hhi_1743_: *mut leanh::LeanObject,
    mut v_pivot_1744_: *mut leanh::LeanObject,
    mut v_as_1745_: *mut leanh::LeanObject,
    mut v_i_1746_: *mut leanh::LeanObject,
    mut v_k_1747_: *mut leanh::LeanObject,
    mut v_ilo_1748_: *mut leanh::LeanObject,
    mut v_ik_1749_: *mut leanh::LeanObject,
    mut v_w_1750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1751_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0(v_n_1740_, v_lo_1741_, v_hi_1742_, v_hhi_1743_, v_pivot_1744_, v_as_1745_, v_i_1746_, v_k_1747_, v_ilo_1748_, v_ik_1749_, v_w_1750_);
    leanh::lean_dec_ref(v_pivot_1744_);
    leanh::lean_dec(v_hi_1742_);
    leanh::lean_dec(v_lo_1741_);
    leanh::lean_dec(v_n_1740_);
    return v_res_1751_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3(
    mut v_x_1752_: *mut leanh::LeanObject,
    mut v_x_1753_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_1752_) == 0 {
        if leanh::lean_obj_tag(v_x_1753_) == 0 {
            let mut v___x_1754_: u8 = 0;
            v___x_1754_ = 1;
            return v___x_1754_;
        } else {
            let mut v___x_1755_: u8 = 0;
            v___x_1755_ = 0;
            return v___x_1755_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_1753_) == 0 {
            let mut v___x_1756_: u8 = 0;
            v___x_1756_ = 0;
            return v___x_1756_;
        } else {
            let mut v_val_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1759_: u8 = 0;
            v_val_1757_ = leanh::lean_ctor_get(v_x_1752_, 0);
            v_val_1758_ = leanh::lean_ctor_get(v_x_1753_, 0);
            v___x_1759_ = lean_nat_dec_eq(v_val_1757_, v_val_1758_);
            return v___x_1759_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3___boxed(
    mut v_x_1760_: *mut leanh::LeanObject,
    mut v_x_1761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1762_: u8 = 0;
    let mut v_r_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1762_ =
        l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3(v_x_1760_, v_x_1761_);
    leanh::lean_dec(v_x_1761_);
    leanh::lean_dec(v_x_1760_);
    v_r_1763_ = leanh::lean_box((v_res_1762_) as usize);
    return v_r_1763_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(
    mut v_pu_1767_: u8,
    mut v_as_1768_: *mut leanh::LeanObject,
    mut v_sz_1769_: usize,
    mut v_i_1770_: usize,
    mut v_b_1771_: *mut leanh::LeanObject,
    mut v___y_1772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: usize = 0;
    let mut v___x_1776_: usize = 0;
    let mut v___x_1778_: u8 = 0;
    let mut v_snd_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1782_: u8 = 0;
    let mut v_array_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: u8 = 0;
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1793_: u8 = 0;
    let mut v_a_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1801_: u8 = 0;
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: u8 = 0;
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: u8 = 0;
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: u8 = 0;
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1832_: u8 = 0;
    let mut v___x_1833_: u8 = 0;
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: u8 = 0;
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1848_: u8 = 0;
    let mut v_code_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___x_1854_: u8 = 0;
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1861_: u8 = 0;
    let mut v_reuseFailAlloc_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1863_: u8 = 0;
    let mut v_unused_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1867_: u8 = 0;
    let mut v_unused_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1778_ = lean_usize_dec_lt(v_i_1770_, v_sz_1769_);
                if v___x_1778_ == 0 {
                    return v_b_1771_;
                } else {
                    v_snd_1779_ = leanh::lean_ctor_get(v_b_1771_, 1);
                    v_isSharedCheck_1867_ = (!leanh::lean_is_exclusive(v_b_1771_)) as u8;
                    if v_isSharedCheck_1867_ == 0 {
                        v_unused_1868_ = leanh::lean_ctor_get(v_b_1771_, 0);
                        leanh::lean_dec(v_unused_1868_);
                        v___x_1781_ = v_b_1771_;
                        v_isShared_1782_ = v_isSharedCheck_1867_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1779_);
                        leanh::lean_dec(v_b_1771_);
                        v___x_1781_ = leanh::lean_box(0);
                        v_isShared_1782_ = v_isSharedCheck_1867_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1775_ = 1usize;
                v___x_1776_ = lean_usize_add(v_i_1770_, v___x_1775_);
                v_i_1770_ = v___x_1776_;
                v_b_1771_ = v_a_1774_;
                state = 0;
                continue;
            }
            2 => {
                v_array_1783_ = leanh::lean_ctor_get(v_snd_1779_, 0);
                v_start_1784_ = leanh::lean_ctor_get(v_snd_1779_, 1);
                v_stop_1785_ = leanh::lean_ctor_get(v_snd_1779_, 2);
                v___x_1786_ = leanh::lean_box(0);
                v___x_1787_ = lean_nat_dec_lt(v_start_1784_, v_stop_1785_);
                if v___x_1787_ == 0 {
                    if v_isShared_1782_ == 0 {
                        leanh::lean_ctor_set(v___x_1781_, 0, v___x_1786_);
                        v___x_1789_ = v___x_1781_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1790_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1786_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_snd_1779_);
                        v___x_1789_ = v_reuseFailAlloc_1790_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_stop_1785_);
                    leanh::lean_inc(v_start_1784_);
                    leanh::lean_inc_ref(v_array_1783_);
                    v_isSharedCheck_1863_ = (!leanh::lean_is_exclusive(v_snd_1779_)) as u8;
                    if v_isSharedCheck_1863_ == 0 {
                        v_unused_1864_ = leanh::lean_ctor_get(v_snd_1779_, 2);
                        leanh::lean_dec(v_unused_1864_);
                        v_unused_1865_ = leanh::lean_ctor_get(v_snd_1779_, 1);
                        leanh::lean_dec(v_unused_1865_);
                        v_unused_1866_ = leanh::lean_ctor_get(v_snd_1779_, 0);
                        leanh::lean_dec(v_unused_1866_);
                        v___x_1792_ = v_snd_1779_;
                        v_isShared_1793_ = v_isSharedCheck_1863_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_snd_1779_);
                        v___x_1792_ = leanh::lean_box(0);
                        v_isShared_1793_ = v_isSharedCheck_1863_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1789_;
            }
            4 => {
                v_a_1794_ = lean_array_uget_borrowed(v_as_1768_, v_i_1770_);
                v___x_1795_ = lean_array_fget(v_array_1783_, v_start_1784_);
                v___x_1796_ = leanh::lean_unsigned_to_nat(1);
                v___x_1797_ = lean_nat_add(v_start_1784_, v___x_1796_);
                leanh::lean_dec(v_start_1784_);
                if v_isShared_1793_ == 0 {
                    leanh::lean_ctor_set(v___x_1792_, 1, v___x_1797_);
                    v___x_1799_ = v___x_1792_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1862_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_array_1783_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1862_, 1, v___x_1797_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1862_, 2, v_stop_1785_);
                    v___x_1799_ = v_reuseFailAlloc_1862_;
                    state = 5;
                    continue;
                }
            }
            5 => match leanh::lean_obj_tag(v_a_1794_) {
                0 => {
                    if leanh::lean_obj_tag(v___x_1795_) == 0 {
                        v_ctorName_1810_ = leanh::lean_ctor_get(v_a_1794_, 0);
                        v_params_1811_ = leanh::lean_ctor_get(v_a_1794_, 1);
                        v_code_1812_ = leanh::lean_ctor_get(v_a_1794_, 2);
                        v_ctorName_1813_ = leanh::lean_ctor_get(v___x_1795_, 0);
                        leanh::lean_inc(v_ctorName_1813_);
                        v_params_1814_ = leanh::lean_ctor_get(v___x_1795_, 1);
                        leanh::lean_inc_ref(v_params_1814_);
                        v_code_1815_ = leanh::lean_ctor_get(v___x_1795_, 2);
                        leanh::lean_inc_ref(v_code_1815_);
                        leanh::lean_dec_ref_known(v___x_1795_, 3);
                        v___x_1816_ = lean_name_eq(v_ctorName_1810_, v_ctorName_1813_);
                        leanh::lean_dec(v_ctorName_1813_);
                        if v___x_1816_ == 0 {
                            leanh::lean_dec_ref(v_code_1815_);
                            leanh::lean_dec_ref(v_params_1814_);
                            leanh::lean_del_object(v___x_1781_);
                            v___x_1817_ = leanh::lean_box((v___x_1816_) as usize);
                            v___x_1818_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1818_, 0, v___x_1817_);
                            v___x_1819_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1819_, 0, v___x_1818_);
                            leanh::lean_ctor_set(v___x_1819_, 1, v___x_1799_);
                            return v___x_1819_;
                        } else {
                            v___x_1820_ = lean_array_get_size(v_params_1814_);
                            v___x_1821_ = lean_array_get_size(v_params_1811_);
                            v___x_1822_ = lean_nat_dec_eq(v___x_1820_, v___x_1821_);
                            if v___x_1822_ == 0 {
                                leanh::lean_dec_ref(v_code_1815_);
                                leanh::lean_dec_ref(v_params_1814_);
                                v___y_1801_ = v___x_1822_;
                                state = 6;
                                continue;
                            } else {
                                v___x_1823_ = leanh::lean_unsigned_to_nat(0);
                                leanh::lean_inc(v___y_1772_);
                                leanh::lean_inc_ref(v_code_1812_);
                                v___x_1824_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_1767_, v_code_1812_, v_code_1815_, v_params_1811_, v_params_1814_, v___x_1823_, v___y_1772_);
                                leanh::lean_dec_ref(v_params_1814_);
                                if v___x_1824_ == 0 {
                                    v___y_1801_ = v___x_1824_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_del_object(v___x_1781_);
                                    v___x_1825_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1825_, 0, v___x_1786_);
                                    leanh::lean_ctor_set(v___x_1825_, 1, v___x_1799_);
                                    v_a_1774_ = v___x_1825_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_1795_);
                        leanh::lean_del_object(v___x_1781_);
                        state = 8;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_1781_);
                    if leanh::lean_obj_tag(v___x_1795_) == 1 {
                        v_info_1826_ = leanh::lean_ctor_get(v_a_1794_, 0);
                        v_code_1827_ = leanh::lean_ctor_get(v_a_1794_, 1);
                        v_info_1828_ = leanh::lean_ctor_get(v___x_1795_, 0);
                        v_code_1829_ = leanh::lean_ctor_get(v___x_1795_, 1);
                        v_isSharedCheck_1848_ =
                            (!leanh::lean_is_exclusive(v___x_1795_)) as u8;
                        if v_isSharedCheck_1848_ == 0 {
                            v___x_1831_ = v___x_1795_;
                            v_isShared_1832_ = v_isSharedCheck_1848_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_code_1829_);
                            leanh::lean_inc(v_info_1828_);
                            leanh::lean_dec(v___x_1795_);
                            v___x_1831_ = leanh::lean_box(0);
                            v_isShared_1832_ = v_isSharedCheck_1848_;
                            state = 9;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1795_);
                        state = 8;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_del_object(v___x_1781_);
                    if leanh::lean_obj_tag(v___x_1795_) == 2 {
                        v_code_1849_ = leanh::lean_ctor_get(v_a_1794_, 0);
                        v_code_1850_ = leanh::lean_ctor_get(v___x_1795_, 0);
                        v_isSharedCheck_1861_ =
                            (!leanh::lean_is_exclusive(v___x_1795_)) as u8;
                        if v_isSharedCheck_1861_ == 0 {
                            v___x_1852_ = v___x_1795_;
                            v_isShared_1853_ = v_isSharedCheck_1861_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_code_1850_);
                            leanh::lean_dec(v___x_1795_);
                            v___x_1852_ = leanh::lean_box(0);
                            v_isShared_1853_ = v_isSharedCheck_1861_;
                            state = 13;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1795_);
                        state = 8;
                        continue;
                    }
                }
            },
            6 => {
                v___x_1802_ = leanh::lean_box((v___y_1801_) as usize);
                v___x_1803_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1803_, 0, v___x_1802_);
                if v_isShared_1782_ == 0 {
                    leanh::lean_ctor_set(v___x_1781_, 1, v___x_1799_);
                    leanh::lean_ctor_set(v___x_1781_, 0, v___x_1803_);
                    v___x_1805_ = v___x_1781_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1806_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1806_, 1, v___x_1799_);
                    v___x_1805_ = v_reuseFailAlloc_1806_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1805_;
            }
            8 => {
                v___x_1808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___closed__0;
                v___x_1809_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1809_, 0, v___x_1808_);
                leanh::lean_ctor_set(v___x_1809_, 1, v___x_1799_);
                return v___x_1809_;
            }
            9 => {
                v___x_1833_ = l_Lean_Compiler_LCNF_instBEqCtorInfo_beq(v_info_1826_, v_info_1828_);
                leanh::lean_dec_ref(v_info_1828_);
                if v___x_1833_ == 0 {
                    leanh::lean_dec_ref(v_code_1829_);
                    v___x_1834_ = leanh::lean_box((v___x_1833_) as usize);
                    v___x_1835_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1835_, 0, v___x_1834_);
                    if v_isShared_1832_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1831_, 0);
                        leanh::lean_ctor_set(v___x_1831_, 1, v___x_1799_);
                        leanh::lean_ctor_set(v___x_1831_, 0, v___x_1835_);
                        v___x_1837_ = v___x_1831_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1838_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1838_, 1, v___x_1799_);
                        v___x_1837_ = v_reuseFailAlloc_1838_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v___y_1772_);
                    leanh::lean_inc_ref(v_code_1827_);
                    v___x_1839_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(
                        v_pu_1767_,
                        v_code_1827_,
                        v_code_1829_,
                        v___y_1772_,
                    );
                    if v___x_1839_ == 0 {
                        v___x_1840_ = leanh::lean_box((v___x_1839_) as usize);
                        v___x_1841_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1841_, 0, v___x_1840_);
                        if v_isShared_1832_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_1831_, 0);
                            leanh::lean_ctor_set(v___x_1831_, 1, v___x_1799_);
                            leanh::lean_ctor_set(v___x_1831_, 0, v___x_1841_);
                            v___x_1843_ = v___x_1831_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_1844_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 1, v___x_1799_);
                            v___x_1843_ = v_reuseFailAlloc_1844_;
                            state = 11;
                            continue;
                        }
                    } else {
                        if v_isShared_1832_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_1831_, 0);
                            leanh::lean_ctor_set(v___x_1831_, 1, v___x_1799_);
                            leanh::lean_ctor_set(v___x_1831_, 0, v___x_1786_);
                            v___x_1846_ = v___x_1831_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_1847_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1786_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1847_, 1, v___x_1799_);
                            v___x_1846_ = v_reuseFailAlloc_1847_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            10 => {
                return v___x_1837_;
            }
            11 => {
                return v___x_1843_;
            }
            12 => {
                v_a_1774_ = v___x_1846_;
                state = 1;
                continue;
            }
            13 => {
                leanh::lean_inc(v___y_1772_);
                leanh::lean_inc_ref(v_code_1849_);
                v___x_1854_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(
                    v_pu_1767_,
                    v_code_1849_,
                    v_code_1850_,
                    v___y_1772_,
                );
                if v___x_1854_ == 0 {
                    v___x_1855_ = leanh::lean_box((v___x_1854_) as usize);
                    if v_isShared_1853_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1852_, 1);
                        leanh::lean_ctor_set(v___x_1852_, 0, v___x_1855_);
                        v___x_1857_ = v___x_1852_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_1859_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1855_);
                        v___x_1857_ = v_reuseFailAlloc_1859_;
                        state = 14;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1852_);
                    v___x_1860_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1860_, 0, v___x_1786_);
                    leanh::lean_ctor_set(v___x_1860_, 1, v___x_1799_);
                    v_a_1774_ = v___x_1860_;
                    state = 1;
                    continue;
                }
            }
            14 => {
                v___x_1858_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1858_, 0, v___x_1857_);
                leanh::lean_ctor_set(v___x_1858_, 1, v___x_1799_);
                return v___x_1858_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(
    mut v_pu_1869_: u8,
    mut v_alts_u2081_1870_: *mut leanh::LeanObject,
    mut v_alts_u2082_1871_: *mut leanh::LeanObject,
    mut v_a_1872_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: u8 = 0;
    v___x_1873_ = lean_array_get_size(v_alts_u2081_1870_);
    v___x_1874_ = lean_array_get_size(v_alts_u2082_1871_);
    v___x_1875_ = lean_nat_dec_eq(v___x_1873_, v___x_1874_);
    if v___x_1875_ == 0 {
        leanh::lean_dec_ref(v_alts_u2082_1871_);
        leanh::lean_dec_ref(v_alts_u2081_1870_);
        return v___x_1875_;
    } else {
        let mut v_alts_u2081_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_alts_u2082_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_1883_: usize = 0;
        let mut v___x_1884_: usize = 0;
        let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_alts_u2081_1876_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_u2081_1870_);
        v_alts_u2082_1877_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_u2082_1871_);
        v___x_1878_ = leanh::lean_unsigned_to_nat(0);
        v___x_1879_ = lean_array_get_size(v_alts_u2082_1877_);
        v___x_1880_ = l_Array_toSubarray___redArg(v_alts_u2082_1877_, v___x_1878_, v___x_1879_);
        v___x_1881_ = leanh::lean_box(0);
        v___x_1882_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1882_, 0, v___x_1881_);
        leanh::lean_ctor_set(v___x_1882_, 1, v___x_1880_);
        v_sz_1883_ = lean_array_size(v_alts_u2081_1876_);
        v___x_1884_ = 0usize;
        v___x_1885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(v_pu_1869_, v_alts_u2081_1876_, v_sz_1883_, v___x_1884_, v___x_1882_, v_a_1872_);
        leanh::lean_dec_ref(v_alts_u2081_1876_);
        v_fst_1886_ = leanh::lean_ctor_get(v___x_1885_, 0);
        leanh::lean_inc(v_fst_1886_);
        leanh::lean_dec_ref(v___x_1885_);
        if leanh::lean_obj_tag(v_fst_1886_) == 0 {
            return v___x_1875_;
        } else {
            let mut v_val_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1888_: u8 = 0;
            v_val_1887_ = leanh::lean_ctor_get(v_fst_1886_, 0);
            leanh::lean_inc(v_val_1887_);
            leanh::lean_dec_ref_known(v_fst_1886_, 1);
            v___x_1888_ = (leanh::lean_unbox(v_val_1887_) as u8);
            leanh::lean_dec(v_val_1887_);
            return v___x_1888_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_eqv(
    mut v_pu_1889_: u8,
    mut v_code_u2081_1890_: *mut leanh::LeanObject,
    mut v_code_u2082_1891_: *mut leanh::LeanObject,
    mut v_a_1892_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_decl_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: u8 = 0;
    let mut v___x_1904_: u8 = 0;
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: u8 = 0;
    let mut v_decl_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: u8 = 0;
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: u8 = 0;
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: u8 = 0;
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: u8 = 0;
    let mut v_decl_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: u8 = 0;
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: u8 = 0;
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: u8 = 0;
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: u8 = 0;
    let mut v_fvarId_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: u8 = 0;
    let mut v___x_1955_: u8 = 0;
    let mut v___x_1956_: u8 = 0;
    let mut v_cases_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: u8 = 0;
    let mut v___x_1966_: u8 = 0;
    let mut v___x_1967_: u8 = 0;
    let mut v___x_1968_: u8 = 0;
    let mut v_fvarId_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: u8 = 0;
    let mut v___x_1972_: u8 = 0;
    let mut v_type_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: u8 = 0;
    let mut v___x_1976_: u8 = 0;
    let mut v_fvarId_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: u8 = 0;
    let mut v___x_1986_: u8 = 0;
    let mut v___x_1987_: u8 = 0;
    let mut v___x_1989_: u8 = 0;
    let mut v_fvarId_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: u8 = 0;
    let mut v___x_1999_: u8 = 0;
    let mut v___x_2000_: u8 = 0;
    let mut v___x_2002_: u8 = 0;
    let mut v_fvarId_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: u8 = 0;
    let mut v___x_2016_: u8 = 0;
    let mut v___x_2017_: u8 = 0;
    let mut v___x_2018_: u8 = 0;
    let mut v___x_2019_: u8 = 0;
    let mut v___x_2021_: u8 = 0;
    let mut v_fvarId_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: u8 = 0;
    let mut v___x_2029_: u8 = 0;
    let mut v___x_2031_: u8 = 0;
    let mut v_fvarId_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_2034_: u8 = 0;
    let mut v_persistent_2035_: u8 = 0;
    let mut v_k_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_2039_: u8 = 0;
    let mut v_persistent_2040_: u8 = 0;
    let mut v_k_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: u8 = 0;
    let mut v___y_2046_: u8 = 0;
    let mut v___x_2047_: u8 = 0;
    let mut v___x_2048_: u8 = 0;
    let mut v_fvarId_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_2051_: u8 = 0;
    let mut v_persistent_2052_: u8 = 0;
    let mut v_objs_x3f_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_2057_: u8 = 0;
    let mut v_persistent_2058_: u8 = 0;
    let mut v_objs_x3f_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: u8 = 0;
    let mut v___x_2063_: u8 = 0;
    let mut v___y_2066_: u8 = 0;
    let mut v___x_2067_: u8 = 0;
    let mut v___x_2068_: u8 = 0;
    let mut v_fvarId_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: u8 = 0;
    let mut v___x_2075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_code_u2081_1890_) {
                0 => {
                    if leanh::lean_obj_tag(v_code_u2082_1891_) == 0 {
                        v_decl_1893_ = leanh::lean_ctor_get(v_code_u2081_1890_, 0);
                        leanh::lean_inc_ref(v_decl_1893_);
                        v_decl_1894_ = leanh::lean_ctor_get(v_code_u2082_1891_, 0);
                        leanh::lean_inc_ref(v_decl_1894_);
                        v_k_1895_ = leanh::lean_ctor_get(v_code_u2081_1890_, 1);
                        leanh::lean_inc_ref(v_k_1895_);
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 2);
                        v_k_1896_ = leanh::lean_ctor_get(v_code_u2082_1891_, 1);
                        leanh::lean_inc_ref(v_k_1896_);
                        leanh::lean_dec_ref_known(v_code_u2082_1891_, 2);
                        v_fvarId_1897_ = leanh::lean_ctor_get(v_decl_1893_, 0);
                        leanh::lean_inc(v_fvarId_1897_);
                        v_type_1898_ = leanh::lean_ctor_get(v_decl_1893_, 2);
                        leanh::lean_inc_ref(v_type_1898_);
                        v_value_1899_ = leanh::lean_ctor_get(v_decl_1893_, 3);
                        leanh::lean_inc(v_value_1899_);
                        leanh::lean_dec_ref(v_decl_1893_);
                        v_fvarId_1900_ = leanh::lean_ctor_get(v_decl_1894_, 0);
                        leanh::lean_inc(v_fvarId_1900_);
                        v_type_1901_ = leanh::lean_ctor_get(v_decl_1894_, 2);
                        leanh::lean_inc_ref(v_type_1901_);
                        v_value_1902_ = leanh::lean_ctor_get(v_decl_1894_, 3);
                        leanh::lean_inc(v_value_1902_);
                        leanh::lean_dec_ref(v_decl_1894_);
                        v___x_1903_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(
                            v_type_1898_,
                            v_type_1901_,
                            v_a_1892_,
                        );
                        leanh::lean_dec_ref(v_type_1901_);
                        leanh::lean_dec_ref(v_type_1898_);
                        if v___x_1903_ == 0 {
                            leanh::lean_dec(v_value_1902_);
                            leanh::lean_dec(v_fvarId_1900_);
                            leanh::lean_dec(v_value_1899_);
                            leanh::lean_dec(v_fvarId_1897_);
                            leanh::lean_dec_ref(v_k_1896_);
                            leanh::lean_dec_ref(v_k_1895_);
                            leanh::lean_dec(v_a_1892_);
                            return v___x_1903_;
                        } else {
                            v___x_1904_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue(
                                v_pu_1889_,
                                v_value_1899_,
                                v_value_1902_,
                                v_a_1892_,
                            );
                            leanh::lean_dec(v_value_1899_);
                            if v___x_1904_ == 0 {
                                leanh::lean_dec(v_fvarId_1900_);
                                leanh::lean_dec(v_fvarId_1897_);
                                leanh::lean_dec_ref(v_k_1896_);
                                leanh::lean_dec_ref(v_k_1895_);
                                leanh::lean_dec(v_a_1892_);
                                return v___x_1904_;
                            } else {
                                v___x_1905_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1900_, v_fvarId_1897_, v_a_1892_);
                                v_code_u2081_1890_ = v_k_1895_;
                                v_code_u2082_1891_ = v_k_1896_;
                                v_a_1892_ = v___x_1905_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 2);
                        leanh::lean_dec(v_a_1892_);
                        leanh::lean_dec_ref(v_code_u2082_1891_);
                        v___x_1907_ = 0;
                        return v___x_1907_;
                    }
                }
                1 => {
                    if leanh::lean_obj_tag(v_code_u2082_1891_) == 1 {
                        v_decl_1908_ = leanh::lean_ctor_get(v_code_u2081_1890_, 0);
                        leanh::lean_inc_ref(v_decl_1908_);
                        v_decl_1909_ = leanh::lean_ctor_get(v_code_u2082_1891_, 0);
                        leanh::lean_inc_ref(v_decl_1909_);
                        v_k_1910_ = leanh::lean_ctor_get(v_code_u2081_1890_, 1);
                        leanh::lean_inc_ref(v_k_1910_);
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 2);
                        v_k_1911_ = leanh::lean_ctor_get(v_code_u2082_1891_, 1);
                        leanh::lean_inc_ref(v_k_1911_);
                        leanh::lean_dec_ref_known(v_code_u2082_1891_, 2);
                        v_fvarId_1912_ = leanh::lean_ctor_get(v_decl_1908_, 0);
                        leanh::lean_inc(v_fvarId_1912_);
                        v_params_1913_ = leanh::lean_ctor_get(v_decl_1908_, 2);
                        leanh::lean_inc_ref(v_params_1913_);
                        v_type_1914_ = leanh::lean_ctor_get(v_decl_1908_, 3);
                        leanh::lean_inc_ref(v_type_1914_);
                        v_value_1915_ = leanh::lean_ctor_get(v_decl_1908_, 4);
                        leanh::lean_inc_ref(v_value_1915_);
                        leanh::lean_dec_ref(v_decl_1908_);
                        v_fvarId_1916_ = leanh::lean_ctor_get(v_decl_1909_, 0);
                        leanh::lean_inc(v_fvarId_1916_);
                        v_params_1917_ = leanh::lean_ctor_get(v_decl_1909_, 2);
                        leanh::lean_inc_ref(v_params_1917_);
                        v_type_1918_ = leanh::lean_ctor_get(v_decl_1909_, 3);
                        leanh::lean_inc_ref(v_type_1918_);
                        v_value_1919_ = leanh::lean_ctor_get(v_decl_1909_, 4);
                        leanh::lean_inc_ref(v_value_1919_);
                        leanh::lean_dec_ref(v_decl_1909_);
                        v___x_1920_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(
                            v_type_1914_,
                            v_type_1918_,
                            v_a_1892_,
                        );
                        leanh::lean_dec_ref(v_type_1918_);
                        leanh::lean_dec_ref(v_type_1914_);
                        if v___x_1920_ == 0 {
                            leanh::lean_dec_ref(v_value_1919_);
                            leanh::lean_dec_ref(v_params_1917_);
                            leanh::lean_dec(v_fvarId_1916_);
                            leanh::lean_dec_ref(v_value_1915_);
                            leanh::lean_dec_ref(v_params_1913_);
                            leanh::lean_dec(v_fvarId_1912_);
                            leanh::lean_dec_ref(v_k_1911_);
                            leanh::lean_dec_ref(v_k_1910_);
                            leanh::lean_dec(v_a_1892_);
                            return v___x_1920_;
                        } else {
                            v___x_1921_ = lean_array_get_size(v_params_1917_);
                            v___x_1922_ = lean_array_get_size(v_params_1913_);
                            v___x_1923_ = lean_nat_dec_eq(v___x_1921_, v___x_1922_);
                            if v___x_1923_ == 0 {
                                leanh::lean_dec_ref(v_value_1919_);
                                leanh::lean_dec_ref(v_params_1917_);
                                leanh::lean_dec(v_fvarId_1916_);
                                leanh::lean_dec_ref(v_value_1915_);
                                leanh::lean_dec_ref(v_params_1913_);
                                leanh::lean_dec(v_fvarId_1912_);
                                leanh::lean_dec_ref(v_k_1911_);
                                leanh::lean_dec_ref(v_k_1910_);
                                leanh::lean_dec(v_a_1892_);
                                return v___x_1923_;
                            } else {
                                v___x_1924_ = leanh::lean_unsigned_to_nat(0);
                                leanh::lean_inc(v_a_1892_);
                                v___x_1925_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_1889_, v_value_1915_, v_value_1919_, v_params_1913_, v_params_1917_, v___x_1924_, v_a_1892_);
                                leanh::lean_dec_ref(v_params_1917_);
                                leanh::lean_dec_ref(v_params_1913_);
                                if v___x_1925_ == 0 {
                                    leanh::lean_dec(v_fvarId_1916_);
                                    leanh::lean_dec(v_fvarId_1912_);
                                    leanh::lean_dec_ref(v_k_1911_);
                                    leanh::lean_dec_ref(v_k_1910_);
                                    leanh::lean_dec(v_a_1892_);
                                    return v___x_1925_;
                                } else {
                                    v___x_1926_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1916_, v_fvarId_1912_, v_a_1892_);
                                    v_code_u2081_1890_ = v_k_1910_;
                                    v_code_u2082_1891_ = v_k_1911_;
                                    v_a_1892_ = v___x_1926_;
                                    state = 0;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 2);
                        leanh::lean_dec(v_a_1892_);
                        leanh::lean_dec_ref(v_code_u2082_1891_);
                        v___x_1928_ = 0;
                        return v___x_1928_;
                    }
                }
                2 => {
                    if leanh::lean_obj_tag(v_code_u2082_1891_) == 2 {
                        v_decl_1929_ = leanh::lean_ctor_get(v_code_u2081_1890_, 0);
                        leanh::lean_inc_ref(v_decl_1929_);
                        v_decl_1930_ = leanh::lean_ctor_get(v_code_u2082_1891_, 0);
                        leanh::lean_inc_ref(v_decl_1930_);
                        v_k_1931_ = leanh::lean_ctor_get(v_code_u2081_1890_, 1);
                        leanh::lean_inc_ref(v_k_1931_);
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 2);
                        v_k_1932_ = leanh::lean_ctor_get(v_code_u2082_1891_, 1);
                        leanh::lean_inc_ref(v_k_1932_);
                        leanh::lean_dec_ref_known(v_code_u2082_1891_, 2);
                        v_fvarId_1933_ = leanh::lean_ctor_get(v_decl_1929_, 0);
                        leanh::lean_inc(v_fvarId_1933_);
                        v_params_1934_ = leanh::lean_ctor_get(v_decl_1929_, 2);
                        leanh::lean_inc_ref(v_params_1934_);
                        v_type_1935_ = leanh::lean_ctor_get(v_decl_1929_, 3);
                        leanh::lean_inc_ref(v_type_1935_);
                        v_value_1936_ = leanh::lean_ctor_get(v_decl_1929_, 4);
                        leanh::lean_inc_ref(v_value_1936_);
                        leanh::lean_dec_ref(v_decl_1929_);
                        v_fvarId_1937_ = leanh::lean_ctor_get(v_decl_1930_, 0);
                        leanh::lean_inc(v_fvarId_1937_);
                        v_params_1938_ = leanh::lean_ctor_get(v_decl_1930_, 2);
                        leanh::lean_inc_ref(v_params_1938_);
                        v_type_1939_ = leanh::lean_ctor_get(v_decl_1930_, 3);
                        leanh::lean_inc_ref(v_type_1939_);
                        v_value_1940_ = leanh::lean_ctor_get(v_decl_1930_, 4);
                        leanh::lean_inc_ref(v_value_1940_);
                        leanh::lean_dec_ref(v_decl_1930_);
                        v___x_1941_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(
                            v_type_1935_,
                            v_type_1939_,
                            v_a_1892_,
                        );
                        leanh::lean_dec_ref(v_type_1939_);
                        leanh::lean_dec_ref(v_type_1935_);
                        if v___x_1941_ == 0 {
                            leanh::lean_dec_ref(v_value_1940_);
                            leanh::lean_dec_ref(v_params_1938_);
                            leanh::lean_dec(v_fvarId_1937_);
                            leanh::lean_dec_ref(v_value_1936_);
                            leanh::lean_dec_ref(v_params_1934_);
                            leanh::lean_dec(v_fvarId_1933_);
                            leanh::lean_dec_ref(v_k_1932_);
                            leanh::lean_dec_ref(v_k_1931_);
                            leanh::lean_dec(v_a_1892_);
                            return v___x_1941_;
                        } else {
                            v___x_1942_ = lean_array_get_size(v_params_1938_);
                            v___x_1943_ = lean_array_get_size(v_params_1934_);
                            v___x_1944_ = lean_nat_dec_eq(v___x_1942_, v___x_1943_);
                            if v___x_1944_ == 0 {
                                leanh::lean_dec_ref(v_value_1940_);
                                leanh::lean_dec_ref(v_params_1938_);
                                leanh::lean_dec(v_fvarId_1937_);
                                leanh::lean_dec_ref(v_value_1936_);
                                leanh::lean_dec_ref(v_params_1934_);
                                leanh::lean_dec(v_fvarId_1933_);
                                leanh::lean_dec_ref(v_k_1932_);
                                leanh::lean_dec_ref(v_k_1931_);
                                leanh::lean_dec(v_a_1892_);
                                return v___x_1944_;
                            } else {
                                v___x_1945_ = leanh::lean_unsigned_to_nat(0);
                                leanh::lean_inc(v_a_1892_);
                                v___x_1946_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_1889_, v_value_1936_, v_value_1940_, v_params_1934_, v_params_1938_, v___x_1945_, v_a_1892_);
                                leanh::lean_dec_ref(v_params_1938_);
                                leanh::lean_dec_ref(v_params_1934_);
                                if v___x_1946_ == 0 {
                                    leanh::lean_dec(v_fvarId_1937_);
                                    leanh::lean_dec(v_fvarId_1933_);
                                    leanh::lean_dec_ref(v_k_1932_);
                                    leanh::lean_dec_ref(v_k_1931_);
                                    leanh::lean_dec(v_a_1892_);
                                    return v___x_1946_;
                                } else {
                                    v___x_1947_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1937_, v_fvarId_1933_, v_a_1892_);
                                    v_code_u2081_1890_ = v_k_1931_;
                                    v_code_u2082_1891_ = v_k_1932_;
                                    v_a_1892_ = v___x_1947_;
                                    state = 0;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 2);
                        leanh::lean_dec(v_a_1892_);
                        leanh::lean_dec_ref(v_code_u2082_1891_);
                        v___x_1949_ = 0;
                        return v___x_1949_;
                    }
                }
                3 => {
                    if leanh::lean_obj_tag(v_code_u2082_1891_) == 3 {
                        v_fvarId_1950_ = leanh::lean_ctor_get(v_code_u2081_1890_, 0);
                        leanh::lean_inc(v_fvarId_1950_);
                        v_args_1951_ = leanh::lean_ctor_get(v_code_u2081_1890_, 1);
                        leanh::lean_inc_ref(v_args_1951_);
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 2);
                        v_fvarId_1952_ = leanh::lean_ctor_get(v_code_u2082_1891_, 0);
                        leanh::lean_inc(v_fvarId_1952_);
                        v_args_1953_ = leanh::lean_ctor_get(v_code_u2082_1891_, 1);
                        leanh::lean_inc_ref(v_args_1953_);
                        leanh::lean_dec_ref_known(v_code_u2082_1891_, 2);
                        v___x_1954_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                            v_fvarId_1950_,
                            v_fvarId_1952_,
                            v_a_1892_,
                        );
                        leanh::lean_dec(v_fvarId_1952_);
                        leanh::lean_dec(v_fvarId_1950_);
                        if v___x_1954_ == 0 {
                            leanh::lean_dec_ref(v_args_1953_);
                            leanh::lean_dec_ref(v_args_1951_);
                            leanh::lean_dec(v_a_1892_);
                            return v___x_1954_;
                        } else {
                            v___x_1955_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(
                                v_pu_1889_,
                                v_args_1951_,
                                v_args_1953_,
                                v_a_1892_,
                            );
                            leanh::lean_dec(v_a_1892_);
                            leanh::lean_dec_ref(v_args_1951_);
                            return v___x_1955_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 2);
                        leanh::lean_dec(v_a_1892_);
                        leanh::lean_dec_ref(v_code_u2082_1891_);
                        v___x_1956_ = 0;
                        return v___x_1956_;
                    }
                }
                4 => {
                    if leanh::lean_obj_tag(v_code_u2082_1891_) == 4 {
                        v_cases_1957_ = leanh::lean_ctor_get(v_code_u2081_1890_, 0);
                        leanh::lean_inc_ref(v_cases_1957_);
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 1);
                        v_cases_1958_ = leanh::lean_ctor_get(v_code_u2082_1891_, 0);
                        leanh::lean_inc_ref(v_cases_1958_);
                        leanh::lean_dec_ref_known(v_code_u2082_1891_, 1);
                        v_resultType_1959_ = leanh::lean_ctor_get(v_cases_1957_, 1);
                        leanh::lean_inc_ref(v_resultType_1959_);
                        v_discr_1960_ = leanh::lean_ctor_get(v_cases_1957_, 2);
                        leanh::lean_inc(v_discr_1960_);
                        v_alts_1961_ = leanh::lean_ctor_get(v_cases_1957_, 3);
                        leanh::lean_inc_ref(v_alts_1961_);
                        leanh::lean_dec_ref(v_cases_1957_);
                        v_resultType_1962_ = leanh::lean_ctor_get(v_cases_1958_, 1);
                        leanh::lean_inc_ref(v_resultType_1962_);
                        v_discr_1963_ = leanh::lean_ctor_get(v_cases_1958_, 2);
                        leanh::lean_inc(v_discr_1963_);
                        v_alts_1964_ = leanh::lean_ctor_get(v_cases_1958_, 3);
                        leanh::lean_inc_ref(v_alts_1964_);
                        leanh::lean_dec_ref(v_cases_1958_);
                        v___x_1965_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                            v_discr_1960_,
                            v_discr_1963_,
                            v_a_1892_,
                        );
                        leanh::lean_dec(v_discr_1963_);
                        leanh::lean_dec(v_discr_1960_);
                        if v___x_1965_ == 0 {
                            leanh::lean_dec_ref(v_alts_1964_);
                            leanh::lean_dec_ref(v_resultType_1962_);
                            leanh::lean_dec_ref(v_alts_1961_);
                            leanh::lean_dec_ref(v_resultType_1959_);
                            leanh::lean_dec(v_a_1892_);
                            return v___x_1965_;
                        } else {
                            v___x_1966_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(
                                v_resultType_1959_,
                                v_resultType_1962_,
                                v_a_1892_,
                            );
                            leanh::lean_dec_ref(v_resultType_1962_);
                            leanh::lean_dec_ref(v_resultType_1959_);
                            if v___x_1966_ == 0 {
                                leanh::lean_dec_ref(v_alts_1964_);
                                leanh::lean_dec_ref(v_alts_1961_);
                                leanh::lean_dec(v_a_1892_);
                                return v___x_1966_;
                            } else {
                                v___x_1967_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(
                                    v_pu_1889_,
                                    v_alts_1961_,
                                    v_alts_1964_,
                                    v_a_1892_,
                                );
                                leanh::lean_dec(v_a_1892_);
                                return v___x_1967_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 1);
                        leanh::lean_dec(v_a_1892_);
                        leanh::lean_dec_ref(v_code_u2082_1891_);
                        v___x_1968_ = 0;
                        return v___x_1968_;
                    }
                }
                5 => {
                    if leanh::lean_obj_tag(v_code_u2082_1891_) == 5 {
                        v_fvarId_1969_ = leanh::lean_ctor_get(v_code_u2081_1890_, 0);
                        leanh::lean_inc(v_fvarId_1969_);
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 1);
                        v_fvarId_1970_ = leanh::lean_ctor_get(v_code_u2082_1891_, 0);
                        leanh::lean_inc(v_fvarId_1970_);
                        leanh::lean_dec_ref_known(v_code_u2082_1891_, 1);
                        v___x_1971_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                            v_fvarId_1969_,
                            v_fvarId_1970_,
                            v_a_1892_,
                        );
                        leanh::lean_dec(v_a_1892_);
                        leanh::lean_dec(v_fvarId_1970_);
                        leanh::lean_dec(v_fvarId_1969_);
                        return v___x_1971_;
                    } else {
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 1);
                        leanh::lean_dec(v_a_1892_);
                        leanh::lean_dec_ref(v_code_u2082_1891_);
                        v___x_1972_ = 0;
                        return v___x_1972_;
                    }
                }
                6 => {
                    if leanh::lean_obj_tag(v_code_u2082_1891_) == 6 {
                        v_type_1973_ = leanh::lean_ctor_get(v_code_u2081_1890_, 0);
                        leanh::lean_inc_ref(v_type_1973_);
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 1);
                        v_type_1974_ = leanh::lean_ctor_get(v_code_u2082_1891_, 0);
                        leanh::lean_inc_ref(v_type_1974_);
                        leanh::lean_dec_ref_known(v_code_u2082_1891_, 1);
                        v___x_1975_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(
                            v_type_1973_,
                            v_type_1974_,
                            v_a_1892_,
                        );
                        leanh::lean_dec(v_a_1892_);
                        leanh::lean_dec_ref(v_type_1974_);
                        leanh::lean_dec_ref(v_type_1973_);
                        return v___x_1975_;
                    } else {
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 1);
                        leanh::lean_dec(v_a_1892_);
                        leanh::lean_dec_ref(v_code_u2082_1891_);
                        v___x_1976_ = 0;
                        return v___x_1976_;
                    }
                }
                7 => {
                    if leanh::lean_obj_tag(v_code_u2082_1891_) == 7 {
                        v_fvarId_1977_ = leanh::lean_ctor_get(v_code_u2081_1890_, 0);
                        leanh::lean_inc(v_fvarId_1977_);
                        v_i_1978_ = leanh::lean_ctor_get(v_code_u2081_1890_, 1);
                        leanh::lean_inc(v_i_1978_);
                        v_y_1979_ = leanh::lean_ctor_get(v_code_u2081_1890_, 2);
                        leanh::lean_inc(v_y_1979_);
                        v_k_1980_ = leanh::lean_ctor_get(v_code_u2081_1890_, 3);
                        leanh::lean_inc_ref(v_k_1980_);
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 4);
                        v_fvarId_1981_ = leanh::lean_ctor_get(v_code_u2082_1891_, 0);
                        leanh::lean_inc(v_fvarId_1981_);
                        v_i_1982_ = leanh::lean_ctor_get(v_code_u2082_1891_, 1);
                        leanh::lean_inc(v_i_1982_);
                        v_y_1983_ = leanh::lean_ctor_get(v_code_u2082_1891_, 2);
                        leanh::lean_inc(v_y_1983_);
                        v_k_1984_ = leanh::lean_ctor_get(v_code_u2082_1891_, 3);
                        leanh::lean_inc_ref(v_k_1984_);
                        leanh::lean_dec_ref_known(v_code_u2082_1891_, 4);
                        v___x_1985_ = lean_nat_dec_eq(v_i_1978_, v_i_1982_);
                        leanh::lean_dec(v_i_1982_);
                        leanh::lean_dec(v_i_1978_);
                        if v___x_1985_ == 0 {
                            leanh::lean_dec_ref(v_k_1984_);
                            leanh::lean_dec(v_y_1983_);
                            leanh::lean_dec(v_fvarId_1981_);
                            leanh::lean_dec_ref(v_k_1980_);
                            leanh::lean_dec(v_y_1979_);
                            leanh::lean_dec(v_fvarId_1977_);
                            leanh::lean_dec(v_a_1892_);
                            return v___x_1985_;
                        } else {
                            v___x_1986_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                                v_fvarId_1977_,
                                v_fvarId_1981_,
                                v_a_1892_,
                            );
                            leanh::lean_dec(v_fvarId_1981_);
                            leanh::lean_dec(v_fvarId_1977_);
                            if v___x_1986_ == 0 {
                                leanh::lean_dec_ref(v_k_1984_);
                                leanh::lean_dec(v_y_1983_);
                                leanh::lean_dec_ref(v_k_1980_);
                                leanh::lean_dec(v_y_1979_);
                                leanh::lean_dec(v_a_1892_);
                                return v___x_1986_;
                            } else {
                                v___x_1987_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(
                                    v_y_1979_, v_y_1983_, v_a_1892_,
                                );
                                leanh::lean_dec(v_y_1983_);
                                leanh::lean_dec(v_y_1979_);
                                if v___x_1987_ == 0 {
                                    leanh::lean_dec_ref(v_k_1984_);
                                    leanh::lean_dec_ref(v_k_1980_);
                                    leanh::lean_dec(v_a_1892_);
                                    return v___x_1987_;
                                } else {
                                    v_code_u2081_1890_ = v_k_1980_;
                                    v_code_u2082_1891_ = v_k_1984_;
                                    state = 0;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 4);
                        leanh::lean_dec(v_a_1892_);
                        leanh::lean_dec_ref(v_code_u2082_1891_);
                        v___x_1989_ = 0;
                        return v___x_1989_;
                    }
                }
                8 => {
                    if leanh::lean_obj_tag(v_code_u2082_1891_) == 8 {
                        v_fvarId_1990_ = leanh::lean_ctor_get(v_code_u2081_1890_, 0);
                        leanh::lean_inc(v_fvarId_1990_);
                        v_i_1991_ = leanh::lean_ctor_get(v_code_u2081_1890_, 1);
                        leanh::lean_inc(v_i_1991_);
                        v_y_1992_ = leanh::lean_ctor_get(v_code_u2081_1890_, 2);
                        leanh::lean_inc(v_y_1992_);
                        v_k_1993_ = leanh::lean_ctor_get(v_code_u2081_1890_, 3);
                        leanh::lean_inc_ref(v_k_1993_);
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 4);
                        v_fvarId_1994_ = leanh::lean_ctor_get(v_code_u2082_1891_, 0);
                        leanh::lean_inc(v_fvarId_1994_);
                        v_i_1995_ = leanh::lean_ctor_get(v_code_u2082_1891_, 1);
                        leanh::lean_inc(v_i_1995_);
                        v_y_1996_ = leanh::lean_ctor_get(v_code_u2082_1891_, 2);
                        leanh::lean_inc(v_y_1996_);
                        v_k_1997_ = leanh::lean_ctor_get(v_code_u2082_1891_, 3);
                        leanh::lean_inc_ref(v_k_1997_);
                        leanh::lean_dec_ref_known(v_code_u2082_1891_, 4);
                        v___x_1998_ = lean_nat_dec_eq(v_i_1991_, v_i_1995_);
                        leanh::lean_dec(v_i_1995_);
                        leanh::lean_dec(v_i_1991_);
                        if v___x_1998_ == 0 {
                            leanh::lean_dec_ref(v_k_1997_);
                            leanh::lean_dec(v_y_1996_);
                            leanh::lean_dec(v_fvarId_1994_);
                            leanh::lean_dec_ref(v_k_1993_);
                            leanh::lean_dec(v_y_1992_);
                            leanh::lean_dec(v_fvarId_1990_);
                            leanh::lean_dec(v_a_1892_);
                            return v___x_1998_;
                        } else {
                            v___x_1999_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                                v_fvarId_1990_,
                                v_fvarId_1994_,
                                v_a_1892_,
                            );
                            leanh::lean_dec(v_fvarId_1994_);
                            leanh::lean_dec(v_fvarId_1990_);
                            if v___x_1999_ == 0 {
                                leanh::lean_dec_ref(v_k_1997_);
                                leanh::lean_dec(v_y_1996_);
                                leanh::lean_dec_ref(v_k_1993_);
                                leanh::lean_dec(v_y_1992_);
                                leanh::lean_dec(v_a_1892_);
                                return v___x_1999_;
                            } else {
                                v___x_2000_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                                    v_y_1992_, v_y_1996_, v_a_1892_,
                                );
                                leanh::lean_dec(v_y_1996_);
                                leanh::lean_dec(v_y_1992_);
                                if v___x_2000_ == 0 {
                                    leanh::lean_dec_ref(v_k_1997_);
                                    leanh::lean_dec_ref(v_k_1993_);
                                    leanh::lean_dec(v_a_1892_);
                                    return v___x_2000_;
                                } else {
                                    v_code_u2081_1890_ = v_k_1993_;
                                    v_code_u2082_1891_ = v_k_1997_;
                                    state = 0;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 4);
                        leanh::lean_dec(v_a_1892_);
                        leanh::lean_dec_ref(v_code_u2082_1891_);
                        v___x_2002_ = 0;
                        return v___x_2002_;
                    }
                }
                9 => {
                    if leanh::lean_obj_tag(v_code_u2082_1891_) == 9 {
                        v_fvarId_2003_ = leanh::lean_ctor_get(v_code_u2081_1890_, 0);
                        leanh::lean_inc(v_fvarId_2003_);
                        v_i_2004_ = leanh::lean_ctor_get(v_code_u2081_1890_, 1);
                        leanh::lean_inc(v_i_2004_);
                        v_offset_2005_ = leanh::lean_ctor_get(v_code_u2081_1890_, 2);
                        leanh::lean_inc(v_offset_2005_);
                        v_y_2006_ = leanh::lean_ctor_get(v_code_u2081_1890_, 3);
                        leanh::lean_inc(v_y_2006_);
                        v_ty_2007_ = leanh::lean_ctor_get(v_code_u2081_1890_, 4);
                        leanh::lean_inc_ref(v_ty_2007_);
                        v_k_2008_ = leanh::lean_ctor_get(v_code_u2081_1890_, 5);
                        leanh::lean_inc_ref(v_k_2008_);
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 6);
                        v_fvarId_2009_ = leanh::lean_ctor_get(v_code_u2082_1891_, 0);
                        leanh::lean_inc(v_fvarId_2009_);
                        v_i_2010_ = leanh::lean_ctor_get(v_code_u2082_1891_, 1);
                        leanh::lean_inc(v_i_2010_);
                        v_offset_2011_ = leanh::lean_ctor_get(v_code_u2082_1891_, 2);
                        leanh::lean_inc(v_offset_2011_);
                        v_y_2012_ = leanh::lean_ctor_get(v_code_u2082_1891_, 3);
                        leanh::lean_inc(v_y_2012_);
                        v_ty_2013_ = leanh::lean_ctor_get(v_code_u2082_1891_, 4);
                        leanh::lean_inc_ref(v_ty_2013_);
                        v_k_2014_ = leanh::lean_ctor_get(v_code_u2082_1891_, 5);
                        leanh::lean_inc_ref(v_k_2014_);
                        leanh::lean_dec_ref_known(v_code_u2082_1891_, 6);
                        v___x_2015_ = lean_nat_dec_eq(v_i_2004_, v_i_2010_);
                        leanh::lean_dec(v_i_2010_);
                        leanh::lean_dec(v_i_2004_);
                        if v___x_2015_ == 0 {
                            leanh::lean_dec_ref(v_k_2014_);
                            leanh::lean_dec_ref(v_ty_2013_);
                            leanh::lean_dec(v_y_2012_);
                            leanh::lean_dec(v_offset_2011_);
                            leanh::lean_dec(v_fvarId_2009_);
                            leanh::lean_dec_ref(v_k_2008_);
                            leanh::lean_dec_ref(v_ty_2007_);
                            leanh::lean_dec(v_y_2006_);
                            leanh::lean_dec(v_offset_2005_);
                            leanh::lean_dec(v_fvarId_2003_);
                            leanh::lean_dec(v_a_1892_);
                            return v___x_2015_;
                        } else {
                            v___x_2016_ = lean_nat_dec_eq(v_offset_2005_, v_offset_2011_);
                            leanh::lean_dec(v_offset_2011_);
                            leanh::lean_dec(v_offset_2005_);
                            if v___x_2016_ == 0 {
                                leanh::lean_dec_ref(v_k_2014_);
                                leanh::lean_dec_ref(v_ty_2013_);
                                leanh::lean_dec(v_y_2012_);
                                leanh::lean_dec(v_fvarId_2009_);
                                leanh::lean_dec_ref(v_k_2008_);
                                leanh::lean_dec_ref(v_ty_2007_);
                                leanh::lean_dec(v_y_2006_);
                                leanh::lean_dec(v_fvarId_2003_);
                                leanh::lean_dec(v_a_1892_);
                                return v___x_2016_;
                            } else {
                                v___x_2017_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                                    v_fvarId_2003_,
                                    v_fvarId_2009_,
                                    v_a_1892_,
                                );
                                leanh::lean_dec(v_fvarId_2009_);
                                leanh::lean_dec(v_fvarId_2003_);
                                if v___x_2017_ == 0 {
                                    leanh::lean_dec_ref(v_k_2014_);
                                    leanh::lean_dec_ref(v_ty_2013_);
                                    leanh::lean_dec(v_y_2012_);
                                    leanh::lean_dec_ref(v_k_2008_);
                                    leanh::lean_dec_ref(v_ty_2007_);
                                    leanh::lean_dec(v_y_2006_);
                                    leanh::lean_dec(v_a_1892_);
                                    return v___x_2017_;
                                } else {
                                    v___x_2018_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                                        v_y_2006_, v_y_2012_, v_a_1892_,
                                    );
                                    leanh::lean_dec(v_y_2012_);
                                    leanh::lean_dec(v_y_2006_);
                                    if v___x_2018_ == 0 {
                                        leanh::lean_dec_ref(v_k_2014_);
                                        leanh::lean_dec_ref(v_ty_2013_);
                                        leanh::lean_dec_ref(v_k_2008_);
                                        leanh::lean_dec_ref(v_ty_2007_);
                                        leanh::lean_dec(v_a_1892_);
                                        return v___x_2018_;
                                    } else {
                                        v___x_2019_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(
                                            v_ty_2007_, v_ty_2013_, v_a_1892_,
                                        );
                                        leanh::lean_dec_ref(v_ty_2013_);
                                        leanh::lean_dec_ref(v_ty_2007_);
                                        if v___x_2019_ == 0 {
                                            leanh::lean_dec_ref(v_k_2014_);
                                            leanh::lean_dec_ref(v_k_2008_);
                                            leanh::lean_dec(v_a_1892_);
                                            return v___x_2019_;
                                        } else {
                                            v_code_u2081_1890_ = v_k_2008_;
                                            v_code_u2082_1891_ = v_k_2014_;
                                            state = 0;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 6);
                        leanh::lean_dec(v_a_1892_);
                        leanh::lean_dec_ref(v_code_u2082_1891_);
                        v___x_2021_ = 0;
                        return v___x_2021_;
                    }
                }
                10 => {
                    if leanh::lean_obj_tag(v_code_u2082_1891_) == 10 {
                        v_fvarId_2022_ = leanh::lean_ctor_get(v_code_u2081_1890_, 0);
                        leanh::lean_inc(v_fvarId_2022_);
                        v_cidx_2023_ = leanh::lean_ctor_get(v_code_u2081_1890_, 1);
                        leanh::lean_inc(v_cidx_2023_);
                        v_k_2024_ = leanh::lean_ctor_get(v_code_u2081_1890_, 2);
                        leanh::lean_inc_ref(v_k_2024_);
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 3);
                        v_fvarId_2025_ = leanh::lean_ctor_get(v_code_u2082_1891_, 0);
                        leanh::lean_inc(v_fvarId_2025_);
                        v_cidx_2026_ = leanh::lean_ctor_get(v_code_u2082_1891_, 1);
                        leanh::lean_inc(v_cidx_2026_);
                        v_k_2027_ = leanh::lean_ctor_get(v_code_u2082_1891_, 2);
                        leanh::lean_inc_ref(v_k_2027_);
                        leanh::lean_dec_ref_known(v_code_u2082_1891_, 3);
                        v___x_2028_ = lean_nat_dec_eq(v_cidx_2023_, v_cidx_2026_);
                        leanh::lean_dec(v_cidx_2026_);
                        leanh::lean_dec(v_cidx_2023_);
                        if v___x_2028_ == 0 {
                            leanh::lean_dec_ref(v_k_2027_);
                            leanh::lean_dec(v_fvarId_2025_);
                            leanh::lean_dec_ref(v_k_2024_);
                            leanh::lean_dec(v_fvarId_2022_);
                            leanh::lean_dec(v_a_1892_);
                            return v___x_2028_;
                        } else {
                            v___x_2029_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                                v_fvarId_2022_,
                                v_fvarId_2025_,
                                v_a_1892_,
                            );
                            leanh::lean_dec(v_fvarId_2025_);
                            leanh::lean_dec(v_fvarId_2022_);
                            if v___x_2029_ == 0 {
                                leanh::lean_dec_ref(v_k_2027_);
                                leanh::lean_dec_ref(v_k_2024_);
                                leanh::lean_dec(v_a_1892_);
                                return v___x_2029_;
                            } else {
                                v_code_u2081_1890_ = v_k_2024_;
                                v_code_u2082_1891_ = v_k_2027_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 3);
                        leanh::lean_dec(v_a_1892_);
                        leanh::lean_dec_ref(v_code_u2082_1891_);
                        v___x_2031_ = 0;
                        return v___x_2031_;
                    }
                }
                11 => {
                    if leanh::lean_obj_tag(v_code_u2082_1891_) == 11 {
                        v_fvarId_2032_ = leanh::lean_ctor_get(v_code_u2081_1890_, 0);
                        leanh::lean_inc(v_fvarId_2032_);
                        v_n_2033_ = leanh::lean_ctor_get(v_code_u2081_1890_, 1);
                        leanh::lean_inc(v_n_2033_);
                        v_check_2034_ = leanh::lean_ctor_get_uint8(
                            v_code_u2081_1890_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v_persistent_2035_ = leanh::lean_ctor_get_uint8(
                            v_code_u2081_1890_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                        );
                        v_k_2036_ = leanh::lean_ctor_get(v_code_u2081_1890_, 2);
                        leanh::lean_inc_ref(v_k_2036_);
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 3);
                        v_fvarId_2037_ = leanh::lean_ctor_get(v_code_u2082_1891_, 0);
                        leanh::lean_inc(v_fvarId_2037_);
                        v_n_2038_ = leanh::lean_ctor_get(v_code_u2082_1891_, 1);
                        leanh::lean_inc(v_n_2038_);
                        v_check_2039_ = leanh::lean_ctor_get_uint8(
                            v_code_u2082_1891_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v_persistent_2040_ = leanh::lean_ctor_get_uint8(
                            v_code_u2082_1891_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                        );
                        v_k_2041_ = leanh::lean_ctor_get(v_code_u2082_1891_, 2);
                        leanh::lean_inc_ref(v_k_2041_);
                        leanh::lean_dec_ref_known(v_code_u2082_1891_, 3);
                        v___x_2047_ = lean_nat_dec_eq(v_n_2033_, v_n_2038_);
                        leanh::lean_dec(v_n_2038_);
                        leanh::lean_dec(v_n_2033_);
                        if v___x_2047_ == 0 {
                            leanh::lean_dec_ref(v_k_2041_);
                            leanh::lean_dec(v_fvarId_2037_);
                            leanh::lean_dec_ref(v_k_2036_);
                            leanh::lean_dec(v_fvarId_2032_);
                            leanh::lean_dec(v_a_1892_);
                            return v___x_2047_;
                        } else {
                            if v_check_2034_ == 0 {
                                if v_check_2039_ == 0 {
                                    v___y_2046_ = v___x_2047_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_k_2041_);
                                    leanh::lean_dec(v_fvarId_2037_);
                                    leanh::lean_dec_ref(v_k_2036_);
                                    leanh::lean_dec(v_fvarId_2032_);
                                    leanh::lean_dec(v_a_1892_);
                                    return v_check_2034_;
                                }
                            } else {
                                v___y_2046_ = v_check_2039_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 3);
                        leanh::lean_dec(v_a_1892_);
                        leanh::lean_dec_ref(v_code_u2082_1891_);
                        v___x_2048_ = 0;
                        return v___x_2048_;
                    }
                }
                12 => {
                    if leanh::lean_obj_tag(v_code_u2082_1891_) == 12 {
                        v_fvarId_2049_ = leanh::lean_ctor_get(v_code_u2081_1890_, 0);
                        leanh::lean_inc(v_fvarId_2049_);
                        v_n_2050_ = leanh::lean_ctor_get(v_code_u2081_1890_, 1);
                        leanh::lean_inc(v_n_2050_);
                        v_check_2051_ = leanh::lean_ctor_get_uint8(
                            v_code_u2081_1890_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        );
                        v_persistent_2052_ = leanh::lean_ctor_get_uint8(
                            v_code_u2081_1890_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                        );
                        v_objs_x3f_2053_ = leanh::lean_ctor_get(v_code_u2081_1890_, 2);
                        leanh::lean_inc(v_objs_x3f_2053_);
                        v_k_2054_ = leanh::lean_ctor_get(v_code_u2081_1890_, 3);
                        leanh::lean_inc_ref(v_k_2054_);
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 4);
                        v_fvarId_2055_ = leanh::lean_ctor_get(v_code_u2082_1891_, 0);
                        leanh::lean_inc(v_fvarId_2055_);
                        v_n_2056_ = leanh::lean_ctor_get(v_code_u2082_1891_, 1);
                        leanh::lean_inc(v_n_2056_);
                        v_check_2057_ = leanh::lean_ctor_get_uint8(
                            v_code_u2082_1891_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        );
                        v_persistent_2058_ = leanh::lean_ctor_get_uint8(
                            v_code_u2082_1891_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                        );
                        v_objs_x3f_2059_ = leanh::lean_ctor_get(v_code_u2082_1891_, 2);
                        leanh::lean_inc(v_objs_x3f_2059_);
                        v_k_2060_ = leanh::lean_ctor_get(v_code_u2082_1891_, 3);
                        leanh::lean_inc_ref(v_k_2060_);
                        leanh::lean_dec_ref_known(v_code_u2082_1891_, 4);
                        v___x_2067_ = lean_nat_dec_eq(v_n_2050_, v_n_2056_);
                        leanh::lean_dec(v_n_2056_);
                        leanh::lean_dec(v_n_2050_);
                        if v___x_2067_ == 0 {
                            leanh::lean_dec_ref(v_k_2060_);
                            leanh::lean_dec(v_objs_x3f_2059_);
                            leanh::lean_dec(v_fvarId_2055_);
                            leanh::lean_dec_ref(v_k_2054_);
                            leanh::lean_dec(v_objs_x3f_2053_);
                            leanh::lean_dec(v_fvarId_2049_);
                            leanh::lean_dec(v_a_1892_);
                            return v___x_2067_;
                        } else {
                            if v_check_2051_ == 0 {
                                if v_check_2057_ == 0 {
                                    v___y_2066_ = v___x_2067_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_k_2060_);
                                    leanh::lean_dec(v_objs_x3f_2059_);
                                    leanh::lean_dec(v_fvarId_2055_);
                                    leanh::lean_dec_ref(v_k_2054_);
                                    leanh::lean_dec(v_objs_x3f_2053_);
                                    leanh::lean_dec(v_fvarId_2049_);
                                    leanh::lean_dec(v_a_1892_);
                                    return v_check_2051_;
                                }
                            } else {
                                v___y_2066_ = v_check_2057_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 4);
                        leanh::lean_dec(v_a_1892_);
                        leanh::lean_dec_ref(v_code_u2082_1891_);
                        v___x_2068_ = 0;
                        return v___x_2068_;
                    }
                }
                _ => {
                    if leanh::lean_obj_tag(v_code_u2082_1891_) == 13 {
                        v_fvarId_2069_ = leanh::lean_ctor_get(v_code_u2081_1890_, 0);
                        leanh::lean_inc(v_fvarId_2069_);
                        v_k_2070_ = leanh::lean_ctor_get(v_code_u2081_1890_, 1);
                        leanh::lean_inc_ref(v_k_2070_);
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 2);
                        v_fvarId_2071_ = leanh::lean_ctor_get(v_code_u2082_1891_, 0);
                        leanh::lean_inc(v_fvarId_2071_);
                        v_k_2072_ = leanh::lean_ctor_get(v_code_u2082_1891_, 1);
                        leanh::lean_inc_ref(v_k_2072_);
                        leanh::lean_dec_ref_known(v_code_u2082_1891_, 2);
                        v___x_2073_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                            v_fvarId_2069_,
                            v_fvarId_2071_,
                            v_a_1892_,
                        );
                        leanh::lean_dec(v_fvarId_2071_);
                        leanh::lean_dec(v_fvarId_2069_);
                        if v___x_2073_ == 0 {
                            leanh::lean_dec_ref(v_k_2072_);
                            leanh::lean_dec_ref(v_k_2070_);
                            leanh::lean_dec(v_a_1892_);
                            return v___x_2073_;
                        } else {
                            v_code_u2081_1890_ = v_k_2070_;
                            v_code_u2082_1891_ = v_k_2072_;
                            state = 0;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_u2081_1890_, 2);
                        leanh::lean_dec(v_a_1892_);
                        leanh::lean_dec_ref(v_code_u2082_1891_);
                        v___x_2075_ = 0;
                        return v___x_2075_;
                    }
                }
            },
            1 => {
                v___x_2043_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                    v_fvarId_2032_,
                    v_fvarId_2037_,
                    v_a_1892_,
                );
                leanh::lean_dec(v_fvarId_2037_);
                leanh::lean_dec(v_fvarId_2032_);
                if v___x_2043_ == 0 {
                    leanh::lean_dec_ref(v_k_2041_);
                    leanh::lean_dec_ref(v_k_2036_);
                    leanh::lean_dec(v_a_1892_);
                    return v___x_2043_;
                } else {
                    v_code_u2081_1890_ = v_k_2036_;
                    v_code_u2082_1891_ = v_k_2041_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_2046_ == 0 {
                    leanh::lean_dec_ref(v_k_2041_);
                    leanh::lean_dec(v_fvarId_2037_);
                    leanh::lean_dec_ref(v_k_2036_);
                    leanh::lean_dec(v_fvarId_2032_);
                    leanh::lean_dec(v_a_1892_);
                    return v___y_2046_;
                } else {
                    if v_persistent_2035_ == 0 {
                        if v_persistent_2040_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_k_2041_);
                            leanh::lean_dec(v_fvarId_2037_);
                            leanh::lean_dec_ref(v_k_2036_);
                            leanh::lean_dec(v_fvarId_2032_);
                            leanh::lean_dec(v_a_1892_);
                            return v_persistent_2035_;
                        }
                    } else {
                        if v_persistent_2040_ == 0 {
                            leanh::lean_dec_ref(v_k_2041_);
                            leanh::lean_dec(v_fvarId_2037_);
                            leanh::lean_dec_ref(v_k_2036_);
                            leanh::lean_dec(v_fvarId_2032_);
                            leanh::lean_dec(v_a_1892_);
                            return v_persistent_2040_;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_2062_ = l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3(
                    v_objs_x3f_2053_,
                    v_objs_x3f_2059_,
                );
                leanh::lean_dec(v_objs_x3f_2059_);
                leanh::lean_dec(v_objs_x3f_2053_);
                if v___x_2062_ == 0 {
                    leanh::lean_dec_ref(v_k_2060_);
                    leanh::lean_dec(v_fvarId_2055_);
                    leanh::lean_dec_ref(v_k_2054_);
                    leanh::lean_dec(v_fvarId_2049_);
                    leanh::lean_dec(v_a_1892_);
                    return v___x_2062_;
                } else {
                    v___x_2063_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(
                        v_fvarId_2049_,
                        v_fvarId_2055_,
                        v_a_1892_,
                    );
                    leanh::lean_dec(v_fvarId_2055_);
                    leanh::lean_dec(v_fvarId_2049_);
                    if v___x_2063_ == 0 {
                        leanh::lean_dec_ref(v_k_2060_);
                        leanh::lean_dec_ref(v_k_2054_);
                        leanh::lean_dec(v_a_1892_);
                        return v___x_2063_;
                    } else {
                        v_code_u2081_1890_ = v_k_2054_;
                        v_code_u2082_1891_ = v_k_2060_;
                        state = 0;
                        continue;
                    }
                }
            }
            4 => {
                if v___y_2066_ == 0 {
                    leanh::lean_dec_ref(v_k_2060_);
                    leanh::lean_dec(v_objs_x3f_2059_);
                    leanh::lean_dec(v_fvarId_2055_);
                    leanh::lean_dec_ref(v_k_2054_);
                    leanh::lean_dec(v_objs_x3f_2053_);
                    leanh::lean_dec(v_fvarId_2049_);
                    leanh::lean_dec(v_a_1892_);
                    return v___y_2066_;
                } else {
                    if v_persistent_2052_ == 0 {
                        if v_persistent_2058_ == 0 {
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_k_2060_);
                            leanh::lean_dec(v_objs_x3f_2059_);
                            leanh::lean_dec(v_fvarId_2055_);
                            leanh::lean_dec_ref(v_k_2054_);
                            leanh::lean_dec(v_objs_x3f_2053_);
                            leanh::lean_dec(v_fvarId_2049_);
                            leanh::lean_dec(v_a_1892_);
                            return v_persistent_2052_;
                        }
                    } else {
                        if v_persistent_2058_ == 0 {
                            leanh::lean_dec_ref(v_k_2060_);
                            leanh::lean_dec(v_objs_x3f_2059_);
                            leanh::lean_dec(v_fvarId_2055_);
                            leanh::lean_dec_ref(v_k_2054_);
                            leanh::lean_dec(v_objs_x3f_2053_);
                            leanh::lean_dec(v_fvarId_2049_);
                            leanh::lean_dec(v_a_1892_);
                            return v_persistent_2058_;
                        } else {
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(
    mut v_pu_2076_: u8,
    mut v_code_2077_: *mut leanh::LeanObject,
    mut v_code_2078_: *mut leanh::LeanObject,
    mut v_params_u2081_2079_: *mut leanh::LeanObject,
    mut v_params_u2082_2080_: *mut leanh::LeanObject,
    mut v_i_2081_: *mut leanh::LeanObject,
    mut v_a_2082_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: u8 = 0;
    let mut v___x_2085_: u8 = 0;
    let mut v_p_u2081_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_u2082_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: u8 = 0;
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2083_ = lean_array_get_size(v_params_u2081_2079_);
                v___x_2084_ = lean_nat_dec_lt(v_i_2081_, v___x_2083_);
                if v___x_2084_ == 0 {
                    leanh::lean_dec(v_i_2081_);
                    v___x_2085_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(
                        v_pu_2076_,
                        v_code_2077_,
                        v_code_2078_,
                        v_a_2082_,
                    );
                    return v___x_2085_;
                } else {
                    v_p_u2081_2086_ = lean_array_fget_borrowed(v_params_u2081_2079_, v_i_2081_);
                    v_fvarId_2087_ = leanh::lean_ctor_get(v_p_u2081_2086_, 0);
                    v_type_2088_ = leanh::lean_ctor_get(v_p_u2081_2086_, 2);
                    v_p_u2082_2089_ = lean_array_fget_borrowed(v_params_u2082_2080_, v_i_2081_);
                    v_fvarId_2090_ = leanh::lean_ctor_get(v_p_u2082_2089_, 0);
                    v_type_2091_ = leanh::lean_ctor_get(v_p_u2082_2089_, 2);
                    v___x_2092_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(
                        v_type_2088_,
                        v_type_2091_,
                        v_a_2082_,
                    );
                    if v___x_2092_ == 0 {
                        leanh::lean_dec(v_a_2082_);
                        leanh::lean_dec(v_i_2081_);
                        leanh::lean_dec_ref(v_code_2078_);
                        leanh::lean_dec_ref(v_code_2077_);
                        return v___x_2092_;
                    } else {
                        v___x_2093_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2094_ = lean_nat_add(v_i_2081_, v___x_2093_);
                        leanh::lean_dec(v_i_2081_);
                        leanh::lean_inc(v_fvarId_2087_);
                        leanh::lean_inc(v_fvarId_2090_);
                        v___x_2095_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_2090_, v_fvarId_2087_, v_a_2082_);
                        v_i_2081_ = v___x_2094_;
                        v_a_2082_ = v___x_2095_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg___boxed(
    mut v_pu_2097_: *mut leanh::LeanObject,
    mut v_code_2098_: *mut leanh::LeanObject,
    mut v_code_2099_: *mut leanh::LeanObject,
    mut v_params_u2081_2100_: *mut leanh::LeanObject,
    mut v_params_u2082_2101_: *mut leanh::LeanObject,
    mut v_i_2102_: *mut leanh::LeanObject,
    mut v_a_2103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_2104_: u8 = 0;
    let mut v_res_2105_: u8 = 0;
    let mut v_r_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2104_ = (leanh::lean_unbox(v_pu_2097_) as u8);
    v_res_2105_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_boxed_2104_, v_code_2098_, v_code_2099_, v_params_u2081_2100_, v_params_u2082_2101_, v_i_2102_, v_a_2103_);
    leanh::lean_dec_ref(v_params_u2082_2101_);
    leanh::lean_dec_ref(v_params_u2081_2100_);
    v_r_2106_ = leanh::lean_box((v_res_2105_) as usize);
    return v_r_2106_;
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts___boxed(
    mut v_pu_2107_: *mut leanh::LeanObject,
    mut v_alts_u2081_2108_: *mut leanh::LeanObject,
    mut v_alts_u2082_2109_: *mut leanh::LeanObject,
    mut v_a_2110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_2111_: u8 = 0;
    let mut v_res_2112_: u8 = 0;
    let mut v_r_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2111_ = (leanh::lean_unbox(v_pu_2107_) as u8);
    v_res_2112_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(
        v_pu_boxed_2111_,
        v_alts_u2081_2108_,
        v_alts_u2082_2109_,
        v_a_2110_,
    );
    leanh::lean_dec(v_a_2110_);
    v_r_2113_ = leanh::lean_box((v_res_2112_) as usize);
    return v_r_2113_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___boxed(
    mut v_pu_2114_: *mut leanh::LeanObject,
    mut v_as_2115_: *mut leanh::LeanObject,
    mut v_sz_2116_: *mut leanh::LeanObject,
    mut v_i_2117_: *mut leanh::LeanObject,
    mut v_b_2118_: *mut leanh::LeanObject,
    mut v___y_2119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_2120_: u8 = 0;
    let mut v_sz_boxed_2121_: usize = 0;
    let mut v_i_boxed_2122_: usize = 0;
    let mut v_res_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2120_ = (leanh::lean_unbox(v_pu_2114_) as u8);
    v_sz_boxed_2121_ = leanh::lean_unbox_usize(v_sz_2116_);
    leanh::lean_dec(v_sz_2116_);
    v_i_boxed_2122_ = leanh::lean_unbox_usize(v_i_2117_);
    leanh::lean_dec(v_i_2117_);
    v_res_2123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(v_pu_boxed_2120_, v_as_2115_, v_sz_boxed_2121_, v_i_boxed_2122_, v_b_2118_, v___y_2119_);
    leanh::lean_dec(v___y_2119_);
    leanh::lean_dec_ref(v_as_2115_);
    return v_res_2123_;
}
pub unsafe fn l_Lean_Compiler_LCNF_AlphaEqv_eqv___boxed(
    mut v_pu_2124_: *mut leanh::LeanObject,
    mut v_code_u2081_2125_: *mut leanh::LeanObject,
    mut v_code_u2082_2126_: *mut leanh::LeanObject,
    mut v_a_2127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_2128_: u8 = 0;
    let mut v_res_2129_: u8 = 0;
    let mut v_r_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2128_ = (leanh::lean_unbox(v_pu_2124_) as u8);
    v_res_2129_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(
        v_pu_boxed_2128_,
        v_code_u2081_2125_,
        v_code_u2082_2126_,
        v_a_2127_,
    );
    v_r_2130_ = leanh::lean_box((v_res_2129_) as usize);
    return v_r_2130_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0(
    mut v_pu_2131_: u8,
    mut v_code_2132_: *mut leanh::LeanObject,
    mut v_code_2133_: *mut leanh::LeanObject,
    mut v_pu_2134_: u8,
    mut v_params_u2081_2135_: *mut leanh::LeanObject,
    mut v_params_u2082_2136_: *mut leanh::LeanObject,
    mut v_h_2137_: *mut leanh::LeanObject,
    mut v_i_2138_: *mut leanh::LeanObject,
    mut v_a_2139_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2140_: u8 = 0;
    leanh::lean_inc(v_a_2139_);
    v___x_2140_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_2131_, v_code_2132_, v_code_2133_, v_params_u2081_2135_, v_params_u2082_2136_, v_i_2138_, v_a_2139_);
    return v___x_2140_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___boxed(
    mut v_pu_2141_: *mut leanh::LeanObject,
    mut v_code_2142_: *mut leanh::LeanObject,
    mut v_code_2143_: *mut leanh::LeanObject,
    mut v_pu_2144_: *mut leanh::LeanObject,
    mut v_params_u2081_2145_: *mut leanh::LeanObject,
    mut v_params_u2082_2146_: *mut leanh::LeanObject,
    mut v_h_2147_: *mut leanh::LeanObject,
    mut v_i_2148_: *mut leanh::LeanObject,
    mut v_a_2149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_2150_: u8 = 0;
    let mut v_pu_boxed_2151_: u8 = 0;
    let mut v_res_2152_: u8 = 0;
    let mut v_r_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2150_ = (leanh::lean_unbox(v_pu_2141_) as u8);
    v_pu_boxed_2151_ = (leanh::lean_unbox(v_pu_2144_) as u8);
    v_res_2152_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0(v_pu_boxed_2150_, v_code_2142_, v_code_2143_, v_pu_boxed_2151_, v_params_u2081_2145_, v_params_u2082_2146_, v_h_2147_, v_i_2148_, v_a_2149_);
    leanh::lean_dec(v_a_2149_);
    leanh::lean_dec_ref(v_params_u2082_2146_);
    leanh::lean_dec_ref(v_params_u2081_2145_);
    v_r_2153_ = leanh::lean_box((v_res_2152_) as usize);
    return v_r_2153_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_alphaEqv(
    mut v_pu_2154_: u8,
    mut v_c_u2081_2155_: *mut leanh::LeanObject,
    mut v_c_u2082_2156_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: u8 = 0;
    v___x_2157_ = leanh::lean_box(1);
    v___x_2158_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(
        v_pu_2154_,
        v_c_u2081_2155_,
        v_c_u2082_2156_,
        v___x_2157_,
    );
    return v___x_2158_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_alphaEqv___boxed(
    mut v_pu_2159_: *mut leanh::LeanObject,
    mut v_c_u2081_2160_: *mut leanh::LeanObject,
    mut v_c_u2082_2161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_2162_: u8 = 0;
    let mut v_res_2163_: u8 = 0;
    let mut v_r_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2162_ = (leanh::lean_unbox(v_pu_2159_) as u8);
    v_res_2163_ =
        l_Lean_Compiler_LCNF_Code_alphaEqv(v_pu_boxed_2162_, v_c_u2081_2160_, v_c_u2082_2161_);
    v_r_2164_ = leanh::lean_box((v_res_2163_) as usize);
    return v_r_2164_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_AlphaEqv(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
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
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_AlphaEqv(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_AlphaEqv(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
}