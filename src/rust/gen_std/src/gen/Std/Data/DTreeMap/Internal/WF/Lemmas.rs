// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.WF.Lemmas
// Imports: Std.Data.DTreeMap.Internal.Model Std.Data.Internal.List.Associative Init.Data.List.Impl Init.Data.Nat.Linear Init.Data.Option.List Init.Data.Subtype.Basic
use crate::r#gen::Init::Data::List::Impl::{
    initialize_Init_Data_List_Impl, runtime_initialize_Init_Data_List_Impl,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Option::List::{
    initialize_Init_Data_Option_List, runtime_initialize_Init_Data_Option_List,
};
use crate::r#gen::Init::Data::Subtype::Basic::{
    initialize_Init_Data_Subtype_Basic, runtime_initialize_Init_Data_Subtype_Basic,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Model::{
    initialize_Std_Data_DTreeMap_Internal_Model,
    runtime_initialize_Std_Data_DTreeMap_Internal_Model,
};
use crate::r#gen::Std::Data::Internal::List::Associative::{
    initialize_Std_Data_Internal_List_Associative,
    runtime_initialize_Std_Data_Internal_List_Associative,
};
pub unsafe fn l_Std_DTreeMap_Internal_Impl_instCoeTypeForall__1(
    mut v_00_u03b1_996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_997_ = leanh::lean_box(0);
    return v___x_997_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter___redArg(
    mut v_l_998_: *mut leanh::LeanObject,
    mut v_h__1_999_: *mut leanh::LeanObject,
    mut v_h__2_1000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_998_) == 0 {
        let mut v_size_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_999_);
        v_size_1001_ = leanh::lean_ctor_get(v_l_998_, 0);
        leanh::lean_inc(v_size_1001_);
        v_k_1002_ = leanh::lean_ctor_get(v_l_998_, 1);
        leanh::lean_inc(v_k_1002_);
        v_v_1003_ = leanh::lean_ctor_get(v_l_998_, 2);
        leanh::lean_inc(v_v_1003_);
        v_l_1004_ = leanh::lean_ctor_get(v_l_998_, 3);
        leanh::lean_inc(v_l_1004_);
        v_r_1005_ = leanh::lean_ctor_get(v_l_998_, 4);
        leanh::lean_inc(v_r_1005_);
        leanh::lean_dec_ref_known(v_l_998_, 5);
        v___x_1006_ = leanh::lean_apply_5(
            v_h__2_1000_,
            v_size_1001_,
            v_k_1002_,
            v_v_1003_,
            v_l_1004_,
            v_r_1005_,
        );
        return v___x_1006_;
    } else {
        let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1000_);
        v___x_1007_ = leanh::lean_box(0);
        v___x_1008_ = leanh::lean_apply_1(v_h__1_999_, v___x_1007_);
        return v___x_1008_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter(
    mut v_00_u03b1_1009_: *mut leanh::LeanObject,
    mut v_00_u03b2_1010_: *mut leanh::LeanObject,
    mut v_motive_1011_: *mut leanh::LeanObject,
    mut v_l_1012_: *mut leanh::LeanObject,
    mut v_h__1_1013_: *mut leanh::LeanObject,
    mut v_h__2_1014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_1012_) == 0 {
        let mut v_size_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1013_);
        v_size_1015_ = leanh::lean_ctor_get(v_l_1012_, 0);
        leanh::lean_inc(v_size_1015_);
        v_k_1016_ = leanh::lean_ctor_get(v_l_1012_, 1);
        leanh::lean_inc(v_k_1016_);
        v_v_1017_ = leanh::lean_ctor_get(v_l_1012_, 2);
        leanh::lean_inc(v_v_1017_);
        v_l_1018_ = leanh::lean_ctor_get(v_l_1012_, 3);
        leanh::lean_inc(v_l_1018_);
        v_r_1019_ = leanh::lean_ctor_get(v_l_1012_, 4);
        leanh::lean_inc(v_r_1019_);
        leanh::lean_dec_ref_known(v_l_1012_, 5);
        v___x_1020_ = leanh::lean_apply_5(
            v_h__2_1014_,
            v_size_1015_,
            v_k_1016_,
            v_v_1017_,
            v_l_1018_,
            v_r_1019_,
        );
        return v___x_1020_;
    } else {
        let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1014_);
        v___x_1021_ = leanh::lean_box(0);
        v___x_1022_ = leanh::lean_apply_1(v_h__1_1013_, v___x_1021_);
        return v___x_1022_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___redArg(
    mut v_r_1023_: *mut leanh::LeanObject,
    mut v_h__1_1024_: *mut leanh::LeanObject,
    mut v_h__2_1025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_1023_) == 0 {
        let mut v_size_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1024_);
        v_size_1026_ = leanh::lean_ctor_get(v_r_1023_, 0);
        leanh::lean_inc(v_size_1026_);
        v_k_1027_ = leanh::lean_ctor_get(v_r_1023_, 1);
        leanh::lean_inc(v_k_1027_);
        v_v_1028_ = leanh::lean_ctor_get(v_r_1023_, 2);
        leanh::lean_inc(v_v_1028_);
        v_l_1029_ = leanh::lean_ctor_get(v_r_1023_, 3);
        leanh::lean_inc(v_l_1029_);
        v_r_1030_ = leanh::lean_ctor_get(v_r_1023_, 4);
        leanh::lean_inc(v_r_1030_);
        leanh::lean_dec_ref_known(v_r_1023_, 5);
        v___x_1031_ = leanh::lean_apply_6(
            v_h__2_1025_,
            v_size_1026_,
            v_k_1027_,
            v_v_1028_,
            v_l_1029_,
            v_r_1030_,
            leanh::lean_box(0),
        );
        return v___x_1031_;
    } else {
        let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1025_);
        v___x_1032_ = leanh::lean_apply_1(v_h__1_1024_, leanh::lean_box(0));
        return v___x_1032_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(
    mut v_00_u03b1_1033_: *mut leanh::LeanObject,
    mut v_00_u03b2_1034_: *mut leanh::LeanObject,
    mut v_l_1035_: *mut leanh::LeanObject,
    mut v_motive_1036_: *mut leanh::LeanObject,
    mut v_r_1037_: *mut leanh::LeanObject,
    mut v_h_1038_: *mut leanh::LeanObject,
    mut v_h__1_1039_: *mut leanh::LeanObject,
    mut v_h__2_1040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_1037_) == 0 {
        let mut v_size_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1039_);
        v_size_1041_ = leanh::lean_ctor_get(v_r_1037_, 0);
        leanh::lean_inc(v_size_1041_);
        v_k_1042_ = leanh::lean_ctor_get(v_r_1037_, 1);
        leanh::lean_inc(v_k_1042_);
        v_v_1043_ = leanh::lean_ctor_get(v_r_1037_, 2);
        leanh::lean_inc(v_v_1043_);
        v_l_1044_ = leanh::lean_ctor_get(v_r_1037_, 3);
        leanh::lean_inc(v_l_1044_);
        v_r_1045_ = leanh::lean_ctor_get(v_r_1037_, 4);
        leanh::lean_inc(v_r_1045_);
        leanh::lean_dec_ref_known(v_r_1037_, 5);
        v___x_1046_ = leanh::lean_apply_6(
            v_h__2_1040_,
            v_size_1041_,
            v_k_1042_,
            v_v_1043_,
            v_l_1044_,
            v_r_1045_,
            leanh::lean_box(0),
        );
        return v___x_1046_;
    } else {
        let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1040_);
        v___x_1047_ = leanh::lean_apply_1(v_h__1_1039_, leanh::lean_box(0));
        return v___x_1047_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___boxed(
    mut v_00_u03b1_1048_: *mut leanh::LeanObject,
    mut v_00_u03b2_1049_: *mut leanh::LeanObject,
    mut v_l_1050_: *mut leanh::LeanObject,
    mut v_motive_1051_: *mut leanh::LeanObject,
    mut v_r_1052_: *mut leanh::LeanObject,
    mut v_h_1053_: *mut leanh::LeanObject,
    mut v_h__1_1054_: *mut leanh::LeanObject,
    mut v_h__2_1055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1056_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(v_00_u03b1_1048_, v_00_u03b2_1049_, v_l_1050_, v_motive_1051_, v_r_1052_, v_h_1053_, v_h__1_1054_, v_h__2_1055_);
    leanh::lean_dec(v_l_1050_);
    return v_res_1056_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___redArg(
    mut v_l_1057_: *mut leanh::LeanObject,
    mut v_h__1_1058_: *mut leanh::LeanObject,
    mut v_h__2_1059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_1057_) == 0 {
        let mut v_size_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1058_);
        v_size_1060_ = leanh::lean_ctor_get(v_l_1057_, 0);
        leanh::lean_inc(v_size_1060_);
        v_k_1061_ = leanh::lean_ctor_get(v_l_1057_, 1);
        leanh::lean_inc(v_k_1061_);
        v_v_1062_ = leanh::lean_ctor_get(v_l_1057_, 2);
        leanh::lean_inc(v_v_1062_);
        v_l_1063_ = leanh::lean_ctor_get(v_l_1057_, 3);
        leanh::lean_inc(v_l_1063_);
        v_r_1064_ = leanh::lean_ctor_get(v_l_1057_, 4);
        leanh::lean_inc(v_r_1064_);
        leanh::lean_dec_ref_known(v_l_1057_, 5);
        v___x_1065_ = leanh::lean_apply_7(
            v_h__2_1059_,
            v_size_1060_,
            v_k_1061_,
            v_v_1062_,
            v_l_1063_,
            v_r_1064_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1065_;
    } else {
        let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1059_);
        v___x_1066_ = leanh::lean_apply_2(
            v_h__1_1058_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1066_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(
    mut v_00_u03b1_1067_: *mut leanh::LeanObject,
    mut v_00_u03b2_1068_: *mut leanh::LeanObject,
    mut v_r_1069_: *mut leanh::LeanObject,
    mut v_motive_1070_: *mut leanh::LeanObject,
    mut v_l_1071_: *mut leanh::LeanObject,
    mut v_h_1072_: *mut leanh::LeanObject,
    mut v_h_1073_: *mut leanh::LeanObject,
    mut v_h__1_1074_: *mut leanh::LeanObject,
    mut v_h__2_1075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_1071_) == 0 {
        let mut v_size_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1074_);
        v_size_1076_ = leanh::lean_ctor_get(v_l_1071_, 0);
        leanh::lean_inc(v_size_1076_);
        v_k_1077_ = leanh::lean_ctor_get(v_l_1071_, 1);
        leanh::lean_inc(v_k_1077_);
        v_v_1078_ = leanh::lean_ctor_get(v_l_1071_, 2);
        leanh::lean_inc(v_v_1078_);
        v_l_1079_ = leanh::lean_ctor_get(v_l_1071_, 3);
        leanh::lean_inc(v_l_1079_);
        v_r_1080_ = leanh::lean_ctor_get(v_l_1071_, 4);
        leanh::lean_inc(v_r_1080_);
        leanh::lean_dec_ref_known(v_l_1071_, 5);
        v___x_1081_ = leanh::lean_apply_7(
            v_h__2_1075_,
            v_size_1076_,
            v_k_1077_,
            v_v_1078_,
            v_l_1079_,
            v_r_1080_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1081_;
    } else {
        let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1075_);
        v___x_1082_ = leanh::lean_apply_2(
            v_h__1_1074_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1082_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___boxed(
    mut v_00_u03b1_1083_: *mut leanh::LeanObject,
    mut v_00_u03b2_1084_: *mut leanh::LeanObject,
    mut v_r_1085_: *mut leanh::LeanObject,
    mut v_motive_1086_: *mut leanh::LeanObject,
    mut v_l_1087_: *mut leanh::LeanObject,
    mut v_h_1088_: *mut leanh::LeanObject,
    mut v_h_1089_: *mut leanh::LeanObject,
    mut v_h__1_1090_: *mut leanh::LeanObject,
    mut v_h__2_1091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1092_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(v_00_u03b1_1083_, v_00_u03b2_1084_, v_r_1085_, v_motive_1086_, v_l_1087_, v_h_1088_, v_h_1089_, v_h__1_1090_, v_h__2_1091_);
    leanh::lean_dec(v_r_1085_);
    return v_res_1092_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(
    mut v_r_1093_: *mut leanh::LeanObject,
    mut v_h__1_1094_: *mut leanh::LeanObject,
    mut v_h__2_1095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_1093_) == 0 {
        let mut v_size_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1094_);
        v_size_1096_ = leanh::lean_ctor_get(v_r_1093_, 0);
        leanh::lean_inc(v_size_1096_);
        v_k_1097_ = leanh::lean_ctor_get(v_r_1093_, 1);
        leanh::lean_inc(v_k_1097_);
        v_v_1098_ = leanh::lean_ctor_get(v_r_1093_, 2);
        leanh::lean_inc(v_v_1098_);
        v_l_1099_ = leanh::lean_ctor_get(v_r_1093_, 3);
        leanh::lean_inc(v_l_1099_);
        v_r_1100_ = leanh::lean_ctor_get(v_r_1093_, 4);
        leanh::lean_inc(v_r_1100_);
        leanh::lean_dec_ref_known(v_r_1093_, 5);
        v___x_1101_ = leanh::lean_apply_7(
            v_h__2_1095_,
            v_size_1096_,
            v_k_1097_,
            v_v_1098_,
            v_l_1099_,
            v_r_1100_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1101_;
    } else {
        let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1095_);
        v___x_1102_ = leanh::lean_apply_2(
            v_h__1_1094_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1102_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(
    mut v_00_u03b1_1103_: *mut leanh::LeanObject,
    mut v_00_u03b2_1104_: *mut leanh::LeanObject,
    mut v_motive_1105_: *mut leanh::LeanObject,
    mut v_r_1106_: *mut leanh::LeanObject,
    mut v_hr_1107_: *mut leanh::LeanObject,
    mut v_h__1_1108_: *mut leanh::LeanObject,
    mut v_h__2_1109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_1106_) == 0 {
        let mut v_size_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1108_);
        v_size_1110_ = leanh::lean_ctor_get(v_r_1106_, 0);
        leanh::lean_inc(v_size_1110_);
        v_k_1111_ = leanh::lean_ctor_get(v_r_1106_, 1);
        leanh::lean_inc(v_k_1111_);
        v_v_1112_ = leanh::lean_ctor_get(v_r_1106_, 2);
        leanh::lean_inc(v_v_1112_);
        v_l_1113_ = leanh::lean_ctor_get(v_r_1106_, 3);
        leanh::lean_inc(v_l_1113_);
        v_r_1114_ = leanh::lean_ctor_get(v_r_1106_, 4);
        leanh::lean_inc(v_r_1114_);
        leanh::lean_dec_ref_known(v_r_1106_, 5);
        v___x_1115_ = leanh::lean_apply_7(
            v_h__2_1109_,
            v_size_1110_,
            v_k_1111_,
            v_v_1112_,
            v_l_1113_,
            v_r_1114_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1115_;
    } else {
        let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1109_);
        v___x_1116_ = leanh::lean_apply_2(
            v_h__1_1108_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1116_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___redArg(
    mut v_x_1117_: *mut leanh::LeanObject,
    mut v_h__1_1118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1119_ = leanh::lean_apply_3(
        v_h__1_1118_,
        v_x_1117_,
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1119_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(
    mut v_00_u03b1_1120_: *mut leanh::LeanObject,
    mut v_00_u03b2_1121_: *mut leanh::LeanObject,
    mut v_l_1122_: *mut leanh::LeanObject,
    mut v_l_x27_x27_1123_: *mut leanh::LeanObject,
    mut v_motive_1124_: *mut leanh::LeanObject,
    mut v_x_1125_: *mut leanh::LeanObject,
    mut v_h__1_1126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1127_ = leanh::lean_apply_3(
        v_h__1_1126_,
        v_x_1125_,
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1127_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___boxed(
    mut v_00_u03b1_1128_: *mut leanh::LeanObject,
    mut v_00_u03b2_1129_: *mut leanh::LeanObject,
    mut v_l_1130_: *mut leanh::LeanObject,
    mut v_l_x27_x27_1131_: *mut leanh::LeanObject,
    mut v_motive_1132_: *mut leanh::LeanObject,
    mut v_x_1133_: *mut leanh::LeanObject,
    mut v_h__1_1134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1135_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(v_00_u03b1_1128_, v_00_u03b2_1129_, v_l_1130_, v_l_x27_x27_1131_, v_motive_1132_, v_x_1133_, v_h__1_1134_);
    leanh::lean_dec(v_l_x27_x27_1131_);
    leanh::lean_dec(v_l_1130_);
    return v_res_1135_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___redArg(
    mut v_x_1136_: *mut leanh::LeanObject,
    mut v_h__1_1137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1138_ = leanh::lean_apply_3(
        v_h__1_1137_,
        v_x_1136_,
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1138_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(
    mut v_00_u03b1_1139_: *mut leanh::LeanObject,
    mut v_00_u03b2_1140_: *mut leanh::LeanObject,
    mut v_r_1141_: *mut leanh::LeanObject,
    mut v_r_x27_1142_: *mut leanh::LeanObject,
    mut v_motive_1143_: *mut leanh::LeanObject,
    mut v_x_1144_: *mut leanh::LeanObject,
    mut v_h__1_1145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1146_ = leanh::lean_apply_3(
        v_h__1_1145_,
        v_x_1144_,
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1146_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___boxed(
    mut v_00_u03b1_1147_: *mut leanh::LeanObject,
    mut v_00_u03b2_1148_: *mut leanh::LeanObject,
    mut v_r_1149_: *mut leanh::LeanObject,
    mut v_r_x27_1150_: *mut leanh::LeanObject,
    mut v_motive_1151_: *mut leanh::LeanObject,
    mut v_x_1152_: *mut leanh::LeanObject,
    mut v_h__1_1153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(v_00_u03b1_1147_, v_00_u03b2_1148_, v_r_1149_, v_r_x27_1150_, v_motive_1151_, v_x_1152_, v_h__1_1153_);
    leanh::lean_dec(v_r_x27_1150_);
    leanh::lean_dec(v_r_1149_);
    return v_res_1154_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(
    mut v_t_1155_: *mut leanh::LeanObject,
    mut v_h__1_1156_: *mut leanh::LeanObject,
    mut v_h__2_1157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1155_) == 0 {
        let mut v_size_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1156_);
        v_size_1158_ = leanh::lean_ctor_get(v_t_1155_, 0);
        leanh::lean_inc(v_size_1158_);
        v_k_1159_ = leanh::lean_ctor_get(v_t_1155_, 1);
        leanh::lean_inc(v_k_1159_);
        v_v_1160_ = leanh::lean_ctor_get(v_t_1155_, 2);
        leanh::lean_inc(v_v_1160_);
        v_l_1161_ = leanh::lean_ctor_get(v_t_1155_, 3);
        leanh::lean_inc(v_l_1161_);
        v_r_1162_ = leanh::lean_ctor_get(v_t_1155_, 4);
        leanh::lean_inc(v_r_1162_);
        leanh::lean_dec_ref_known(v_t_1155_, 5);
        v___x_1163_ = leanh::lean_apply_6(
            v_h__2_1157_,
            v_size_1158_,
            v_k_1159_,
            v_v_1160_,
            v_l_1161_,
            v_r_1162_,
            leanh::lean_box(0),
        );
        return v___x_1163_;
    } else {
        let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1157_);
        v___x_1164_ = leanh::lean_apply_1(v_h__1_1156_, leanh::lean_box(0));
        return v___x_1164_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(
    mut v_00_u03b1_1165_: *mut leanh::LeanObject,
    mut v_00_u03b2_1166_: *mut leanh::LeanObject,
    mut v_motive_1167_: *mut leanh::LeanObject,
    mut v_t_1168_: *mut leanh::LeanObject,
    mut v_hr_1169_: *mut leanh::LeanObject,
    mut v_h__1_1170_: *mut leanh::LeanObject,
    mut v_h__2_1171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1168_) == 0 {
        let mut v_size_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1170_);
        v_size_1172_ = leanh::lean_ctor_get(v_t_1168_, 0);
        leanh::lean_inc(v_size_1172_);
        v_k_1173_ = leanh::lean_ctor_get(v_t_1168_, 1);
        leanh::lean_inc(v_k_1173_);
        v_v_1174_ = leanh::lean_ctor_get(v_t_1168_, 2);
        leanh::lean_inc(v_v_1174_);
        v_l_1175_ = leanh::lean_ctor_get(v_t_1168_, 3);
        leanh::lean_inc(v_l_1175_);
        v_r_1176_ = leanh::lean_ctor_get(v_t_1168_, 4);
        leanh::lean_inc(v_r_1176_);
        leanh::lean_dec_ref_known(v_t_1168_, 5);
        v___x_1177_ = leanh::lean_apply_6(
            v_h__2_1171_,
            v_size_1172_,
            v_k_1173_,
            v_v_1174_,
            v_l_1175_,
            v_r_1176_,
            leanh::lean_box(0),
        );
        return v___x_1177_;
    } else {
        let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1171_);
        v___x_1178_ = leanh::lean_apply_1(v_h__1_1170_, leanh::lean_box(0));
        return v___x_1178_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___redArg(
    mut v_x_1179_: *mut leanh::LeanObject,
    mut v_h__1_1180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1181_ = leanh::lean_apply_3(
        v_h__1_1180_,
        v_x_1179_,
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1181_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(
    mut v_00_u03b1_1182_: *mut leanh::LeanObject,
    mut v_00_u03b2_1183_: *mut leanh::LeanObject,
    mut v_szl_1184_: *mut leanh::LeanObject,
    mut v_k_x27_1185_: *mut leanh::LeanObject,
    mut v_v_x27_1186_: *mut leanh::LeanObject,
    mut v_l_x27_1187_: *mut leanh::LeanObject,
    mut v_r_x27_1188_: *mut leanh::LeanObject,
    mut v_l_x27_x27_1189_: *mut leanh::LeanObject,
    mut v_motive_1190_: *mut leanh::LeanObject,
    mut v_x_1191_: *mut leanh::LeanObject,
    mut v_h__1_1192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1193_ = leanh::lean_apply_3(
        v_h__1_1192_,
        v_x_1191_,
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1193_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___boxed(
    mut v_00_u03b1_1194_: *mut leanh::LeanObject,
    mut v_00_u03b2_1195_: *mut leanh::LeanObject,
    mut v_szl_1196_: *mut leanh::LeanObject,
    mut v_k_x27_1197_: *mut leanh::LeanObject,
    mut v_v_x27_1198_: *mut leanh::LeanObject,
    mut v_l_x27_1199_: *mut leanh::LeanObject,
    mut v_r_x27_1200_: *mut leanh::LeanObject,
    mut v_l_x27_x27_1201_: *mut leanh::LeanObject,
    mut v_motive_1202_: *mut leanh::LeanObject,
    mut v_x_1203_: *mut leanh::LeanObject,
    mut v_h__1_1204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1205_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(v_00_u03b1_1194_, v_00_u03b2_1195_, v_szl_1196_, v_k_x27_1197_, v_v_x27_1198_, v_l_x27_1199_, v_r_x27_1200_, v_l_x27_x27_1201_, v_motive_1202_, v_x_1203_, v_h__1_1204_);
    leanh::lean_dec(v_l_x27_x27_1201_);
    leanh::lean_dec(v_r_x27_1200_);
    leanh::lean_dec(v_l_x27_1199_);
    leanh::lean_dec(v_v_x27_1198_);
    leanh::lean_dec(v_k_x27_1197_);
    leanh::lean_dec(v_szl_1196_);
    return v_res_1205_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___redArg(
    mut v_x_1206_: *mut leanh::LeanObject,
    mut v_h__1_1207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1208_ = leanh::lean_apply_3(
        v_h__1_1207_,
        v_x_1206_,
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1208_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(
    mut v_00_u03b1_1209_: *mut leanh::LeanObject,
    mut v_00_u03b2_1210_: *mut leanh::LeanObject,
    mut v_r_x27_1211_: *mut leanh::LeanObject,
    mut v_szr_1212_: *mut leanh::LeanObject,
    mut v_k_x27_x27_1213_: *mut leanh::LeanObject,
    mut v_v_x27_x27_1214_: *mut leanh::LeanObject,
    mut v_l_x27_x27_1215_: *mut leanh::LeanObject,
    mut v_r_x27_x27_1216_: *mut leanh::LeanObject,
    mut v_motive_1217_: *mut leanh::LeanObject,
    mut v_x_1218_: *mut leanh::LeanObject,
    mut v_h__1_1219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1220_ = leanh::lean_apply_3(
        v_h__1_1219_,
        v_x_1218_,
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1220_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___boxed(
    mut v_00_u03b1_1221_: *mut leanh::LeanObject,
    mut v_00_u03b2_1222_: *mut leanh::LeanObject,
    mut v_r_x27_1223_: *mut leanh::LeanObject,
    mut v_szr_1224_: *mut leanh::LeanObject,
    mut v_k_x27_x27_1225_: *mut leanh::LeanObject,
    mut v_v_x27_x27_1226_: *mut leanh::LeanObject,
    mut v_l_x27_x27_1227_: *mut leanh::LeanObject,
    mut v_r_x27_x27_1228_: *mut leanh::LeanObject,
    mut v_motive_1229_: *mut leanh::LeanObject,
    mut v_x_1230_: *mut leanh::LeanObject,
    mut v_h__1_1231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1232_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(v_00_u03b1_1221_, v_00_u03b2_1222_, v_r_x27_1223_, v_szr_1224_, v_k_x27_x27_1225_, v_v_x27_x27_1226_, v_l_x27_x27_1227_, v_r_x27_x27_1228_, v_motive_1229_, v_x_1230_, v_h__1_1231_);
    leanh::lean_dec(v_r_x27_x27_1228_);
    leanh::lean_dec(v_l_x27_x27_1227_);
    leanh::lean_dec(v_v_x27_x27_1226_);
    leanh::lean_dec(v_k_x27_x27_1225_);
    leanh::lean_dec(v_szr_1224_);
    leanh::lean_dec(v_r_x27_1223_);
    return v_res_1232_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(
    mut v_l_1233_: *mut leanh::LeanObject,
    mut v_h__1_1234_: *mut leanh::LeanObject,
    mut v_h__2_1235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_1233_) == 0 {
        let mut v_size_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1234_);
        v_size_1236_ = leanh::lean_ctor_get(v_l_1233_, 0);
        leanh::lean_inc(v_size_1236_);
        v_k_1237_ = leanh::lean_ctor_get(v_l_1233_, 1);
        leanh::lean_inc(v_k_1237_);
        v_v_1238_ = leanh::lean_ctor_get(v_l_1233_, 2);
        leanh::lean_inc(v_v_1238_);
        v_l_1239_ = leanh::lean_ctor_get(v_l_1233_, 3);
        leanh::lean_inc(v_l_1239_);
        v_r_1240_ = leanh::lean_ctor_get(v_l_1233_, 4);
        leanh::lean_inc(v_r_1240_);
        leanh::lean_dec_ref_known(v_l_1233_, 5);
        v___x_1241_ = leanh::lean_apply_6(
            v_h__2_1235_,
            v_size_1236_,
            v_k_1237_,
            v_v_1238_,
            v_l_1239_,
            v_r_1240_,
            leanh::lean_box(0),
        );
        return v___x_1241_;
    } else {
        let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1235_);
        v___x_1242_ = leanh::lean_apply_1(v_h__1_1234_, leanh::lean_box(0));
        return v___x_1242_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(
    mut v_00_u03b1_1243_: *mut leanh::LeanObject,
    mut v_00_u03b2_1244_: *mut leanh::LeanObject,
    mut v_motive_1245_: *mut leanh::LeanObject,
    mut v_l_1246_: *mut leanh::LeanObject,
    mut v_hl_1247_: *mut leanh::LeanObject,
    mut v_h__1_1248_: *mut leanh::LeanObject,
    mut v_h__2_1249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_1246_) == 0 {
        let mut v_size_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1248_);
        v_size_1250_ = leanh::lean_ctor_get(v_l_1246_, 0);
        leanh::lean_inc(v_size_1250_);
        v_k_1251_ = leanh::lean_ctor_get(v_l_1246_, 1);
        leanh::lean_inc(v_k_1251_);
        v_v_1252_ = leanh::lean_ctor_get(v_l_1246_, 2);
        leanh::lean_inc(v_v_1252_);
        v_l_1253_ = leanh::lean_ctor_get(v_l_1246_, 3);
        leanh::lean_inc(v_l_1253_);
        v_r_1254_ = leanh::lean_ctor_get(v_l_1246_, 4);
        leanh::lean_inc(v_r_1254_);
        leanh::lean_dec_ref_known(v_l_1246_, 5);
        v___x_1255_ = leanh::lean_apply_6(
            v_h__2_1249_,
            v_size_1250_,
            v_k_1251_,
            v_v_1252_,
            v_l_1253_,
            v_r_1254_,
            leanh::lean_box(0),
        );
        return v___x_1255_;
    } else {
        let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1249_);
        v___x_1256_ = leanh::lean_apply_1(v_h__1_1248_, leanh::lean_box(0));
        return v___x_1256_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(
    mut v_x_1257_: *mut leanh::LeanObject,
    mut v_h__1_1258_: *mut leanh::LeanObject,
    mut v_h__2_1259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1257_) == 0 {
        let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1259_);
        v___x_1260_ = leanh::lean_box(0);
        v___x_1261_ = leanh::lean_apply_1(v_h__1_1258_, v___x_1260_);
        return v___x_1261_;
    } else {
        let mut v_val_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1258_);
        v_val_1262_ = leanh::lean_ctor_get(v_x_1257_, 0);
        leanh::lean_inc(v_val_1262_);
        leanh::lean_dec_ref_known(v_x_1257_, 1);
        v_fst_1263_ = leanh::lean_ctor_get(v_val_1262_, 0);
        leanh::lean_inc(v_fst_1263_);
        v_snd_1264_ = leanh::lean_ctor_get(v_val_1262_, 1);
        leanh::lean_inc(v_snd_1264_);
        leanh::lean_dec(v_val_1262_);
        v___x_1265_ = leanh::lean_apply_2(v_h__2_1259_, v_fst_1263_, v_snd_1264_);
        return v___x_1265_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(
    mut v_00_u03b1_1266_: *mut leanh::LeanObject,
    mut v_00_u03b2_1267_: *mut leanh::LeanObject,
    mut v_motive_1268_: *mut leanh::LeanObject,
    mut v_x_1269_: *mut leanh::LeanObject,
    mut v_h__1_1270_: *mut leanh::LeanObject,
    mut v_h__2_1271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1269_) == 0 {
        let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1271_);
        v___x_1272_ = leanh::lean_box(0);
        v___x_1273_ = leanh::lean_apply_1(v_h__1_1270_, v___x_1272_);
        return v___x_1273_;
    } else {
        let mut v_val_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1270_);
        v_val_1274_ = leanh::lean_ctor_get(v_x_1269_, 0);
        leanh::lean_inc(v_val_1274_);
        leanh::lean_dec_ref_known(v_x_1269_, 1);
        v_fst_1275_ = leanh::lean_ctor_get(v_val_1274_, 0);
        leanh::lean_inc(v_fst_1275_);
        v_snd_1276_ = leanh::lean_ctor_get(v_val_1274_, 1);
        leanh::lean_inc(v_snd_1276_);
        leanh::lean_dec(v_val_1274_);
        v___x_1277_ = leanh::lean_apply_2(v_h__2_1271_, v_fst_1275_, v_snd_1276_);
        return v___x_1277_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(
    mut v_x_1278_: u8,
    mut v_h__1_1279_: *mut leanh::LeanObject,
    mut v_h__2_1280_: *mut leanh::LeanObject,
    mut v_h__3_1281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_x_1278_ {
        0 => {
            let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1281_);
            leanh::lean_dec(v_h__2_1280_);
            v___x_1282_ = leanh::lean_apply_1(v_h__1_1279_, leanh::lean_box(0));
            return v___x_1282_;
        }
        1 => {
            let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1281_);
            leanh::lean_dec(v_h__1_1279_);
            v___x_1283_ = leanh::lean_apply_1(v_h__2_1280_, leanh::lean_box(0));
            return v___x_1283_;
        }
        _ => {
            let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1280_);
            leanh::lean_dec(v_h__1_1279_);
            v___x_1284_ = leanh::lean_apply_1(v_h__3_1281_, leanh::lean_box(0));
            return v___x_1284_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(
    mut v_x_1285_: *mut leanh::LeanObject,
    mut v_h__1_1286_: *mut leanh::LeanObject,
    mut v_h__2_1287_: *mut leanh::LeanObject,
    mut v_h__3_1288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_33__boxed_1289_: u8 = 0;
    let mut v_res_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_33__boxed_1289_ = (leanh::lean_unbox(v_x_1285_) as u8);
    v_res_1290_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(v_x_33__boxed_1289_, v_h__1_1286_, v_h__2_1287_, v_h__3_1288_);
    return v_res_1290_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(
    mut v_motive_1291_: *mut leanh::LeanObject,
    mut v_x_1292_: u8,
    mut v_h__1_1293_: *mut leanh::LeanObject,
    mut v_h__2_1294_: *mut leanh::LeanObject,
    mut v_h__3_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_x_1292_ {
        0 => {
            let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1295_);
            leanh::lean_dec(v_h__2_1294_);
            v___x_1296_ = leanh::lean_apply_1(v_h__1_1293_, leanh::lean_box(0));
            return v___x_1296_;
        }
        1 => {
            let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1295_);
            leanh::lean_dec(v_h__1_1293_);
            v___x_1297_ = leanh::lean_apply_1(v_h__2_1294_, leanh::lean_box(0));
            return v___x_1297_;
        }
        _ => {
            let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1294_);
            leanh::lean_dec(v_h__1_1293_);
            v___x_1298_ = leanh::lean_apply_1(v_h__3_1295_, leanh::lean_box(0));
            return v___x_1298_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(
    mut v_motive_1299_: *mut leanh::LeanObject,
    mut v_x_1300_: *mut leanh::LeanObject,
    mut v_h__1_1301_: *mut leanh::LeanObject,
    mut v_h__2_1302_: *mut leanh::LeanObject,
    mut v_h__3_1303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_42__boxed_1304_: u8 = 0;
    let mut v_res_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_42__boxed_1304_ = (leanh::lean_unbox(v_x_1300_) as u8);
    v_res_1305_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(v_motive_1299_, v_x_42__boxed_1304_, v_h__1_1301_, v_h__2_1302_, v_h__3_1303_);
    return v_res_1305_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___redArg(
    mut v_x_1306_: *mut leanh::LeanObject,
    mut v_h__1_1307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1308_ = leanh::lean_apply_4(
        v_h__1_1307_,
        v_x_1306_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1308_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(
    mut v_00_u03b1_1309_: *mut leanh::LeanObject,
    mut v_00_u03b2_1310_: *mut leanh::LeanObject,
    mut v_l_1311_: *mut leanh::LeanObject,
    mut v_motive_1312_: *mut leanh::LeanObject,
    mut v_x_1313_: *mut leanh::LeanObject,
    mut v_h__1_1314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1315_ = leanh::lean_apply_4(
        v_h__1_1314_,
        v_x_1313_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1315_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___boxed(
    mut v_00_u03b1_1316_: *mut leanh::LeanObject,
    mut v_00_u03b2_1317_: *mut leanh::LeanObject,
    mut v_l_1318_: *mut leanh::LeanObject,
    mut v_motive_1319_: *mut leanh::LeanObject,
    mut v_x_1320_: *mut leanh::LeanObject,
    mut v_h__1_1321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1322_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(v_00_u03b1_1316_, v_00_u03b2_1317_, v_l_1318_, v_motive_1319_, v_x_1320_, v_h__1_1321_);
    leanh::lean_dec(v_l_1318_);
    return v_res_1322_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(
    mut v_x_1323_: u8,
    mut v_h__1_1324_: *mut leanh::LeanObject,
    mut v_h__2_1325_: *mut leanh::LeanObject,
    mut v_h__3_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_x_1323_ {
        0 => {
            let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1326_);
            leanh::lean_dec(v_h__2_1325_);
            v___x_1327_ = leanh::lean_box(0);
            v___x_1328_ = leanh::lean_apply_1(v_h__1_1324_, v___x_1327_);
            return v___x_1328_;
        }
        1 => {
            let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1325_);
            leanh::lean_dec(v_h__1_1324_);
            v___x_1329_ = leanh::lean_box(0);
            v___x_1330_ = leanh::lean_apply_1(v_h__3_1326_, v___x_1329_);
            return v___x_1330_;
        }
        _ => {
            let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1326_);
            leanh::lean_dec(v_h__1_1324_);
            v___x_1331_ = leanh::lean_box(0);
            v___x_1332_ = leanh::lean_apply_1(v_h__2_1325_, v___x_1331_);
            return v___x_1332_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg___boxed(
    mut v_x_1333_: *mut leanh::LeanObject,
    mut v_h__1_1334_: *mut leanh::LeanObject,
    mut v_h__2_1335_: *mut leanh::LeanObject,
    mut v_h__3_1336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_36__boxed_1337_: u8 = 0;
    let mut v_res_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_1337_ = (leanh::lean_unbox(v_x_1333_) as u8);
    v_res_1338_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_36__boxed_1337_, v_h__1_1334_, v_h__2_1335_, v_h__3_1336_);
    return v_res_1338_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(
    mut v_motive_1339_: *mut leanh::LeanObject,
    mut v_x_1340_: u8,
    mut v_h__1_1341_: *mut leanh::LeanObject,
    mut v_h__2_1342_: *mut leanh::LeanObject,
    mut v_h__3_1343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_x_1340_ {
        0 => {
            let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1343_);
            leanh::lean_dec(v_h__2_1342_);
            v___x_1344_ = leanh::lean_box(0);
            v___x_1345_ = leanh::lean_apply_1(v_h__1_1341_, v___x_1344_);
            return v___x_1345_;
        }
        1 => {
            let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1342_);
            leanh::lean_dec(v_h__1_1341_);
            v___x_1346_ = leanh::lean_box(0);
            v___x_1347_ = leanh::lean_apply_1(v_h__3_1343_, v___x_1346_);
            return v___x_1347_;
        }
        _ => {
            let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1343_);
            leanh::lean_dec(v_h__1_1341_);
            v___x_1348_ = leanh::lean_box(0);
            v___x_1349_ = leanh::lean_apply_1(v_h__2_1342_, v___x_1348_);
            return v___x_1349_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___boxed(
    mut v_motive_1350_: *mut leanh::LeanObject,
    mut v_x_1351_: *mut leanh::LeanObject,
    mut v_h__1_1352_: *mut leanh::LeanObject,
    mut v_h__2_1353_: *mut leanh::LeanObject,
    mut v_h__3_1354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_51__boxed_1355_: u8 = 0;
    let mut v_res_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_51__boxed_1355_ = (leanh::lean_unbox(v_x_1351_) as u8);
    v_res_1356_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(v_motive_1350_, v_x_51__boxed_1355_, v_h__1_1352_, v_h__2_1353_, v_h__3_1354_);
    return v_res_1356_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(
    mut v_x_1357_: *mut leanh::LeanObject,
    mut v_h__1_1358_: *mut leanh::LeanObject,
    mut v_h__2_1359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1357_) == 0 {
        let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1359_);
        v___x_1360_ = leanh::lean_apply_1(v_h__1_1358_, leanh::lean_box(0));
        return v___x_1360_;
    } else {
        let mut v_val_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1358_);
        v_val_1361_ = leanh::lean_ctor_get(v_x_1357_, 0);
        leanh::lean_inc(v_val_1361_);
        leanh::lean_dec_ref_known(v_x_1357_, 1);
        v___x_1362_ =
            leanh::lean_apply_2(v_h__2_1359_, v_val_1361_, leanh::lean_box(0));
        return v___x_1362_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(
    mut v_00_u03b1_1363_: *mut leanh::LeanObject,
    mut v_00_u03b2_1364_: *mut leanh::LeanObject,
    mut v_motive_1365_: *mut leanh::LeanObject,
    mut v_x_1366_: *mut leanh::LeanObject,
    mut v_h__1_1367_: *mut leanh::LeanObject,
    mut v_h__2_1368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1366_) == 0 {
        let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1368_);
        v___x_1369_ = leanh::lean_apply_1(v_h__1_1367_, leanh::lean_box(0));
        return v___x_1369_;
    } else {
        let mut v_val_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1367_);
        v_val_1370_ = leanh::lean_ctor_get(v_x_1366_, 0);
        leanh::lean_inc(v_val_1370_);
        leanh::lean_dec_ref_known(v_x_1366_, 1);
        v___x_1371_ =
            leanh::lean_apply_2(v_h__2_1368_, v_val_1370_, leanh::lean_box(0));
        return v___x_1371_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(
    mut v_x_1372_: *mut leanh::LeanObject,
    mut v_h__1_1373_: *mut leanh::LeanObject,
    mut v_h__2_1374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1372_) == 0 {
        let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1374_);
        v___x_1375_ = leanh::lean_box(0);
        v___x_1376_ = leanh::lean_apply_1(v_h__1_1373_, v___x_1375_);
        return v___x_1376_;
    } else {
        let mut v_val_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1373_);
        v_val_1377_ = leanh::lean_ctor_get(v_x_1372_, 0);
        leanh::lean_inc(v_val_1377_);
        leanh::lean_dec_ref_known(v_x_1372_, 1);
        v___x_1378_ = leanh::lean_apply_1(v_h__2_1374_, v_val_1377_);
        return v___x_1378_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(
    mut v_00_u03b1_1379_: *mut leanh::LeanObject,
    mut v_00_u03b2_1380_: *mut leanh::LeanObject,
    mut v_motive_1381_: *mut leanh::LeanObject,
    mut v_x_1382_: *mut leanh::LeanObject,
    mut v_h__1_1383_: *mut leanh::LeanObject,
    mut v_h__2_1384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1382_) == 0 {
        let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1384_);
        v___x_1385_ = leanh::lean_box(0);
        v___x_1386_ = leanh::lean_apply_1(v_h__1_1383_, v___x_1385_);
        return v___x_1386_;
    } else {
        let mut v_val_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1383_);
        v_val_1387_ = leanh::lean_ctor_get(v_x_1382_, 0);
        leanh::lean_inc(v_val_1387_);
        leanh::lean_dec_ref_known(v_x_1382_, 1);
        v___x_1388_ = leanh::lean_apply_1(v_h__2_1384_, v_val_1387_);
        return v___x_1388_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(
    mut v_x_1389_: *mut leanh::LeanObject,
    mut v_h__1_1390_: *mut leanh::LeanObject,
    mut v_h__2_1391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1389_) == 0 {
        let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1391_);
        v___x_1392_ = leanh::lean_box(0);
        v___x_1393_ = leanh::lean_apply_1(v_h__1_1390_, v___x_1392_);
        return v___x_1393_;
    } else {
        let mut v_head_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1390_);
        v_head_1394_ = leanh::lean_ctor_get(v_x_1389_, 0);
        leanh::lean_inc(v_head_1394_);
        v_tail_1395_ = leanh::lean_ctor_get(v_x_1389_, 1);
        leanh::lean_inc(v_tail_1395_);
        leanh::lean_dec_ref_known(v_x_1389_, 2);
        v_fst_1396_ = leanh::lean_ctor_get(v_head_1394_, 0);
        leanh::lean_inc(v_fst_1396_);
        v_snd_1397_ = leanh::lean_ctor_get(v_head_1394_, 1);
        leanh::lean_inc(v_snd_1397_);
        leanh::lean_dec(v_head_1394_);
        v___x_1398_ =
            leanh::lean_apply_3(v_h__2_1391_, v_fst_1396_, v_snd_1397_, v_tail_1395_);
        return v___x_1398_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_getEntry_x3f_match__1_splitter(
    mut v_00_u03b1_1399_: *mut leanh::LeanObject,
    mut v_00_u03b2_1400_: *mut leanh::LeanObject,
    mut v_motive_1401_: *mut leanh::LeanObject,
    mut v_x_1402_: *mut leanh::LeanObject,
    mut v_h__1_1403_: *mut leanh::LeanObject,
    mut v_h__2_1404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1402_) == 0 {
        let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1404_);
        v___x_1405_ = leanh::lean_box(0);
        v___x_1406_ = leanh::lean_apply_1(v_h__1_1403_, v___x_1405_);
        return v___x_1406_;
    } else {
        let mut v_head_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1403_);
        v_head_1407_ = leanh::lean_ctor_get(v_x_1402_, 0);
        leanh::lean_inc(v_head_1407_);
        v_tail_1408_ = leanh::lean_ctor_get(v_x_1402_, 1);
        leanh::lean_inc(v_tail_1408_);
        leanh::lean_dec_ref_known(v_x_1402_, 2);
        v_fst_1409_ = leanh::lean_ctor_get(v_head_1407_, 0);
        leanh::lean_inc(v_fst_1409_);
        v_snd_1410_ = leanh::lean_ctor_get(v_head_1407_, 1);
        leanh::lean_inc(v_snd_1410_);
        leanh::lean_dec(v_head_1407_);
        v___x_1411_ =
            leanh::lean_apply_3(v_h__2_1404_, v_fst_1409_, v_snd_1410_, v_tail_1408_);
        return v___x_1411_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(
    mut v_x_1412_: *mut leanh::LeanObject,
    mut v_h__1_1413_: *mut leanh::LeanObject,
    mut v_h__2_1414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1412_) == 0 {
        let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1414_);
        v___x_1415_ = leanh::lean_box(0);
        v___x_1416_ = leanh::lean_apply_1(v_h__1_1413_, v___x_1415_);
        return v___x_1416_;
    } else {
        let mut v_val_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1413_);
        v_val_1417_ = leanh::lean_ctor_get(v_x_1412_, 0);
        leanh::lean_inc(v_val_1417_);
        leanh::lean_dec_ref_known(v_x_1412_, 1);
        v___x_1418_ = leanh::lean_apply_1(v_h__2_1414_, v_val_1417_);
        return v___x_1418_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(
    mut v_00_u03b1_1419_: *mut leanh::LeanObject,
    mut v_00_u03b2_1420_: *mut leanh::LeanObject,
    mut v_motive_1421_: *mut leanh::LeanObject,
    mut v_x_1422_: *mut leanh::LeanObject,
    mut v_h__1_1423_: *mut leanh::LeanObject,
    mut v_h__2_1424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1422_) == 0 {
        let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1424_);
        v___x_1425_ = leanh::lean_box(0);
        v___x_1426_ = leanh::lean_apply_1(v_h__1_1423_, v___x_1425_);
        return v___x_1426_;
    } else {
        let mut v_val_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1423_);
        v_val_1427_ = leanh::lean_ctor_get(v_x_1422_, 0);
        leanh::lean_inc(v_val_1427_);
        leanh::lean_dec_ref_known(v_x_1422_, 1);
        v___x_1428_ = leanh::lean_apply_1(v_h__2_1424_, v_val_1427_);
        return v___x_1428_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___redArg(
    mut v_x_1429_: *mut leanh::LeanObject,
    mut v_h__1_1430_: *mut leanh::LeanObject,
    mut v_h__2_1431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1429_) == 0 {
        let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1431_);
        v___x_1432_ = leanh::lean_box(0);
        v___x_1433_ = leanh::lean_apply_1(v_h__1_1430_, v___x_1432_);
        return v___x_1433_;
    } else {
        let mut v_val_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1430_);
        v_val_1434_ = leanh::lean_ctor_get(v_x_1429_, 0);
        leanh::lean_inc(v_val_1434_);
        leanh::lean_dec_ref_known(v_x_1429_, 1);
        v___x_1435_ = leanh::lean_apply_1(v_h__2_1431_, v_val_1434_);
        return v___x_1435_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(
    mut v_00_u03b1_1436_: *mut leanh::LeanObject,
    mut v_00_u03b2_1437_: *mut leanh::LeanObject,
    mut v_k_1438_: *mut leanh::LeanObject,
    mut v_motive_1439_: *mut leanh::LeanObject,
    mut v_x_1440_: *mut leanh::LeanObject,
    mut v_h__1_1441_: *mut leanh::LeanObject,
    mut v_h__2_1442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1440_) == 0 {
        let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1442_);
        v___x_1443_ = leanh::lean_box(0);
        v___x_1444_ = leanh::lean_apply_1(v_h__1_1441_, v___x_1443_);
        return v___x_1444_;
    } else {
        let mut v_val_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1441_);
        v_val_1445_ = leanh::lean_ctor_get(v_x_1440_, 0);
        leanh::lean_inc(v_val_1445_);
        leanh::lean_dec_ref_known(v_x_1440_, 1);
        v___x_1446_ = leanh::lean_apply_1(v_h__2_1442_, v_val_1445_);
        return v___x_1446_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___boxed(
    mut v_00_u03b1_1447_: *mut leanh::LeanObject,
    mut v_00_u03b2_1448_: *mut leanh::LeanObject,
    mut v_k_1449_: *mut leanh::LeanObject,
    mut v_motive_1450_: *mut leanh::LeanObject,
    mut v_x_1451_: *mut leanh::LeanObject,
    mut v_h__1_1452_: *mut leanh::LeanObject,
    mut v_h__2_1453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1454_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(v_00_u03b1_1447_, v_00_u03b2_1448_, v_k_1449_, v_motive_1450_, v_x_1451_, v_h__1_1452_, v_h__2_1453_);
    leanh::lean_dec(v_k_1449_);
    return v_res_1454_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filterMap_match__1_splitter___redArg(
    mut v_x_1455_: *mut leanh::LeanObject,
    mut v_h__1_1456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1457_ = leanh::lean_apply_2(v_h__1_1456_, v_x_1455_, leanh::lean_box(0));
    return v___x_1457_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filterMap_match__1_splitter(
    mut v_00_u03b1_1458_: *mut leanh::LeanObject,
    mut v_00_u03b3_1459_: *mut leanh::LeanObject,
    mut v_motive_1460_: *mut leanh::LeanObject,
    mut v_x_1461_: *mut leanh::LeanObject,
    mut v_h__1_1462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1463_ = leanh::lean_apply_2(v_h__1_1462_, v_x_1461_, leanh::lean_box(0));
    return v___x_1463_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(
    mut v_x_1464_: u8,
    mut v_h__1_1465_: *mut leanh::LeanObject,
    mut v_h__2_1466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1464_ == 0 {
        let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1466_);
        v___x_1467_ = leanh::lean_box(0);
        v___x_1468_ = leanh::lean_apply_1(v_h__1_1465_, v___x_1467_);
        return v___x_1468_;
    } else {
        let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1465_);
        v___x_1469_ = leanh::lean_box(0);
        v___x_1470_ = leanh::lean_apply_1(v_h__2_1466_, v___x_1469_);
        return v___x_1470_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg___boxed(
    mut v_x_1471_: *mut leanh::LeanObject,
    mut v_h__1_1472_: *mut leanh::LeanObject,
    mut v_h__2_1473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_26__boxed_1474_: u8 = 0;
    let mut v_res_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1474_ = (leanh::lean_unbox(v_x_1471_) as u8);
    v_res_1475_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(v_x_26__boxed_1474_, v_h__1_1472_, v_h__2_1473_);
    return v_res_1475_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(
    mut v_motive_1476_: *mut leanh::LeanObject,
    mut v_x_1477_: u8,
    mut v_h__1_1478_: *mut leanh::LeanObject,
    mut v_h__2_1479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1477_ == 0 {
        let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1479_);
        v___x_1480_ = leanh::lean_box(0);
        v___x_1481_ = leanh::lean_apply_1(v_h__1_1478_, v___x_1480_);
        return v___x_1481_;
    } else {
        let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1478_);
        v___x_1482_ = leanh::lean_box(0);
        v___x_1483_ = leanh::lean_apply_1(v_h__2_1479_, v___x_1482_);
        return v___x_1483_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___boxed(
    mut v_motive_1484_: *mut leanh::LeanObject,
    mut v_x_1485_: *mut leanh::LeanObject,
    mut v_h__1_1486_: *mut leanh::LeanObject,
    mut v_h__2_1487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_37__boxed_1488_: u8 = 0;
    let mut v_res_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_1488_ = (leanh::lean_unbox(v_x_1485_) as u8);
    v_res_1489_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(v_motive_1484_, v_x_37__boxed_1488_, v_h__1_1486_, v_h__2_1487_);
    return v_res_1489_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___redArg(
    mut v_v_x3f_1490_: *mut leanh::LeanObject,
    mut v_h__1_1491_: *mut leanh::LeanObject,
    mut v_h__2_1492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_v_x3f_1490_) == 0 {
        let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1492_);
        v___x_1493_ = leanh::lean_box(0);
        v___x_1494_ = leanh::lean_apply_1(v_h__1_1491_, v___x_1493_);
        return v___x_1494_;
    } else {
        let mut v_val_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1491_);
        v_val_1495_ = leanh::lean_ctor_get(v_v_x3f_1490_, 0);
        leanh::lean_inc(v_val_1495_);
        leanh::lean_dec_ref_known(v_v_x3f_1490_, 1);
        v___x_1496_ = leanh::lean_apply_1(v_h__2_1492_, v_val_1495_);
        return v___x_1496_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(
    mut v_00_u03b1_1497_: *mut leanh::LeanObject,
    mut v_00_u03b2_1498_: *mut leanh::LeanObject,
    mut v_k_1499_: *mut leanh::LeanObject,
    mut v_motive_1500_: *mut leanh::LeanObject,
    mut v_v_x3f_1501_: *mut leanh::LeanObject,
    mut v_h__1_1502_: *mut leanh::LeanObject,
    mut v_h__2_1503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_v_x3f_1501_) == 0 {
        let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1503_);
        v___x_1504_ = leanh::lean_box(0);
        v___x_1505_ = leanh::lean_apply_1(v_h__1_1502_, v___x_1504_);
        return v___x_1505_;
    } else {
        let mut v_val_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1502_);
        v_val_1506_ = leanh::lean_ctor_get(v_v_x3f_1501_, 0);
        leanh::lean_inc(v_val_1506_);
        leanh::lean_dec_ref_known(v_v_x3f_1501_, 1);
        v___x_1507_ = leanh::lean_apply_1(v_h__2_1503_, v_val_1506_);
        return v___x_1507_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___boxed(
    mut v_00_u03b1_1508_: *mut leanh::LeanObject,
    mut v_00_u03b2_1509_: *mut leanh::LeanObject,
    mut v_k_1510_: *mut leanh::LeanObject,
    mut v_motive_1511_: *mut leanh::LeanObject,
    mut v_v_x3f_1512_: *mut leanh::LeanObject,
    mut v_h__1_1513_: *mut leanh::LeanObject,
    mut v_h__2_1514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1515_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(v_00_u03b1_1508_, v_00_u03b2_1509_, v_k_1510_, v_motive_1511_, v_v_x3f_1512_, v_h__1_1513_, v_h__2_1514_);
    leanh::lean_dec(v_k_1510_);
    return v_res_1515_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(
    mut v_x_1516_: *mut leanh::LeanObject,
    mut v_h__1_1517_: *mut leanh::LeanObject,
    mut v_h__2_1518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1516_) == 0 {
        let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1518_);
        v___x_1519_ = leanh::lean_box(0);
        v___x_1520_ = leanh::lean_apply_1(v_h__1_1517_, v___x_1519_);
        return v___x_1520_;
    } else {
        let mut v_val_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1517_);
        v_val_1521_ = leanh::lean_ctor_get(v_x_1516_, 0);
        leanh::lean_inc(v_val_1521_);
        leanh::lean_dec_ref_known(v_x_1516_, 1);
        v___x_1522_ = leanh::lean_apply_1(v_h__2_1518_, v_val_1521_);
        return v___x_1522_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(
    mut v_00_u03b1_1523_: *mut leanh::LeanObject,
    mut v_00_u03b2_1524_: *mut leanh::LeanObject,
    mut v_k_1525_: *mut leanh::LeanObject,
    mut v_motive_1526_: *mut leanh::LeanObject,
    mut v_x_1527_: *mut leanh::LeanObject,
    mut v_h__1_1528_: *mut leanh::LeanObject,
    mut v_h__2_1529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1527_) == 0 {
        let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1529_);
        v___x_1530_ = leanh::lean_box(0);
        v___x_1531_ = leanh::lean_apply_1(v_h__1_1528_, v___x_1530_);
        return v___x_1531_;
    } else {
        let mut v_val_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1528_);
        v_val_1532_ = leanh::lean_ctor_get(v_x_1527_, 0);
        leanh::lean_inc(v_val_1532_);
        leanh::lean_dec_ref_known(v_x_1527_, 1);
        v___x_1533_ = leanh::lean_apply_1(v_h__2_1529_, v_val_1532_);
        return v___x_1533_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(
    mut v_00_u03b1_1534_: *mut leanh::LeanObject,
    mut v_00_u03b2_1535_: *mut leanh::LeanObject,
    mut v_k_1536_: *mut leanh::LeanObject,
    mut v_motive_1537_: *mut leanh::LeanObject,
    mut v_x_1538_: *mut leanh::LeanObject,
    mut v_h__1_1539_: *mut leanh::LeanObject,
    mut v_h__2_1540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1541_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_1534_, v_00_u03b2_1535_, v_k_1536_, v_motive_1537_, v_x_1538_, v_h__1_1539_, v_h__2_1540_);
    leanh::lean_dec(v_k_1536_);
    return v_res_1541_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter___redArg(
    mut v_x_1542_: *mut leanh::LeanObject,
    mut v_h__1_1543_: *mut leanh::LeanObject,
    mut v_h__2_1544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1542_) == 0 {
        let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1544_);
        v___x_1545_ = leanh::lean_apply_1(v_h__1_1543_, leanh::lean_box(0));
        return v___x_1545_;
    } else {
        let mut v_val_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1543_);
        v_val_1546_ = leanh::lean_ctor_get(v_x_1542_, 0);
        leanh::lean_inc(v_val_1546_);
        leanh::lean_dec_ref_known(v_x_1542_, 1);
        v_fst_1547_ = leanh::lean_ctor_get(v_val_1546_, 0);
        leanh::lean_inc(v_fst_1547_);
        v_snd_1548_ = leanh::lean_ctor_get(v_val_1546_, 1);
        leanh::lean_inc(v_snd_1548_);
        leanh::lean_dec(v_val_1546_);
        v___x_1549_ = leanh::lean_apply_3(
            v_h__2_1544_,
            v_fst_1547_,
            v_snd_1548_,
            leanh::lean_box(0),
        );
        return v___x_1549_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter(
    mut v_00_u03b1_1550_: *mut leanh::LeanObject,
    mut v_00_u03b2_1551_: *mut leanh::LeanObject,
    mut v_motive_1552_: *mut leanh::LeanObject,
    mut v_x_1553_: *mut leanh::LeanObject,
    mut v_h__1_1554_: *mut leanh::LeanObject,
    mut v_h__2_1555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1553_) == 0 {
        let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1555_);
        v___x_1556_ = leanh::lean_apply_1(v_h__1_1554_, leanh::lean_box(0));
        return v___x_1556_;
    } else {
        let mut v_val_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1554_);
        v_val_1557_ = leanh::lean_ctor_get(v_x_1553_, 0);
        leanh::lean_inc(v_val_1557_);
        leanh::lean_dec_ref_known(v_x_1553_, 1);
        v_fst_1558_ = leanh::lean_ctor_get(v_val_1557_, 0);
        leanh::lean_inc(v_fst_1558_);
        v_snd_1559_ = leanh::lean_ctor_get(v_val_1557_, 1);
        leanh::lean_inc(v_snd_1559_);
        leanh::lean_dec(v_val_1557_);
        v___x_1560_ = leanh::lean_apply_3(
            v_h__2_1555_,
            v_fst_1558_,
            v_snd_1559_,
            leanh::lean_box(0),
        );
        return v___x_1560_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___redArg(
    mut v_x_1561_: *mut leanh::LeanObject,
    mut v_h__1_1562_: *mut leanh::LeanObject,
    mut v_h__2_1563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1561_) == 0 {
        let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1563_);
        v___x_1564_ = leanh::lean_box(0);
        v___x_1565_ = leanh::lean_apply_1(v_h__1_1562_, v___x_1564_);
        return v___x_1565_;
    } else {
        let mut v_val_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1562_);
        v_val_1566_ = leanh::lean_ctor_get(v_x_1561_, 0);
        leanh::lean_inc(v_val_1566_);
        leanh::lean_dec_ref_known(v_x_1561_, 1);
        v___x_1567_ = leanh::lean_apply_1(v_h__2_1563_, v_val_1566_);
        return v___x_1567_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(
    mut v_00_u03b1_1568_: *mut leanh::LeanObject,
    mut v_00_u03b2_1569_: *mut leanh::LeanObject,
    mut v_k_1570_: *mut leanh::LeanObject,
    mut v_motive_1571_: *mut leanh::LeanObject,
    mut v_x_1572_: *mut leanh::LeanObject,
    mut v_h__1_1573_: *mut leanh::LeanObject,
    mut v_h__2_1574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1572_) == 0 {
        let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1574_);
        v___x_1575_ = leanh::lean_box(0);
        v___x_1576_ = leanh::lean_apply_1(v_h__1_1573_, v___x_1575_);
        return v___x_1576_;
    } else {
        let mut v_val_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1573_);
        v_val_1577_ = leanh::lean_ctor_get(v_x_1572_, 0);
        leanh::lean_inc(v_val_1577_);
        leanh::lean_dec_ref_known(v_x_1572_, 1);
        v___x_1578_ = leanh::lean_apply_1(v_h__2_1574_, v_val_1577_);
        return v___x_1578_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___boxed(
    mut v_00_u03b1_1579_: *mut leanh::LeanObject,
    mut v_00_u03b2_1580_: *mut leanh::LeanObject,
    mut v_k_1581_: *mut leanh::LeanObject,
    mut v_motive_1582_: *mut leanh::LeanObject,
    mut v_x_1583_: *mut leanh::LeanObject,
    mut v_h__1_1584_: *mut leanh::LeanObject,
    mut v_h__2_1585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1586_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(v_00_u03b1_1579_, v_00_u03b2_1580_, v_k_1581_, v_motive_1582_, v_x_1583_, v_h__1_1584_, v_h__2_1585_);
    leanh::lean_dec(v_k_1581_);
    return v_res_1586_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(
    mut v_x_1587_: u8,
    mut v_h__1_1588_: *mut leanh::LeanObject,
    mut v_h__2_1589_: *mut leanh::LeanObject,
    mut v_h__3_1590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_x_1587_ {
        0 => {
            let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1590_);
            leanh::lean_dec(v_h__2_1589_);
            v___x_1591_ = leanh::lean_apply_1(v_h__1_1588_, leanh::lean_box(0));
            return v___x_1591_;
        }
        1 => {
            let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1589_);
            leanh::lean_dec(v_h__1_1588_);
            v___x_1592_ = leanh::lean_apply_1(v_h__3_1590_, leanh::lean_box(0));
            return v___x_1592_;
        }
        _ => {
            let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1590_);
            leanh::lean_dec(v_h__1_1588_);
            v___x_1593_ = leanh::lean_apply_1(v_h__2_1589_, leanh::lean_box(0));
            return v___x_1593_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg___boxed(
    mut v_x_1594_: *mut leanh::LeanObject,
    mut v_h__1_1595_: *mut leanh::LeanObject,
    mut v_h__2_1596_: *mut leanh::LeanObject,
    mut v_h__3_1597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_33__boxed_1598_: u8 = 0;
    let mut v_res_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_33__boxed_1598_ = (leanh::lean_unbox(v_x_1594_) as u8);
    v_res_1599_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(v_x_33__boxed_1598_, v_h__1_1595_, v_h__2_1596_, v_h__3_1597_);
    return v_res_1599_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(
    mut v_motive_1600_: *mut leanh::LeanObject,
    mut v_x_1601_: u8,
    mut v_h__1_1602_: *mut leanh::LeanObject,
    mut v_h__2_1603_: *mut leanh::LeanObject,
    mut v_h__3_1604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_x_1601_ {
        0 => {
            let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1604_);
            leanh::lean_dec(v_h__2_1603_);
            v___x_1605_ = leanh::lean_apply_1(v_h__1_1602_, leanh::lean_box(0));
            return v___x_1605_;
        }
        1 => {
            let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1603_);
            leanh::lean_dec(v_h__1_1602_);
            v___x_1606_ = leanh::lean_apply_1(v_h__3_1604_, leanh::lean_box(0));
            return v___x_1606_;
        }
        _ => {
            let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1604_);
            leanh::lean_dec(v_h__1_1602_);
            v___x_1607_ = leanh::lean_apply_1(v_h__2_1603_, leanh::lean_box(0));
            return v___x_1607_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___boxed(
    mut v_motive_1608_: *mut leanh::LeanObject,
    mut v_x_1609_: *mut leanh::LeanObject,
    mut v_h__1_1610_: *mut leanh::LeanObject,
    mut v_h__2_1611_: *mut leanh::LeanObject,
    mut v_h__3_1612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_42__boxed_1613_: u8 = 0;
    let mut v_res_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_42__boxed_1613_ = (leanh::lean_unbox(v_x_1609_) as u8);
    v_res_1614_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(v_motive_1608_, v_x_42__boxed_1613_, v_h__1_1610_, v_h__2_1611_, v_h__3_1612_);
    return v_res_1614_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter___redArg(
    mut v_x_1615_: *mut leanh::LeanObject,
    mut v_h__1_1616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1617_ = leanh::lean_apply_4(
        v_h__1_1616_,
        v_x_1615_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1617_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter(
    mut v_00_u03b1_1618_: *mut leanh::LeanObject,
    mut v_00_u03b2_1619_: *mut leanh::LeanObject,
    mut v_l_x27_1620_: *mut leanh::LeanObject,
    mut v_motive_1621_: *mut leanh::LeanObject,
    mut v_x_1622_: *mut leanh::LeanObject,
    mut v_h__1_1623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1624_ = leanh::lean_apply_4(
        v_h__1_1623_,
        v_x_1622_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1624_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter___boxed(
    mut v_00_u03b1_1625_: *mut leanh::LeanObject,
    mut v_00_u03b2_1626_: *mut leanh::LeanObject,
    mut v_l_x27_1627_: *mut leanh::LeanObject,
    mut v_motive_1628_: *mut leanh::LeanObject,
    mut v_x_1629_: *mut leanh::LeanObject,
    mut v_h__1_1630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1631_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter(v_00_u03b1_1625_, v_00_u03b2_1626_, v_l_x27_1627_, v_motive_1628_, v_x_1629_, v_h__1_1630_);
    leanh::lean_dec(v_l_x27_1627_);
    return v_res_1631_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(
    mut v_l_1632_: *mut leanh::LeanObject,
    mut v_h__1_1633_: *mut leanh::LeanObject,
    mut v_h__2_1634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_1632_) == 0 {
        let mut v_size_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1633_);
        v_size_1635_ = leanh::lean_ctor_get(v_l_1632_, 0);
        leanh::lean_inc(v_size_1635_);
        v_k_1636_ = leanh::lean_ctor_get(v_l_1632_, 1);
        leanh::lean_inc(v_k_1636_);
        v_v_1637_ = leanh::lean_ctor_get(v_l_1632_, 2);
        leanh::lean_inc(v_v_1637_);
        v_l_1638_ = leanh::lean_ctor_get(v_l_1632_, 3);
        leanh::lean_inc(v_l_1638_);
        v_r_1639_ = leanh::lean_ctor_get(v_l_1632_, 4);
        leanh::lean_inc(v_r_1639_);
        leanh::lean_dec_ref_known(v_l_1632_, 5);
        v___x_1640_ = leanh::lean_apply_5(
            v_h__2_1634_,
            v_size_1635_,
            v_k_1636_,
            v_v_1637_,
            v_l_1638_,
            v_r_1639_,
        );
        return v___x_1640_;
    } else {
        let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1634_);
        v___x_1641_ = leanh::lean_box(0);
        v___x_1642_ = leanh::lean_apply_1(v_h__1_1633_, v___x_1641_);
        return v___x_1642_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(
    mut v_00_u03b1_1643_: *mut leanh::LeanObject,
    mut v_00_u03b2_1644_: *mut leanh::LeanObject,
    mut v_motive_1645_: *mut leanh::LeanObject,
    mut v_l_1646_: *mut leanh::LeanObject,
    mut v_h__1_1647_: *mut leanh::LeanObject,
    mut v_h__2_1648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_1646_) == 0 {
        let mut v_size_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1647_);
        v_size_1649_ = leanh::lean_ctor_get(v_l_1646_, 0);
        leanh::lean_inc(v_size_1649_);
        v_k_1650_ = leanh::lean_ctor_get(v_l_1646_, 1);
        leanh::lean_inc(v_k_1650_);
        v_v_1651_ = leanh::lean_ctor_get(v_l_1646_, 2);
        leanh::lean_inc(v_v_1651_);
        v_l_1652_ = leanh::lean_ctor_get(v_l_1646_, 3);
        leanh::lean_inc(v_l_1652_);
        v_r_1653_ = leanh::lean_ctor_get(v_l_1646_, 4);
        leanh::lean_inc(v_r_1653_);
        leanh::lean_dec_ref_known(v_l_1646_, 5);
        v___x_1654_ = leanh::lean_apply_5(
            v_h__2_1648_,
            v_size_1649_,
            v_k_1650_,
            v_v_1651_,
            v_l_1652_,
            v_r_1653_,
        );
        return v___x_1654_;
    } else {
        let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1648_);
        v___x_1655_ = leanh::lean_box(0);
        v___x_1656_ = leanh::lean_apply_1(v_h__1_1647_, v___x_1655_);
        return v___x_1656_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(
    mut v_t_1657_: *mut leanh::LeanObject,
    mut v_h__1_1658_: *mut leanh::LeanObject,
    mut v_h__2_1659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1657_) == 0 {
        let mut v_size_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1658_);
        v_size_1660_ = leanh::lean_ctor_get(v_t_1657_, 0);
        leanh::lean_inc(v_size_1660_);
        v_k_1661_ = leanh::lean_ctor_get(v_t_1657_, 1);
        leanh::lean_inc(v_k_1661_);
        v_v_1662_ = leanh::lean_ctor_get(v_t_1657_, 2);
        leanh::lean_inc(v_v_1662_);
        v_l_1663_ = leanh::lean_ctor_get(v_t_1657_, 3);
        leanh::lean_inc(v_l_1663_);
        v_r_1664_ = leanh::lean_ctor_get(v_t_1657_, 4);
        leanh::lean_inc(v_r_1664_);
        leanh::lean_dec_ref_known(v_t_1657_, 5);
        v___x_1665_ = leanh::lean_apply_5(
            v_h__2_1659_,
            v_size_1660_,
            v_k_1661_,
            v_v_1662_,
            v_l_1663_,
            v_r_1664_,
        );
        return v___x_1665_;
    } else {
        let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1659_);
        v___x_1666_ = leanh::lean_box(0);
        v___x_1667_ = leanh::lean_apply_1(v_h__1_1658_, v___x_1666_);
        return v___x_1667_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(
    mut v_00_u03b1_1668_: *mut leanh::LeanObject,
    mut v_00_u03b2_1669_: *mut leanh::LeanObject,
    mut v_motive_1670_: *mut leanh::LeanObject,
    mut v_t_1671_: *mut leanh::LeanObject,
    mut v_h__1_1672_: *mut leanh::LeanObject,
    mut v_h__2_1673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1671_) == 0 {
        let mut v_size_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1672_);
        v_size_1674_ = leanh::lean_ctor_get(v_t_1671_, 0);
        leanh::lean_inc(v_size_1674_);
        v_k_1675_ = leanh::lean_ctor_get(v_t_1671_, 1);
        leanh::lean_inc(v_k_1675_);
        v_v_1676_ = leanh::lean_ctor_get(v_t_1671_, 2);
        leanh::lean_inc(v_v_1676_);
        v_l_1677_ = leanh::lean_ctor_get(v_t_1671_, 3);
        leanh::lean_inc(v_l_1677_);
        v_r_1678_ = leanh::lean_ctor_get(v_t_1671_, 4);
        leanh::lean_inc(v_r_1678_);
        leanh::lean_dec_ref_known(v_t_1671_, 5);
        v___x_1679_ = leanh::lean_apply_5(
            v_h__2_1673_,
            v_size_1674_,
            v_k_1675_,
            v_v_1676_,
            v_l_1677_,
            v_r_1678_,
        );
        return v___x_1679_;
    } else {
        let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1673_);
        v___x_1680_ = leanh::lean_box(0);
        v___x_1681_ = leanh::lean_apply_1(v_h__1_1672_, v___x_1680_);
        return v___x_1681_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter___redArg(
    mut v_____do__lift_1682_: *mut leanh::LeanObject,
    mut v_h__1_1683_: *mut leanh::LeanObject,
    mut v_h__2_1684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1682_) == 0 {
        let mut v_a_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1684_);
        v_a_1685_ = leanh::lean_ctor_get(v_____do__lift_1682_, 0);
        leanh::lean_inc(v_a_1685_);
        leanh::lean_dec_ref_known(v_____do__lift_1682_, 1);
        v___x_1686_ = leanh::lean_apply_1(v_h__1_1683_, v_a_1685_);
        return v___x_1686_;
    } else {
        let mut v_a_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1683_);
        v_a_1687_ = leanh::lean_ctor_get(v_____do__lift_1682_, 0);
        leanh::lean_inc(v_a_1687_);
        leanh::lean_dec_ref_known(v_____do__lift_1682_, 1);
        v___x_1688_ = leanh::lean_apply_1(v_h__2_1684_, v_a_1687_);
        return v___x_1688_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter(
    mut v_00_u03b4_1689_: *mut leanh::LeanObject,
    mut v_motive_1690_: *mut leanh::LeanObject,
    mut v_____do__lift_1691_: *mut leanh::LeanObject,
    mut v_h__1_1692_: *mut leanh::LeanObject,
    mut v_h__2_1693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1691_) == 0 {
        let mut v_a_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1693_);
        v_a_1694_ = leanh::lean_ctor_get(v_____do__lift_1691_, 0);
        leanh::lean_inc(v_a_1694_);
        leanh::lean_dec_ref_known(v_____do__lift_1691_, 1);
        v___x_1695_ = leanh::lean_apply_1(v_h__1_1692_, v_a_1694_);
        return v___x_1695_;
    } else {
        let mut v_a_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1692_);
        v_a_1696_ = leanh::lean_ctor_get(v_____do__lift_1691_, 0);
        leanh::lean_inc(v_a_1696_);
        leanh::lean_dec_ref_known(v_____do__lift_1691_, 1);
        v___x_1697_ = leanh::lean_apply_1(v_h__2_1693_, v_a_1696_);
        return v___x_1697_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter___redArg(
    mut v_x_1698_: *mut leanh::LeanObject,
    mut v_h__1_1699_: *mut leanh::LeanObject,
    mut v_h__2_1700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1698_) == 0 {
        let mut v_a_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1699_);
        v_a_1701_ = leanh::lean_ctor_get(v_x_1698_, 0);
        leanh::lean_inc(v_a_1701_);
        leanh::lean_dec_ref_known(v_x_1698_, 1);
        v___x_1702_ = leanh::lean_apply_1(v_h__2_1700_, v_a_1701_);
        return v___x_1702_;
    } else {
        let mut v_a_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1700_);
        v_a_1703_ = leanh::lean_ctor_get(v_x_1698_, 0);
        leanh::lean_inc(v_a_1703_);
        leanh::lean_dec_ref_known(v_x_1698_, 1);
        v___x_1704_ = leanh::lean_apply_1(v_h__1_1699_, v_a_1703_);
        return v___x_1704_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter(
    mut v_00_u03b4_1705_: *mut leanh::LeanObject,
    mut v_motive_1706_: *mut leanh::LeanObject,
    mut v_x_1707_: *mut leanh::LeanObject,
    mut v_h__1_1708_: *mut leanh::LeanObject,
    mut v_h__2_1709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1707_) == 0 {
        let mut v_a_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1708_);
        v_a_1710_ = leanh::lean_ctor_get(v_x_1707_, 0);
        leanh::lean_inc(v_a_1710_);
        leanh::lean_dec_ref_known(v_x_1707_, 1);
        v___x_1711_ = leanh::lean_apply_1(v_h__2_1709_, v_a_1710_);
        return v___x_1711_;
    } else {
        let mut v_a_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1709_);
        v_a_1712_ = leanh::lean_ctor_get(v_x_1707_, 0);
        leanh::lean_inc(v_a_1712_);
        leanh::lean_dec_ref_known(v_x_1707_, 1);
        v___x_1713_ = leanh::lean_apply_1(v_h__1_1708_, v_a_1712_);
        return v___x_1713_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_1714_: *mut leanh::LeanObject,
    mut v_h__1_1715_: *mut leanh::LeanObject,
    mut v_h__2_1716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_b_1714_) == 0 {
        let mut v_a_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1715_);
        v_a_1717_ = leanh::lean_ctor_get(v_b_1714_, 0);
        leanh::lean_inc(v_a_1717_);
        leanh::lean_dec_ref_known(v_b_1714_, 1);
        v___x_1718_ = leanh::lean_apply_1(v_h__2_1716_, v_a_1717_);
        return v___x_1718_;
    } else {
        let mut v_a_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1716_);
        v_a_1719_ = leanh::lean_ctor_get(v_b_1714_, 0);
        leanh::lean_inc(v_a_1719_);
        leanh::lean_dec_ref_known(v_b_1714_, 1);
        v___x_1720_ = leanh::lean_apply_1(v_h__1_1715_, v_a_1719_);
        return v___x_1720_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_1721_: *mut leanh::LeanObject,
    mut v_motive_1722_: *mut leanh::LeanObject,
    mut v_b_1723_: *mut leanh::LeanObject,
    mut v_h__1_1724_: *mut leanh::LeanObject,
    mut v_h__2_1725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_b_1723_) == 0 {
        let mut v_a_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1724_);
        v_a_1726_ = leanh::lean_ctor_get(v_b_1723_, 0);
        leanh::lean_inc(v_a_1726_);
        leanh::lean_dec_ref_known(v_b_1723_, 1);
        v___x_1727_ = leanh::lean_apply_1(v_h__2_1725_, v_a_1726_);
        return v___x_1727_;
    } else {
        let mut v_a_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1725_);
        v_a_1728_ = leanh::lean_ctor_get(v_b_1723_, 0);
        leanh::lean_inc(v_a_1728_);
        leanh::lean_dec_ref_known(v_b_1723_, 1);
        v___x_1729_ = leanh::lean_apply_1(v_h__1_1724_, v_a_1728_);
        return v___x_1729_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(
    mut v_x_1730_: *mut leanh::LeanObject,
    mut v_h__1_1731_: *mut leanh::LeanObject,
    mut v_h__2_1732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1730_) == 0 {
        let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1732_);
        v___x_1733_ = leanh::lean_box(0);
        v___x_1734_ = leanh::lean_apply_1(v_h__1_1731_, v___x_1733_);
        return v___x_1734_;
    } else {
        let mut v_val_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1731_);
        v_val_1735_ = leanh::lean_ctor_get(v_x_1730_, 0);
        leanh::lean_inc(v_val_1735_);
        leanh::lean_dec_ref_known(v_x_1730_, 1);
        v___x_1736_ = leanh::lean_apply_1(v_h__2_1732_, v_val_1735_);
        return v___x_1736_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter(
    mut v_00_u03b2_1737_: *mut leanh::LeanObject,
    mut v_motive_1738_: *mut leanh::LeanObject,
    mut v_x_1739_: *mut leanh::LeanObject,
    mut v_h__1_1740_: *mut leanh::LeanObject,
    mut v_h__2_1741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1739_) == 0 {
        let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1741_);
        v___x_1742_ = leanh::lean_box(0);
        v___x_1743_ = leanh::lean_apply_1(v_h__1_1740_, v___x_1742_);
        return v___x_1743_;
    } else {
        let mut v_val_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1740_);
        v_val_1744_ = leanh::lean_ctor_get(v_x_1739_, 0);
        leanh::lean_inc(v_val_1744_);
        leanh::lean_dec_ref_known(v_x_1739_, 1);
        v___x_1745_ = leanh::lean_apply_1(v_h__2_1741_, v_val_1744_);
        return v___x_1745_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter___redArg(
    mut v_x_1746_: *mut leanh::LeanObject,
    mut v_h__1_1747_: *mut leanh::LeanObject,
    mut v_h__2_1748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1746_) == 0 {
        let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1748_);
        v___x_1749_ = leanh::lean_box(0);
        v___x_1750_ = leanh::lean_apply_1(v_h__1_1747_, v___x_1749_);
        return v___x_1750_;
    } else {
        let mut v_val_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1747_);
        v_val_1751_ = leanh::lean_ctor_get(v_x_1746_, 0);
        leanh::lean_inc(v_val_1751_);
        leanh::lean_dec_ref_known(v_x_1746_, 1);
        v_fst_1752_ = leanh::lean_ctor_get(v_val_1751_, 0);
        leanh::lean_inc(v_fst_1752_);
        v_snd_1753_ = leanh::lean_ctor_get(v_val_1751_, 1);
        leanh::lean_inc(v_snd_1753_);
        leanh::lean_dec(v_val_1751_);
        v___x_1754_ = leanh::lean_apply_2(v_h__2_1748_, v_fst_1752_, v_snd_1753_);
        return v___x_1754_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter(
    mut v_00_u03b1_1755_: *mut leanh::LeanObject,
    mut v_00_u03b2_1756_: *mut leanh::LeanObject,
    mut v_motive_1757_: *mut leanh::LeanObject,
    mut v_x_1758_: *mut leanh::LeanObject,
    mut v_h__1_1759_: *mut leanh::LeanObject,
    mut v_h__2_1760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1758_) == 0 {
        let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1760_);
        v___x_1761_ = leanh::lean_box(0);
        v___x_1762_ = leanh::lean_apply_1(v_h__1_1759_, v___x_1761_);
        return v___x_1762_;
    } else {
        let mut v_val_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1759_);
        v_val_1763_ = leanh::lean_ctor_get(v_x_1758_, 0);
        leanh::lean_inc(v_val_1763_);
        leanh::lean_dec_ref_known(v_x_1758_, 1);
        v_fst_1764_ = leanh::lean_ctor_get(v_val_1763_, 0);
        leanh::lean_inc(v_fst_1764_);
        v_snd_1765_ = leanh::lean_ctor_get(v_val_1763_, 1);
        leanh::lean_inc(v_snd_1765_);
        leanh::lean_dec(v_val_1763_);
        v___x_1766_ = leanh::lean_apply_2(v_h__2_1760_, v_fst_1764_, v_snd_1765_);
        return v___x_1766_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(
    mut v_x_1767_: *mut leanh::LeanObject,
    mut v_h__1_1768_: *mut leanh::LeanObject,
    mut v_h__2_1769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1767_) == 0 {
        let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1769_);
        v___x_1770_ = leanh::lean_box(0);
        v___x_1771_ = leanh::lean_apply_1(v_h__1_1768_, v___x_1770_);
        return v___x_1771_;
    } else {
        let mut v_val_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1768_);
        v_val_1772_ = leanh::lean_ctor_get(v_x_1767_, 0);
        leanh::lean_inc(v_val_1772_);
        leanh::lean_dec_ref_known(v_x_1767_, 1);
        v___x_1773_ = leanh::lean_apply_1(v_h__2_1769_, v_val_1772_);
        return v___x_1773_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter(
    mut v_00_u03b2_1774_: *mut leanh::LeanObject,
    mut v_motive_1775_: *mut leanh::LeanObject,
    mut v_x_1776_: *mut leanh::LeanObject,
    mut v_h__1_1777_: *mut leanh::LeanObject,
    mut v_h__2_1778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1776_) == 0 {
        let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1778_);
        v___x_1779_ = leanh::lean_box(0);
        v___x_1780_ = leanh::lean_apply_1(v_h__1_1777_, v___x_1779_);
        return v___x_1780_;
    } else {
        let mut v_val_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1777_);
        v_val_1781_ = leanh::lean_ctor_get(v_x_1776_, 0);
        leanh::lean_inc(v_val_1781_);
        leanh::lean_dec_ref_known(v_x_1776_, 1);
        v___x_1782_ = leanh::lean_apply_1(v_h__2_1778_, v_val_1781_);
        return v___x_1782_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__3_splitter___redArg(
    mut v_t_1783_: *mut leanh::LeanObject,
    mut v_h__1_1784_: *mut leanh::LeanObject,
    mut v_h__2_1785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1783_) == 0 {
        let mut v_size_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1784_);
        v_size_1786_ = leanh::lean_ctor_get(v_t_1783_, 0);
        leanh::lean_inc(v_size_1786_);
        v_k_1787_ = leanh::lean_ctor_get(v_t_1783_, 1);
        leanh::lean_inc(v_k_1787_);
        v_v_1788_ = leanh::lean_ctor_get(v_t_1783_, 2);
        leanh::lean_inc(v_v_1788_);
        v_l_1789_ = leanh::lean_ctor_get(v_t_1783_, 3);
        leanh::lean_inc(v_l_1789_);
        v_r_1790_ = leanh::lean_ctor_get(v_t_1783_, 4);
        leanh::lean_inc(v_r_1790_);
        leanh::lean_dec_ref_known(v_t_1783_, 5);
        v___x_1791_ = leanh::lean_apply_6(
            v_h__2_1785_,
            v_size_1786_,
            v_k_1787_,
            v_v_1788_,
            v_l_1789_,
            v_r_1790_,
            leanh::lean_box(0),
        );
        return v___x_1791_;
    } else {
        let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1785_);
        v___x_1792_ = leanh::lean_apply_1(v_h__1_1784_, leanh::lean_box(0));
        return v___x_1792_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__3_splitter(
    mut v_00_u03b1_1793_: *mut leanh::LeanObject,
    mut v_00_u03b2_1794_: *mut leanh::LeanObject,
    mut v_motive_1795_: *mut leanh::LeanObject,
    mut v_t_1796_: *mut leanh::LeanObject,
    mut v_hl_1797_: *mut leanh::LeanObject,
    mut v_h__1_1798_: *mut leanh::LeanObject,
    mut v_h__2_1799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1796_) == 0 {
        let mut v_size_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1798_);
        v_size_1800_ = leanh::lean_ctor_get(v_t_1796_, 0);
        leanh::lean_inc(v_size_1800_);
        v_k_1801_ = leanh::lean_ctor_get(v_t_1796_, 1);
        leanh::lean_inc(v_k_1801_);
        v_v_1802_ = leanh::lean_ctor_get(v_t_1796_, 2);
        leanh::lean_inc(v_v_1802_);
        v_l_1803_ = leanh::lean_ctor_get(v_t_1796_, 3);
        leanh::lean_inc(v_l_1803_);
        v_r_1804_ = leanh::lean_ctor_get(v_t_1796_, 4);
        leanh::lean_inc(v_r_1804_);
        leanh::lean_dec_ref_known(v_t_1796_, 5);
        v___x_1805_ = leanh::lean_apply_6(
            v_h__2_1799_,
            v_size_1800_,
            v_k_1801_,
            v_v_1802_,
            v_l_1803_,
            v_r_1804_,
            leanh::lean_box(0),
        );
        return v___x_1805_;
    } else {
        let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1799_);
        v___x_1806_ = leanh::lean_apply_1(v_h__1_1798_, leanh::lean_box(0));
        return v___x_1806_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter___redArg(
    mut v_x_1807_: *mut leanh::LeanObject,
    mut v_h__1_1808_: *mut leanh::LeanObject,
    mut v_h__2_1809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1807_) == 0 {
        let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1809_);
        v___x_1810_ = leanh::lean_box(0);
        v___x_1811_ = leanh::lean_apply_1(v_h__1_1808_, v___x_1810_);
        return v___x_1811_;
    } else {
        let mut v_val_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1808_);
        v_val_1812_ = leanh::lean_ctor_get(v_x_1807_, 0);
        leanh::lean_inc(v_val_1812_);
        leanh::lean_dec_ref_known(v_x_1807_, 1);
        v___x_1813_ = leanh::lean_apply_1(v_h__2_1809_, v_val_1812_);
        return v___x_1813_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter(
    mut v_00_u03b2_1814_: *mut leanh::LeanObject,
    mut v_motive_1815_: *mut leanh::LeanObject,
    mut v_x_1816_: *mut leanh::LeanObject,
    mut v_h__1_1817_: *mut leanh::LeanObject,
    mut v_h__2_1818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1816_) == 0 {
        let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1818_);
        v___x_1819_ = leanh::lean_box(0);
        v___x_1820_ = leanh::lean_apply_1(v_h__1_1817_, v___x_1819_);
        return v___x_1820_;
    } else {
        let mut v_val_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1817_);
        v_val_1821_ = leanh::lean_ctor_get(v_x_1816_, 0);
        leanh::lean_inc(v_val_1821_);
        leanh::lean_dec_ref_known(v_x_1816_, 1);
        v___x_1822_ = leanh::lean_apply_1(v_h__2_1818_, v_val_1821_);
        return v___x_1822_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(
    mut v_x_1823_: u8,
    mut v_h__1_1824_: *mut leanh::LeanObject,
    mut v_h__2_1825_: *mut leanh::LeanObject,
    mut v_h__3_1826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_x_1823_ {
        0 => {
            let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1826_);
            leanh::lean_dec(v_h__2_1825_);
            v___x_1827_ = leanh::lean_box(0);
            v___x_1828_ = leanh::lean_apply_1(v_h__1_1824_, v___x_1827_);
            return v___x_1828_;
        }
        1 => {
            let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1825_);
            leanh::lean_dec(v_h__1_1824_);
            v___x_1829_ = leanh::lean_box(0);
            v___x_1830_ = leanh::lean_apply_1(v_h__3_1826_, v___x_1829_);
            return v___x_1830_;
        }
        _ => {
            let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1826_);
            leanh::lean_dec(v_h__1_1824_);
            v___x_1831_ = leanh::lean_box(0);
            v___x_1832_ = leanh::lean_apply_1(v_h__2_1825_, v___x_1831_);
            return v___x_1832_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(
    mut v_x_1833_: *mut leanh::LeanObject,
    mut v_h__1_1834_: *mut leanh::LeanObject,
    mut v_h__2_1835_: *mut leanh::LeanObject,
    mut v_h__3_1836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_36__boxed_1837_: u8 = 0;
    let mut v_res_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_1837_ = (leanh::lean_unbox(v_x_1833_) as u8);
    v_res_1838_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_36__boxed_1837_, v_h__1_1834_, v_h__2_1835_, v_h__3_1836_);
    return v_res_1838_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(
    mut v_motive_1839_: *mut leanh::LeanObject,
    mut v_x_1840_: u8,
    mut v_h__1_1841_: *mut leanh::LeanObject,
    mut v_h__2_1842_: *mut leanh::LeanObject,
    mut v_h__3_1843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_x_1840_ {
        0 => {
            let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1843_);
            leanh::lean_dec(v_h__2_1842_);
            v___x_1844_ = leanh::lean_box(0);
            v___x_1845_ = leanh::lean_apply_1(v_h__1_1841_, v___x_1844_);
            return v___x_1845_;
        }
        1 => {
            let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1842_);
            leanh::lean_dec(v_h__1_1841_);
            v___x_1846_ = leanh::lean_box(0);
            v___x_1847_ = leanh::lean_apply_1(v_h__3_1843_, v___x_1846_);
            return v___x_1847_;
        }
        _ => {
            let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1843_);
            leanh::lean_dec(v_h__1_1841_);
            v___x_1848_ = leanh::lean_box(0);
            v___x_1849_ = leanh::lean_apply_1(v_h__2_1842_, v___x_1848_);
            return v___x_1849_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(
    mut v_motive_1850_: *mut leanh::LeanObject,
    mut v_x_1851_: *mut leanh::LeanObject,
    mut v_h__1_1852_: *mut leanh::LeanObject,
    mut v_h__2_1853_: *mut leanh::LeanObject,
    mut v_h__3_1854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_51__boxed_1855_: u8 = 0;
    let mut v_res_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_51__boxed_1855_ = (leanh::lean_unbox(v_x_1851_) as u8);
    v_res_1856_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(v_motive_1850_, v_x_51__boxed_1855_, v_h__1_1852_, v_h__2_1853_, v_h__3_1854_);
    return v_res_1856_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter___redArg(
    mut v_x_1857_: *mut leanh::LeanObject,
    mut v_h__1_1858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1859_ = leanh::lean_apply_4(
        v_h__1_1858_,
        v_x_1857_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1859_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter(
    mut v_00_u03b1_1860_: *mut leanh::LeanObject,
    mut v_00_u03b2_1861_: *mut leanh::LeanObject,
    mut v_l_x27_1862_: *mut leanh::LeanObject,
    mut v_motive_1863_: *mut leanh::LeanObject,
    mut v_x_1864_: *mut leanh::LeanObject,
    mut v_h__1_1865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1866_ = leanh::lean_apply_4(
        v_h__1_1865_,
        v_x_1864_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1866_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter___boxed(
    mut v_00_u03b1_1867_: *mut leanh::LeanObject,
    mut v_00_u03b2_1868_: *mut leanh::LeanObject,
    mut v_l_x27_1869_: *mut leanh::LeanObject,
    mut v_motive_1870_: *mut leanh::LeanObject,
    mut v_x_1871_: *mut leanh::LeanObject,
    mut v_h__1_1872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1873_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter(v_00_u03b1_1867_, v_00_u03b2_1868_, v_l_x27_1869_, v_motive_1870_, v_x_1871_, v_h__1_1872_);
    leanh::lean_dec(v_l_x27_1869_);
    return v_res_1873_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter___redArg(
    mut v_t_1874_: *mut leanh::LeanObject,
    mut v_h__1_1875_: *mut leanh::LeanObject,
    mut v_h__2_1876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1874_) == 0 {
        let mut v_size_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1875_);
        v_size_1877_ = leanh::lean_ctor_get(v_t_1874_, 0);
        leanh::lean_inc(v_size_1877_);
        v_k_1878_ = leanh::lean_ctor_get(v_t_1874_, 1);
        leanh::lean_inc(v_k_1878_);
        v_v_1879_ = leanh::lean_ctor_get(v_t_1874_, 2);
        leanh::lean_inc(v_v_1879_);
        v_l_1880_ = leanh::lean_ctor_get(v_t_1874_, 3);
        leanh::lean_inc(v_l_1880_);
        v_r_1881_ = leanh::lean_ctor_get(v_t_1874_, 4);
        leanh::lean_inc(v_r_1881_);
        leanh::lean_dec_ref_known(v_t_1874_, 5);
        v___x_1882_ = leanh::lean_apply_5(
            v_h__2_1876_,
            v_size_1877_,
            v_k_1878_,
            v_v_1879_,
            v_l_1880_,
            v_r_1881_,
        );
        return v___x_1882_;
    } else {
        let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1876_);
        v___x_1883_ = leanh::lean_box(0);
        v___x_1884_ = leanh::lean_apply_1(v_h__1_1875_, v___x_1883_);
        return v___x_1884_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter(
    mut v_00_u03b1_1885_: *mut leanh::LeanObject,
    mut v_00_u03b2_1886_: *mut leanh::LeanObject,
    mut v_motive_1887_: *mut leanh::LeanObject,
    mut v_t_1888_: *mut leanh::LeanObject,
    mut v_h__1_1889_: *mut leanh::LeanObject,
    mut v_h__2_1890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1888_) == 0 {
        let mut v_size_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1889_);
        v_size_1891_ = leanh::lean_ctor_get(v_t_1888_, 0);
        leanh::lean_inc(v_size_1891_);
        v_k_1892_ = leanh::lean_ctor_get(v_t_1888_, 1);
        leanh::lean_inc(v_k_1892_);
        v_v_1893_ = leanh::lean_ctor_get(v_t_1888_, 2);
        leanh::lean_inc(v_v_1893_);
        v_l_1894_ = leanh::lean_ctor_get(v_t_1888_, 3);
        leanh::lean_inc(v_l_1894_);
        v_r_1895_ = leanh::lean_ctor_get(v_t_1888_, 4);
        leanh::lean_inc(v_r_1895_);
        leanh::lean_dec_ref_known(v_t_1888_, 5);
        v___x_1896_ = leanh::lean_apply_5(
            v_h__2_1890_,
            v_size_1891_,
            v_k_1892_,
            v_v_1893_,
            v_l_1894_,
            v_r_1895_,
        );
        return v___x_1896_;
    } else {
        let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1890_);
        v___x_1897_ = leanh::lean_box(0);
        v___x_1898_ = leanh::lean_apply_1(v_h__1_1889_, v___x_1897_);
        return v___x_1898_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter___redArg(
    mut v_x_1899_: *mut leanh::LeanObject,
    mut v_h__1_1900_: *mut leanh::LeanObject,
    mut v_h__2_1901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1899_) == 0 {
        let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1900_);
        v___x_1902_ = leanh::lean_box(0);
        v___x_1903_ = leanh::lean_apply_1(v_h__2_1901_, v___x_1902_);
        return v___x_1903_;
    } else {
        let mut v_val_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1901_);
        v_val_1904_ = leanh::lean_ctor_get(v_x_1899_, 0);
        leanh::lean_inc(v_val_1904_);
        leanh::lean_dec_ref_known(v_x_1899_, 1);
        v___x_1905_ = leanh::lean_apply_1(v_h__1_1900_, v_val_1904_);
        return v___x_1905_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter(
    mut v_00_u03b1_1906_: *mut leanh::LeanObject,
    mut v_00_u03b2_1907_: *mut leanh::LeanObject,
    mut v_motive_1908_: *mut leanh::LeanObject,
    mut v_x_1909_: *mut leanh::LeanObject,
    mut v_h__1_1910_: *mut leanh::LeanObject,
    mut v_h__2_1911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1909_) == 0 {
        let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1910_);
        v___x_1912_ = leanh::lean_box(0);
        v___x_1913_ = leanh::lean_apply_1(v_h__2_1911_, v___x_1912_);
        return v___x_1913_;
    } else {
        let mut v_val_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1911_);
        v_val_1914_ = leanh::lean_ctor_get(v_x_1909_, 0);
        leanh::lean_inc(v_val_1914_);
        leanh::lean_dec_ref_known(v_x_1909_, 1);
        v___x_1915_ = leanh::lean_apply_1(v_h__1_1910_, v_val_1914_);
        return v___x_1915_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter___redArg(
    mut v_x_1916_: *mut leanh::LeanObject,
    mut v_h__1_1917_: *mut leanh::LeanObject,
    mut v_h__2_1918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1916_) == 0 {
        let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1917_);
        v___x_1919_ = leanh::lean_box(0);
        v___x_1920_ = leanh::lean_apply_1(v_h__2_1918_, v___x_1919_);
        return v___x_1920_;
    } else {
        let mut v_val_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1918_);
        v_val_1921_ = leanh::lean_ctor_get(v_x_1916_, 0);
        leanh::lean_inc(v_val_1921_);
        leanh::lean_dec_ref_known(v_x_1916_, 1);
        v___x_1922_ = leanh::lean_apply_1(v_h__1_1917_, v_val_1921_);
        return v___x_1922_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter(
    mut v_00_u03b1_1923_: *mut leanh::LeanObject,
    mut v_motive_1924_: *mut leanh::LeanObject,
    mut v_x_1925_: *mut leanh::LeanObject,
    mut v_h__1_1926_: *mut leanh::LeanObject,
    mut v_h__2_1927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1925_) == 0 {
        let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1926_);
        v___x_1928_ = leanh::lean_box(0);
        v___x_1929_ = leanh::lean_apply_1(v_h__2_1927_, v___x_1928_);
        return v___x_1929_;
    } else {
        let mut v_val_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1927_);
        v_val_1930_ = leanh::lean_ctor_get(v_x_1925_, 0);
        leanh::lean_inc(v_val_1930_);
        leanh::lean_dec_ref_known(v_x_1925_, 1);
        v___x_1931_ = leanh::lean_apply_1(v_h__1_1926_, v_val_1930_);
        return v___x_1931_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_1932_: *mut leanh::LeanObject,
    mut v_h__1_1933_: *mut leanh::LeanObject,
    mut v_h__2_1934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1932_) == 0 {
        let mut v_a_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1934_);
        v_a_1935_ = leanh::lean_ctor_get(v_x_1932_, 0);
        leanh::lean_inc(v_a_1935_);
        leanh::lean_dec_ref_known(v_x_1932_, 1);
        v___x_1936_ = leanh::lean_apply_1(v_h__1_1933_, v_a_1935_);
        return v___x_1936_;
    } else {
        let mut v_a_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1933_);
        v_a_1937_ = leanh::lean_ctor_get(v_x_1932_, 0);
        leanh::lean_inc(v_a_1937_);
        leanh::lean_dec_ref_known(v_x_1932_, 1);
        v___x_1938_ = leanh::lean_apply_1(v_h__2_1934_, v_a_1937_);
        return v___x_1938_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_1939_: *mut leanh::LeanObject,
    mut v_motive_1940_: *mut leanh::LeanObject,
    mut v_x_1941_: *mut leanh::LeanObject,
    mut v_h__1_1942_: *mut leanh::LeanObject,
    mut v_h__2_1943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1941_) == 0 {
        let mut v_a_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1943_);
        v_a_1944_ = leanh::lean_ctor_get(v_x_1941_, 0);
        leanh::lean_inc(v_a_1944_);
        leanh::lean_dec_ref_known(v_x_1941_, 1);
        v___x_1945_ = leanh::lean_apply_1(v_h__1_1942_, v_a_1944_);
        return v___x_1945_;
    } else {
        let mut v_a_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1942_);
        v_a_1946_ = leanh::lean_ctor_get(v_x_1941_, 0);
        leanh::lean_inc(v_a_1946_);
        leanh::lean_dec_ref_known(v_x_1941_, 1);
        v___x_1947_ = leanh::lean_apply_1(v_h__2_1943_, v_a_1946_);
        return v___x_1947_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(
    mut v_x_1948_: *mut leanh::LeanObject,
    mut v_h__1_1949_: *mut leanh::LeanObject,
    mut v_h__2_1950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1948_) == 0 {
        let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1949_);
        v___x_1951_ = leanh::lean_box(0);
        v___x_1952_ = leanh::lean_apply_1(v_h__2_1950_, v___x_1951_);
        return v___x_1952_;
    } else {
        let mut v_val_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1950_);
        v_val_1953_ = leanh::lean_ctor_get(v_x_1948_, 0);
        leanh::lean_inc(v_val_1953_);
        leanh::lean_dec_ref_known(v_x_1948_, 1);
        v___x_1954_ = leanh::lean_apply_1(v_h__1_1949_, v_val_1953_);
        return v___x_1954_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter(
    mut v_00_u03b1_1955_: *mut leanh::LeanObject,
    mut v_00_u03b2_1956_: *mut leanh::LeanObject,
    mut v_motive_1957_: *mut leanh::LeanObject,
    mut v_x_1958_: *mut leanh::LeanObject,
    mut v_h__1_1959_: *mut leanh::LeanObject,
    mut v_h__2_1960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1958_) == 0 {
        let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1959_);
        v___x_1961_ = leanh::lean_box(0);
        v___x_1962_ = leanh::lean_apply_1(v_h__2_1960_, v___x_1961_);
        return v___x_1962_;
    } else {
        let mut v_val_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1960_);
        v_val_1963_ = leanh::lean_ctor_get(v_x_1958_, 0);
        leanh::lean_inc(v_val_1963_);
        leanh::lean_dec_ref_known(v_x_1958_, 1);
        v___x_1964_ = leanh::lean_apply_1(v_h__1_1959_, v_val_1963_);
        return v___x_1964_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(
    mut v_x_1965_: u8,
    mut v_h__1_1966_: *mut leanh::LeanObject,
    mut v_h__2_1967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1965_ == 0 {
        let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1966_);
        v___x_1968_ = leanh::lean_box(0);
        v___x_1969_ = leanh::lean_apply_1(v_h__2_1967_, v___x_1968_);
        return v___x_1969_;
    } else {
        let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1967_);
        v___x_1970_ = leanh::lean_box(0);
        v___x_1971_ = leanh::lean_apply_1(v_h__1_1966_, v___x_1970_);
        return v___x_1971_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_1972_: *mut leanh::LeanObject,
    mut v_h__1_1973_: *mut leanh::LeanObject,
    mut v_h__2_1974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_26__boxed_1975_: u8 = 0;
    let mut v_res_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1975_ = (leanh::lean_unbox(v_x_1972_) as u8);
    v_res_1976_ =
        l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(
            v_x_26__boxed_1975_,
            v_h__1_1973_,
            v_h__2_1974_,
        );
    return v_res_1976_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter(
    mut v_motive_1977_: *mut leanh::LeanObject,
    mut v_x_1978_: u8,
    mut v_h__1_1979_: *mut leanh::LeanObject,
    mut v_h__2_1980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1978_ == 0 {
        let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1979_);
        v___x_1981_ = leanh::lean_box(0);
        v___x_1982_ = leanh::lean_apply_1(v_h__2_1980_, v___x_1981_);
        return v___x_1982_;
    } else {
        let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1980_);
        v___x_1983_ = leanh::lean_box(0);
        v___x_1984_ = leanh::lean_apply_1(v_h__1_1979_, v___x_1983_);
        return v___x_1984_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___boxed(
    mut v_motive_1985_: *mut leanh::LeanObject,
    mut v_x_1986_: *mut leanh::LeanObject,
    mut v_h__1_1987_: *mut leanh::LeanObject,
    mut v_h__2_1988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_37__boxed_1989_: u8 = 0;
    let mut v_res_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_1989_ = (leanh::lean_unbox(v_x_1986_) as u8);
    v_res_1990_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter(
        v_motive_1985_,
        v_x_37__boxed_1989_,
        v_h__1_1987_,
        v_h__2_1988_,
    );
    return v_res_1990_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Model(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Impl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(
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
pub unsafe fn initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Internal_Model(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Internal_List_Associative(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Impl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Subtype_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(builtin);
}