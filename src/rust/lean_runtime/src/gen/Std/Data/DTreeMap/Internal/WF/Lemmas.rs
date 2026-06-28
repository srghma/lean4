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
    mut v_00_u03b1_996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_997_ = crate::leanh::lean_box(0);
    return v___x_997_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter___redArg(
    mut v_l_998_: *mut crate::leanh::LeanObject,
    mut v_h__1_999_: *mut crate::leanh::LeanObject,
    mut v_h__2_1000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_998_) == 0 {
        let mut v_size_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_999_);
        v_size_1001_ = crate::leanh::lean_ctor_get(v_l_998_, 0);
        crate::leanh::lean_inc(v_size_1001_);
        v_k_1002_ = crate::leanh::lean_ctor_get(v_l_998_, 1);
        crate::leanh::lean_inc(v_k_1002_);
        v_v_1003_ = crate::leanh::lean_ctor_get(v_l_998_, 2);
        crate::leanh::lean_inc(v_v_1003_);
        v_l_1004_ = crate::leanh::lean_ctor_get(v_l_998_, 3);
        crate::leanh::lean_inc(v_l_1004_);
        v_r_1005_ = crate::leanh::lean_ctor_get(v_l_998_, 4);
        crate::leanh::lean_inc(v_r_1005_);
        crate::leanh::lean_dec_ref_known(v_l_998_, 5);
        v___x_1006_ = crate::leanh::lean_apply_5(
            v_h__2_1000_,
            v_size_1001_,
            v_k_1002_,
            v_v_1003_,
            v_l_1004_,
            v_r_1005_,
        );
        return v___x_1006_;
    } else {
        let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1000_);
        v___x_1007_ = crate::leanh::lean_box(0);
        v___x_1008_ = crate::leanh::lean_apply_1(v_h__1_999_, v___x_1007_);
        return v___x_1008_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter(
    mut v_00_u03b1_1009_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1010_: *mut crate::leanh::LeanObject,
    mut v_motive_1011_: *mut crate::leanh::LeanObject,
    mut v_l_1012_: *mut crate::leanh::LeanObject,
    mut v_h__1_1013_: *mut crate::leanh::LeanObject,
    mut v_h__2_1014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_1012_) == 0 {
        let mut v_size_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1013_);
        v_size_1015_ = crate::leanh::lean_ctor_get(v_l_1012_, 0);
        crate::leanh::lean_inc(v_size_1015_);
        v_k_1016_ = crate::leanh::lean_ctor_get(v_l_1012_, 1);
        crate::leanh::lean_inc(v_k_1016_);
        v_v_1017_ = crate::leanh::lean_ctor_get(v_l_1012_, 2);
        crate::leanh::lean_inc(v_v_1017_);
        v_l_1018_ = crate::leanh::lean_ctor_get(v_l_1012_, 3);
        crate::leanh::lean_inc(v_l_1018_);
        v_r_1019_ = crate::leanh::lean_ctor_get(v_l_1012_, 4);
        crate::leanh::lean_inc(v_r_1019_);
        crate::leanh::lean_dec_ref_known(v_l_1012_, 5);
        v___x_1020_ = crate::leanh::lean_apply_5(
            v_h__2_1014_,
            v_size_1015_,
            v_k_1016_,
            v_v_1017_,
            v_l_1018_,
            v_r_1019_,
        );
        return v___x_1020_;
    } else {
        let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1014_);
        v___x_1021_ = crate::leanh::lean_box(0);
        v___x_1022_ = crate::leanh::lean_apply_1(v_h__1_1013_, v___x_1021_);
        return v___x_1022_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___redArg(
    mut v_r_1023_: *mut crate::leanh::LeanObject,
    mut v_h__1_1024_: *mut crate::leanh::LeanObject,
    mut v_h__2_1025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_1023_) == 0 {
        let mut v_size_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1024_);
        v_size_1026_ = crate::leanh::lean_ctor_get(v_r_1023_, 0);
        crate::leanh::lean_inc(v_size_1026_);
        v_k_1027_ = crate::leanh::lean_ctor_get(v_r_1023_, 1);
        crate::leanh::lean_inc(v_k_1027_);
        v_v_1028_ = crate::leanh::lean_ctor_get(v_r_1023_, 2);
        crate::leanh::lean_inc(v_v_1028_);
        v_l_1029_ = crate::leanh::lean_ctor_get(v_r_1023_, 3);
        crate::leanh::lean_inc(v_l_1029_);
        v_r_1030_ = crate::leanh::lean_ctor_get(v_r_1023_, 4);
        crate::leanh::lean_inc(v_r_1030_);
        crate::leanh::lean_dec_ref_known(v_r_1023_, 5);
        v___x_1031_ = crate::leanh::lean_apply_6(
            v_h__2_1025_,
            v_size_1026_,
            v_k_1027_,
            v_v_1028_,
            v_l_1029_,
            v_r_1030_,
            crate::leanh::lean_box(0),
        );
        return v___x_1031_;
    } else {
        let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1025_);
        v___x_1032_ = crate::leanh::lean_apply_1(v_h__1_1024_, crate::leanh::lean_box(0));
        return v___x_1032_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(
    mut v_00_u03b1_1033_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1034_: *mut crate::leanh::LeanObject,
    mut v_l_1035_: *mut crate::leanh::LeanObject,
    mut v_motive_1036_: *mut crate::leanh::LeanObject,
    mut v_r_1037_: *mut crate::leanh::LeanObject,
    mut v_h_1038_: *mut crate::leanh::LeanObject,
    mut v_h__1_1039_: *mut crate::leanh::LeanObject,
    mut v_h__2_1040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_1037_) == 0 {
        let mut v_size_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1039_);
        v_size_1041_ = crate::leanh::lean_ctor_get(v_r_1037_, 0);
        crate::leanh::lean_inc(v_size_1041_);
        v_k_1042_ = crate::leanh::lean_ctor_get(v_r_1037_, 1);
        crate::leanh::lean_inc(v_k_1042_);
        v_v_1043_ = crate::leanh::lean_ctor_get(v_r_1037_, 2);
        crate::leanh::lean_inc(v_v_1043_);
        v_l_1044_ = crate::leanh::lean_ctor_get(v_r_1037_, 3);
        crate::leanh::lean_inc(v_l_1044_);
        v_r_1045_ = crate::leanh::lean_ctor_get(v_r_1037_, 4);
        crate::leanh::lean_inc(v_r_1045_);
        crate::leanh::lean_dec_ref_known(v_r_1037_, 5);
        v___x_1046_ = crate::leanh::lean_apply_6(
            v_h__2_1040_,
            v_size_1041_,
            v_k_1042_,
            v_v_1043_,
            v_l_1044_,
            v_r_1045_,
            crate::leanh::lean_box(0),
        );
        return v___x_1046_;
    } else {
        let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1040_);
        v___x_1047_ = crate::leanh::lean_apply_1(v_h__1_1039_, crate::leanh::lean_box(0));
        return v___x_1047_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___boxed(
    mut v_00_u03b1_1048_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1049_: *mut crate::leanh::LeanObject,
    mut v_l_1050_: *mut crate::leanh::LeanObject,
    mut v_motive_1051_: *mut crate::leanh::LeanObject,
    mut v_r_1052_: *mut crate::leanh::LeanObject,
    mut v_h_1053_: *mut crate::leanh::LeanObject,
    mut v_h__1_1054_: *mut crate::leanh::LeanObject,
    mut v_h__2_1055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1056_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(v_00_u03b1_1048_, v_00_u03b2_1049_, v_l_1050_, v_motive_1051_, v_r_1052_, v_h_1053_, v_h__1_1054_, v_h__2_1055_);
    crate::leanh::lean_dec(v_l_1050_);
    return v_res_1056_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___redArg(
    mut v_l_1057_: *mut crate::leanh::LeanObject,
    mut v_h__1_1058_: *mut crate::leanh::LeanObject,
    mut v_h__2_1059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_1057_) == 0 {
        let mut v_size_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1058_);
        v_size_1060_ = crate::leanh::lean_ctor_get(v_l_1057_, 0);
        crate::leanh::lean_inc(v_size_1060_);
        v_k_1061_ = crate::leanh::lean_ctor_get(v_l_1057_, 1);
        crate::leanh::lean_inc(v_k_1061_);
        v_v_1062_ = crate::leanh::lean_ctor_get(v_l_1057_, 2);
        crate::leanh::lean_inc(v_v_1062_);
        v_l_1063_ = crate::leanh::lean_ctor_get(v_l_1057_, 3);
        crate::leanh::lean_inc(v_l_1063_);
        v_r_1064_ = crate::leanh::lean_ctor_get(v_l_1057_, 4);
        crate::leanh::lean_inc(v_r_1064_);
        crate::leanh::lean_dec_ref_known(v_l_1057_, 5);
        v___x_1065_ = crate::leanh::lean_apply_7(
            v_h__2_1059_,
            v_size_1060_,
            v_k_1061_,
            v_v_1062_,
            v_l_1063_,
            v_r_1064_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1065_;
    } else {
        let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1059_);
        v___x_1066_ = crate::leanh::lean_apply_2(
            v_h__1_1058_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1066_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(
    mut v_00_u03b1_1067_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1068_: *mut crate::leanh::LeanObject,
    mut v_r_1069_: *mut crate::leanh::LeanObject,
    mut v_motive_1070_: *mut crate::leanh::LeanObject,
    mut v_l_1071_: *mut crate::leanh::LeanObject,
    mut v_h_1072_: *mut crate::leanh::LeanObject,
    mut v_h_1073_: *mut crate::leanh::LeanObject,
    mut v_h__1_1074_: *mut crate::leanh::LeanObject,
    mut v_h__2_1075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_1071_) == 0 {
        let mut v_size_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1074_);
        v_size_1076_ = crate::leanh::lean_ctor_get(v_l_1071_, 0);
        crate::leanh::lean_inc(v_size_1076_);
        v_k_1077_ = crate::leanh::lean_ctor_get(v_l_1071_, 1);
        crate::leanh::lean_inc(v_k_1077_);
        v_v_1078_ = crate::leanh::lean_ctor_get(v_l_1071_, 2);
        crate::leanh::lean_inc(v_v_1078_);
        v_l_1079_ = crate::leanh::lean_ctor_get(v_l_1071_, 3);
        crate::leanh::lean_inc(v_l_1079_);
        v_r_1080_ = crate::leanh::lean_ctor_get(v_l_1071_, 4);
        crate::leanh::lean_inc(v_r_1080_);
        crate::leanh::lean_dec_ref_known(v_l_1071_, 5);
        v___x_1081_ = crate::leanh::lean_apply_7(
            v_h__2_1075_,
            v_size_1076_,
            v_k_1077_,
            v_v_1078_,
            v_l_1079_,
            v_r_1080_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1081_;
    } else {
        let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1075_);
        v___x_1082_ = crate::leanh::lean_apply_2(
            v_h__1_1074_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1082_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___boxed(
    mut v_00_u03b1_1083_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1084_: *mut crate::leanh::LeanObject,
    mut v_r_1085_: *mut crate::leanh::LeanObject,
    mut v_motive_1086_: *mut crate::leanh::LeanObject,
    mut v_l_1087_: *mut crate::leanh::LeanObject,
    mut v_h_1088_: *mut crate::leanh::LeanObject,
    mut v_h_1089_: *mut crate::leanh::LeanObject,
    mut v_h__1_1090_: *mut crate::leanh::LeanObject,
    mut v_h__2_1091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1092_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(v_00_u03b1_1083_, v_00_u03b2_1084_, v_r_1085_, v_motive_1086_, v_l_1087_, v_h_1088_, v_h_1089_, v_h__1_1090_, v_h__2_1091_);
    crate::leanh::lean_dec(v_r_1085_);
    return v_res_1092_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(
    mut v_r_1093_: *mut crate::leanh::LeanObject,
    mut v_h__1_1094_: *mut crate::leanh::LeanObject,
    mut v_h__2_1095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_1093_) == 0 {
        let mut v_size_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1094_);
        v_size_1096_ = crate::leanh::lean_ctor_get(v_r_1093_, 0);
        crate::leanh::lean_inc(v_size_1096_);
        v_k_1097_ = crate::leanh::lean_ctor_get(v_r_1093_, 1);
        crate::leanh::lean_inc(v_k_1097_);
        v_v_1098_ = crate::leanh::lean_ctor_get(v_r_1093_, 2);
        crate::leanh::lean_inc(v_v_1098_);
        v_l_1099_ = crate::leanh::lean_ctor_get(v_r_1093_, 3);
        crate::leanh::lean_inc(v_l_1099_);
        v_r_1100_ = crate::leanh::lean_ctor_get(v_r_1093_, 4);
        crate::leanh::lean_inc(v_r_1100_);
        crate::leanh::lean_dec_ref_known(v_r_1093_, 5);
        v___x_1101_ = crate::leanh::lean_apply_7(
            v_h__2_1095_,
            v_size_1096_,
            v_k_1097_,
            v_v_1098_,
            v_l_1099_,
            v_r_1100_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1101_;
    } else {
        let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1095_);
        v___x_1102_ = crate::leanh::lean_apply_2(
            v_h__1_1094_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1102_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(
    mut v_00_u03b1_1103_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1104_: *mut crate::leanh::LeanObject,
    mut v_motive_1105_: *mut crate::leanh::LeanObject,
    mut v_r_1106_: *mut crate::leanh::LeanObject,
    mut v_hr_1107_: *mut crate::leanh::LeanObject,
    mut v_h__1_1108_: *mut crate::leanh::LeanObject,
    mut v_h__2_1109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_1106_) == 0 {
        let mut v_size_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1108_);
        v_size_1110_ = crate::leanh::lean_ctor_get(v_r_1106_, 0);
        crate::leanh::lean_inc(v_size_1110_);
        v_k_1111_ = crate::leanh::lean_ctor_get(v_r_1106_, 1);
        crate::leanh::lean_inc(v_k_1111_);
        v_v_1112_ = crate::leanh::lean_ctor_get(v_r_1106_, 2);
        crate::leanh::lean_inc(v_v_1112_);
        v_l_1113_ = crate::leanh::lean_ctor_get(v_r_1106_, 3);
        crate::leanh::lean_inc(v_l_1113_);
        v_r_1114_ = crate::leanh::lean_ctor_get(v_r_1106_, 4);
        crate::leanh::lean_inc(v_r_1114_);
        crate::leanh::lean_dec_ref_known(v_r_1106_, 5);
        v___x_1115_ = crate::leanh::lean_apply_7(
            v_h__2_1109_,
            v_size_1110_,
            v_k_1111_,
            v_v_1112_,
            v_l_1113_,
            v_r_1114_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1115_;
    } else {
        let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1109_);
        v___x_1116_ = crate::leanh::lean_apply_2(
            v_h__1_1108_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1116_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___redArg(
    mut v_x_1117_: *mut crate::leanh::LeanObject,
    mut v_h__1_1118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1119_ = crate::leanh::lean_apply_3(
        v_h__1_1118_,
        v_x_1117_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1119_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(
    mut v_00_u03b1_1120_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1121_: *mut crate::leanh::LeanObject,
    mut v_l_1122_: *mut crate::leanh::LeanObject,
    mut v_l_x27_x27_1123_: *mut crate::leanh::LeanObject,
    mut v_motive_1124_: *mut crate::leanh::LeanObject,
    mut v_x_1125_: *mut crate::leanh::LeanObject,
    mut v_h__1_1126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1127_ = crate::leanh::lean_apply_3(
        v_h__1_1126_,
        v_x_1125_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1127_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___boxed(
    mut v_00_u03b1_1128_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1129_: *mut crate::leanh::LeanObject,
    mut v_l_1130_: *mut crate::leanh::LeanObject,
    mut v_l_x27_x27_1131_: *mut crate::leanh::LeanObject,
    mut v_motive_1132_: *mut crate::leanh::LeanObject,
    mut v_x_1133_: *mut crate::leanh::LeanObject,
    mut v_h__1_1134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1135_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(v_00_u03b1_1128_, v_00_u03b2_1129_, v_l_1130_, v_l_x27_x27_1131_, v_motive_1132_, v_x_1133_, v_h__1_1134_);
    crate::leanh::lean_dec(v_l_x27_x27_1131_);
    crate::leanh::lean_dec(v_l_1130_);
    return v_res_1135_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___redArg(
    mut v_x_1136_: *mut crate::leanh::LeanObject,
    mut v_h__1_1137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1138_ = crate::leanh::lean_apply_3(
        v_h__1_1137_,
        v_x_1136_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1138_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(
    mut v_00_u03b1_1139_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1140_: *mut crate::leanh::LeanObject,
    mut v_r_1141_: *mut crate::leanh::LeanObject,
    mut v_r_x27_1142_: *mut crate::leanh::LeanObject,
    mut v_motive_1143_: *mut crate::leanh::LeanObject,
    mut v_x_1144_: *mut crate::leanh::LeanObject,
    mut v_h__1_1145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1146_ = crate::leanh::lean_apply_3(
        v_h__1_1145_,
        v_x_1144_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1146_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___boxed(
    mut v_00_u03b1_1147_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1148_: *mut crate::leanh::LeanObject,
    mut v_r_1149_: *mut crate::leanh::LeanObject,
    mut v_r_x27_1150_: *mut crate::leanh::LeanObject,
    mut v_motive_1151_: *mut crate::leanh::LeanObject,
    mut v_x_1152_: *mut crate::leanh::LeanObject,
    mut v_h__1_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(v_00_u03b1_1147_, v_00_u03b2_1148_, v_r_1149_, v_r_x27_1150_, v_motive_1151_, v_x_1152_, v_h__1_1153_);
    crate::leanh::lean_dec(v_r_x27_1150_);
    crate::leanh::lean_dec(v_r_1149_);
    return v_res_1154_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(
    mut v_t_1155_: *mut crate::leanh::LeanObject,
    mut v_h__1_1156_: *mut crate::leanh::LeanObject,
    mut v_h__2_1157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1155_) == 0 {
        let mut v_size_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1156_);
        v_size_1158_ = crate::leanh::lean_ctor_get(v_t_1155_, 0);
        crate::leanh::lean_inc(v_size_1158_);
        v_k_1159_ = crate::leanh::lean_ctor_get(v_t_1155_, 1);
        crate::leanh::lean_inc(v_k_1159_);
        v_v_1160_ = crate::leanh::lean_ctor_get(v_t_1155_, 2);
        crate::leanh::lean_inc(v_v_1160_);
        v_l_1161_ = crate::leanh::lean_ctor_get(v_t_1155_, 3);
        crate::leanh::lean_inc(v_l_1161_);
        v_r_1162_ = crate::leanh::lean_ctor_get(v_t_1155_, 4);
        crate::leanh::lean_inc(v_r_1162_);
        crate::leanh::lean_dec_ref_known(v_t_1155_, 5);
        v___x_1163_ = crate::leanh::lean_apply_6(
            v_h__2_1157_,
            v_size_1158_,
            v_k_1159_,
            v_v_1160_,
            v_l_1161_,
            v_r_1162_,
            crate::leanh::lean_box(0),
        );
        return v___x_1163_;
    } else {
        let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1157_);
        v___x_1164_ = crate::leanh::lean_apply_1(v_h__1_1156_, crate::leanh::lean_box(0));
        return v___x_1164_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(
    mut v_00_u03b1_1165_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1166_: *mut crate::leanh::LeanObject,
    mut v_motive_1167_: *mut crate::leanh::LeanObject,
    mut v_t_1168_: *mut crate::leanh::LeanObject,
    mut v_hr_1169_: *mut crate::leanh::LeanObject,
    mut v_h__1_1170_: *mut crate::leanh::LeanObject,
    mut v_h__2_1171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1168_) == 0 {
        let mut v_size_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1170_);
        v_size_1172_ = crate::leanh::lean_ctor_get(v_t_1168_, 0);
        crate::leanh::lean_inc(v_size_1172_);
        v_k_1173_ = crate::leanh::lean_ctor_get(v_t_1168_, 1);
        crate::leanh::lean_inc(v_k_1173_);
        v_v_1174_ = crate::leanh::lean_ctor_get(v_t_1168_, 2);
        crate::leanh::lean_inc(v_v_1174_);
        v_l_1175_ = crate::leanh::lean_ctor_get(v_t_1168_, 3);
        crate::leanh::lean_inc(v_l_1175_);
        v_r_1176_ = crate::leanh::lean_ctor_get(v_t_1168_, 4);
        crate::leanh::lean_inc(v_r_1176_);
        crate::leanh::lean_dec_ref_known(v_t_1168_, 5);
        v___x_1177_ = crate::leanh::lean_apply_6(
            v_h__2_1171_,
            v_size_1172_,
            v_k_1173_,
            v_v_1174_,
            v_l_1175_,
            v_r_1176_,
            crate::leanh::lean_box(0),
        );
        return v___x_1177_;
    } else {
        let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1171_);
        v___x_1178_ = crate::leanh::lean_apply_1(v_h__1_1170_, crate::leanh::lean_box(0));
        return v___x_1178_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___redArg(
    mut v_x_1179_: *mut crate::leanh::LeanObject,
    mut v_h__1_1180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1181_ = crate::leanh::lean_apply_3(
        v_h__1_1180_,
        v_x_1179_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1181_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(
    mut v_00_u03b1_1182_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1183_: *mut crate::leanh::LeanObject,
    mut v_szl_1184_: *mut crate::leanh::LeanObject,
    mut v_k_x27_1185_: *mut crate::leanh::LeanObject,
    mut v_v_x27_1186_: *mut crate::leanh::LeanObject,
    mut v_l_x27_1187_: *mut crate::leanh::LeanObject,
    mut v_r_x27_1188_: *mut crate::leanh::LeanObject,
    mut v_l_x27_x27_1189_: *mut crate::leanh::LeanObject,
    mut v_motive_1190_: *mut crate::leanh::LeanObject,
    mut v_x_1191_: *mut crate::leanh::LeanObject,
    mut v_h__1_1192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1193_ = crate::leanh::lean_apply_3(
        v_h__1_1192_,
        v_x_1191_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1193_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___boxed(
    mut v_00_u03b1_1194_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1195_: *mut crate::leanh::LeanObject,
    mut v_szl_1196_: *mut crate::leanh::LeanObject,
    mut v_k_x27_1197_: *mut crate::leanh::LeanObject,
    mut v_v_x27_1198_: *mut crate::leanh::LeanObject,
    mut v_l_x27_1199_: *mut crate::leanh::LeanObject,
    mut v_r_x27_1200_: *mut crate::leanh::LeanObject,
    mut v_l_x27_x27_1201_: *mut crate::leanh::LeanObject,
    mut v_motive_1202_: *mut crate::leanh::LeanObject,
    mut v_x_1203_: *mut crate::leanh::LeanObject,
    mut v_h__1_1204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1205_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(v_00_u03b1_1194_, v_00_u03b2_1195_, v_szl_1196_, v_k_x27_1197_, v_v_x27_1198_, v_l_x27_1199_, v_r_x27_1200_, v_l_x27_x27_1201_, v_motive_1202_, v_x_1203_, v_h__1_1204_);
    crate::leanh::lean_dec(v_l_x27_x27_1201_);
    crate::leanh::lean_dec(v_r_x27_1200_);
    crate::leanh::lean_dec(v_l_x27_1199_);
    crate::leanh::lean_dec(v_v_x27_1198_);
    crate::leanh::lean_dec(v_k_x27_1197_);
    crate::leanh::lean_dec(v_szl_1196_);
    return v_res_1205_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___redArg(
    mut v_x_1206_: *mut crate::leanh::LeanObject,
    mut v_h__1_1207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1208_ = crate::leanh::lean_apply_3(
        v_h__1_1207_,
        v_x_1206_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1208_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(
    mut v_00_u03b1_1209_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1210_: *mut crate::leanh::LeanObject,
    mut v_r_x27_1211_: *mut crate::leanh::LeanObject,
    mut v_szr_1212_: *mut crate::leanh::LeanObject,
    mut v_k_x27_x27_1213_: *mut crate::leanh::LeanObject,
    mut v_v_x27_x27_1214_: *mut crate::leanh::LeanObject,
    mut v_l_x27_x27_1215_: *mut crate::leanh::LeanObject,
    mut v_r_x27_x27_1216_: *mut crate::leanh::LeanObject,
    mut v_motive_1217_: *mut crate::leanh::LeanObject,
    mut v_x_1218_: *mut crate::leanh::LeanObject,
    mut v_h__1_1219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1220_ = crate::leanh::lean_apply_3(
        v_h__1_1219_,
        v_x_1218_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1220_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___boxed(
    mut v_00_u03b1_1221_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1222_: *mut crate::leanh::LeanObject,
    mut v_r_x27_1223_: *mut crate::leanh::LeanObject,
    mut v_szr_1224_: *mut crate::leanh::LeanObject,
    mut v_k_x27_x27_1225_: *mut crate::leanh::LeanObject,
    mut v_v_x27_x27_1226_: *mut crate::leanh::LeanObject,
    mut v_l_x27_x27_1227_: *mut crate::leanh::LeanObject,
    mut v_r_x27_x27_1228_: *mut crate::leanh::LeanObject,
    mut v_motive_1229_: *mut crate::leanh::LeanObject,
    mut v_x_1230_: *mut crate::leanh::LeanObject,
    mut v_h__1_1231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1232_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(v_00_u03b1_1221_, v_00_u03b2_1222_, v_r_x27_1223_, v_szr_1224_, v_k_x27_x27_1225_, v_v_x27_x27_1226_, v_l_x27_x27_1227_, v_r_x27_x27_1228_, v_motive_1229_, v_x_1230_, v_h__1_1231_);
    crate::leanh::lean_dec(v_r_x27_x27_1228_);
    crate::leanh::lean_dec(v_l_x27_x27_1227_);
    crate::leanh::lean_dec(v_v_x27_x27_1226_);
    crate::leanh::lean_dec(v_k_x27_x27_1225_);
    crate::leanh::lean_dec(v_szr_1224_);
    crate::leanh::lean_dec(v_r_x27_1223_);
    return v_res_1232_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(
    mut v_l_1233_: *mut crate::leanh::LeanObject,
    mut v_h__1_1234_: *mut crate::leanh::LeanObject,
    mut v_h__2_1235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_1233_) == 0 {
        let mut v_size_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1234_);
        v_size_1236_ = crate::leanh::lean_ctor_get(v_l_1233_, 0);
        crate::leanh::lean_inc(v_size_1236_);
        v_k_1237_ = crate::leanh::lean_ctor_get(v_l_1233_, 1);
        crate::leanh::lean_inc(v_k_1237_);
        v_v_1238_ = crate::leanh::lean_ctor_get(v_l_1233_, 2);
        crate::leanh::lean_inc(v_v_1238_);
        v_l_1239_ = crate::leanh::lean_ctor_get(v_l_1233_, 3);
        crate::leanh::lean_inc(v_l_1239_);
        v_r_1240_ = crate::leanh::lean_ctor_get(v_l_1233_, 4);
        crate::leanh::lean_inc(v_r_1240_);
        crate::leanh::lean_dec_ref_known(v_l_1233_, 5);
        v___x_1241_ = crate::leanh::lean_apply_6(
            v_h__2_1235_,
            v_size_1236_,
            v_k_1237_,
            v_v_1238_,
            v_l_1239_,
            v_r_1240_,
            crate::leanh::lean_box(0),
        );
        return v___x_1241_;
    } else {
        let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1235_);
        v___x_1242_ = crate::leanh::lean_apply_1(v_h__1_1234_, crate::leanh::lean_box(0));
        return v___x_1242_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(
    mut v_00_u03b1_1243_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1244_: *mut crate::leanh::LeanObject,
    mut v_motive_1245_: *mut crate::leanh::LeanObject,
    mut v_l_1246_: *mut crate::leanh::LeanObject,
    mut v_hl_1247_: *mut crate::leanh::LeanObject,
    mut v_h__1_1248_: *mut crate::leanh::LeanObject,
    mut v_h__2_1249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_1246_) == 0 {
        let mut v_size_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1248_);
        v_size_1250_ = crate::leanh::lean_ctor_get(v_l_1246_, 0);
        crate::leanh::lean_inc(v_size_1250_);
        v_k_1251_ = crate::leanh::lean_ctor_get(v_l_1246_, 1);
        crate::leanh::lean_inc(v_k_1251_);
        v_v_1252_ = crate::leanh::lean_ctor_get(v_l_1246_, 2);
        crate::leanh::lean_inc(v_v_1252_);
        v_l_1253_ = crate::leanh::lean_ctor_get(v_l_1246_, 3);
        crate::leanh::lean_inc(v_l_1253_);
        v_r_1254_ = crate::leanh::lean_ctor_get(v_l_1246_, 4);
        crate::leanh::lean_inc(v_r_1254_);
        crate::leanh::lean_dec_ref_known(v_l_1246_, 5);
        v___x_1255_ = crate::leanh::lean_apply_6(
            v_h__2_1249_,
            v_size_1250_,
            v_k_1251_,
            v_v_1252_,
            v_l_1253_,
            v_r_1254_,
            crate::leanh::lean_box(0),
        );
        return v___x_1255_;
    } else {
        let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1249_);
        v___x_1256_ = crate::leanh::lean_apply_1(v_h__1_1248_, crate::leanh::lean_box(0));
        return v___x_1256_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(
    mut v_x_1257_: *mut crate::leanh::LeanObject,
    mut v_h__1_1258_: *mut crate::leanh::LeanObject,
    mut v_h__2_1259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1257_) == 0 {
        let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1259_);
        v___x_1260_ = crate::leanh::lean_box(0);
        v___x_1261_ = crate::leanh::lean_apply_1(v_h__1_1258_, v___x_1260_);
        return v___x_1261_;
    } else {
        let mut v_val_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1258_);
        v_val_1262_ = crate::leanh::lean_ctor_get(v_x_1257_, 0);
        crate::leanh::lean_inc(v_val_1262_);
        crate::leanh::lean_dec_ref_known(v_x_1257_, 1);
        v_fst_1263_ = crate::leanh::lean_ctor_get(v_val_1262_, 0);
        crate::leanh::lean_inc(v_fst_1263_);
        v_snd_1264_ = crate::leanh::lean_ctor_get(v_val_1262_, 1);
        crate::leanh::lean_inc(v_snd_1264_);
        crate::leanh::lean_dec(v_val_1262_);
        v___x_1265_ = crate::leanh::lean_apply_2(v_h__2_1259_, v_fst_1263_, v_snd_1264_);
        return v___x_1265_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(
    mut v_00_u03b1_1266_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1267_: *mut crate::leanh::LeanObject,
    mut v_motive_1268_: *mut crate::leanh::LeanObject,
    mut v_x_1269_: *mut crate::leanh::LeanObject,
    mut v_h__1_1270_: *mut crate::leanh::LeanObject,
    mut v_h__2_1271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1269_) == 0 {
        let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1271_);
        v___x_1272_ = crate::leanh::lean_box(0);
        v___x_1273_ = crate::leanh::lean_apply_1(v_h__1_1270_, v___x_1272_);
        return v___x_1273_;
    } else {
        let mut v_val_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1270_);
        v_val_1274_ = crate::leanh::lean_ctor_get(v_x_1269_, 0);
        crate::leanh::lean_inc(v_val_1274_);
        crate::leanh::lean_dec_ref_known(v_x_1269_, 1);
        v_fst_1275_ = crate::leanh::lean_ctor_get(v_val_1274_, 0);
        crate::leanh::lean_inc(v_fst_1275_);
        v_snd_1276_ = crate::leanh::lean_ctor_get(v_val_1274_, 1);
        crate::leanh::lean_inc(v_snd_1276_);
        crate::leanh::lean_dec(v_val_1274_);
        v___x_1277_ = crate::leanh::lean_apply_2(v_h__2_1271_, v_fst_1275_, v_snd_1276_);
        return v___x_1277_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(
    mut v_x_1278_: u8,
    mut v_h__1_1279_: *mut crate::leanh::LeanObject,
    mut v_h__2_1280_: *mut crate::leanh::LeanObject,
    mut v_h__3_1281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_1278_ {
        0 => {
            let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1281_);
            crate::leanh::lean_dec(v_h__2_1280_);
            v___x_1282_ = crate::leanh::lean_apply_1(v_h__1_1279_, crate::leanh::lean_box(0));
            return v___x_1282_;
        }
        1 => {
            let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1281_);
            crate::leanh::lean_dec(v_h__1_1279_);
            v___x_1283_ = crate::leanh::lean_apply_1(v_h__2_1280_, crate::leanh::lean_box(0));
            return v___x_1283_;
        }
        _ => {
            let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1280_);
            crate::leanh::lean_dec(v_h__1_1279_);
            v___x_1284_ = crate::leanh::lean_apply_1(v_h__3_1281_, crate::leanh::lean_box(0));
            return v___x_1284_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(
    mut v_x_1285_: *mut crate::leanh::LeanObject,
    mut v_h__1_1286_: *mut crate::leanh::LeanObject,
    mut v_h__2_1287_: *mut crate::leanh::LeanObject,
    mut v_h__3_1288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_33__boxed_1289_: u8 = 0;
    let mut v_res_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_33__boxed_1289_ = (crate::leanh::lean_unbox(v_x_1285_) as u8);
    v_res_1290_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(v_x_33__boxed_1289_, v_h__1_1286_, v_h__2_1287_, v_h__3_1288_);
    return v_res_1290_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(
    mut v_motive_1291_: *mut crate::leanh::LeanObject,
    mut v_x_1292_: u8,
    mut v_h__1_1293_: *mut crate::leanh::LeanObject,
    mut v_h__2_1294_: *mut crate::leanh::LeanObject,
    mut v_h__3_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_1292_ {
        0 => {
            let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1295_);
            crate::leanh::lean_dec(v_h__2_1294_);
            v___x_1296_ = crate::leanh::lean_apply_1(v_h__1_1293_, crate::leanh::lean_box(0));
            return v___x_1296_;
        }
        1 => {
            let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1295_);
            crate::leanh::lean_dec(v_h__1_1293_);
            v___x_1297_ = crate::leanh::lean_apply_1(v_h__2_1294_, crate::leanh::lean_box(0));
            return v___x_1297_;
        }
        _ => {
            let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1294_);
            crate::leanh::lean_dec(v_h__1_1293_);
            v___x_1298_ = crate::leanh::lean_apply_1(v_h__3_1295_, crate::leanh::lean_box(0));
            return v___x_1298_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(
    mut v_motive_1299_: *mut crate::leanh::LeanObject,
    mut v_x_1300_: *mut crate::leanh::LeanObject,
    mut v_h__1_1301_: *mut crate::leanh::LeanObject,
    mut v_h__2_1302_: *mut crate::leanh::LeanObject,
    mut v_h__3_1303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_42__boxed_1304_: u8 = 0;
    let mut v_res_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_42__boxed_1304_ = (crate::leanh::lean_unbox(v_x_1300_) as u8);
    v_res_1305_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(v_motive_1299_, v_x_42__boxed_1304_, v_h__1_1301_, v_h__2_1302_, v_h__3_1303_);
    return v_res_1305_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___redArg(
    mut v_x_1306_: *mut crate::leanh::LeanObject,
    mut v_h__1_1307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1308_ = crate::leanh::lean_apply_4(
        v_h__1_1307_,
        v_x_1306_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1308_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(
    mut v_00_u03b1_1309_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1310_: *mut crate::leanh::LeanObject,
    mut v_l_1311_: *mut crate::leanh::LeanObject,
    mut v_motive_1312_: *mut crate::leanh::LeanObject,
    mut v_x_1313_: *mut crate::leanh::LeanObject,
    mut v_h__1_1314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1315_ = crate::leanh::lean_apply_4(
        v_h__1_1314_,
        v_x_1313_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1315_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___boxed(
    mut v_00_u03b1_1316_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1317_: *mut crate::leanh::LeanObject,
    mut v_l_1318_: *mut crate::leanh::LeanObject,
    mut v_motive_1319_: *mut crate::leanh::LeanObject,
    mut v_x_1320_: *mut crate::leanh::LeanObject,
    mut v_h__1_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1322_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(v_00_u03b1_1316_, v_00_u03b2_1317_, v_l_1318_, v_motive_1319_, v_x_1320_, v_h__1_1321_);
    crate::leanh::lean_dec(v_l_1318_);
    return v_res_1322_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(
    mut v_x_1323_: u8,
    mut v_h__1_1324_: *mut crate::leanh::LeanObject,
    mut v_h__2_1325_: *mut crate::leanh::LeanObject,
    mut v_h__3_1326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_1323_ {
        0 => {
            let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1326_);
            crate::leanh::lean_dec(v_h__2_1325_);
            v___x_1327_ = crate::leanh::lean_box(0);
            v___x_1328_ = crate::leanh::lean_apply_1(v_h__1_1324_, v___x_1327_);
            return v___x_1328_;
        }
        1 => {
            let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1325_);
            crate::leanh::lean_dec(v_h__1_1324_);
            v___x_1329_ = crate::leanh::lean_box(0);
            v___x_1330_ = crate::leanh::lean_apply_1(v_h__3_1326_, v___x_1329_);
            return v___x_1330_;
        }
        _ => {
            let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1326_);
            crate::leanh::lean_dec(v_h__1_1324_);
            v___x_1331_ = crate::leanh::lean_box(0);
            v___x_1332_ = crate::leanh::lean_apply_1(v_h__2_1325_, v___x_1331_);
            return v___x_1332_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg___boxed(
    mut v_x_1333_: *mut crate::leanh::LeanObject,
    mut v_h__1_1334_: *mut crate::leanh::LeanObject,
    mut v_h__2_1335_: *mut crate::leanh::LeanObject,
    mut v_h__3_1336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_36__boxed_1337_: u8 = 0;
    let mut v_res_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_1337_ = (crate::leanh::lean_unbox(v_x_1333_) as u8);
    v_res_1338_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_36__boxed_1337_, v_h__1_1334_, v_h__2_1335_, v_h__3_1336_);
    return v_res_1338_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(
    mut v_motive_1339_: *mut crate::leanh::LeanObject,
    mut v_x_1340_: u8,
    mut v_h__1_1341_: *mut crate::leanh::LeanObject,
    mut v_h__2_1342_: *mut crate::leanh::LeanObject,
    mut v_h__3_1343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_1340_ {
        0 => {
            let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1343_);
            crate::leanh::lean_dec(v_h__2_1342_);
            v___x_1344_ = crate::leanh::lean_box(0);
            v___x_1345_ = crate::leanh::lean_apply_1(v_h__1_1341_, v___x_1344_);
            return v___x_1345_;
        }
        1 => {
            let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1342_);
            crate::leanh::lean_dec(v_h__1_1341_);
            v___x_1346_ = crate::leanh::lean_box(0);
            v___x_1347_ = crate::leanh::lean_apply_1(v_h__3_1343_, v___x_1346_);
            return v___x_1347_;
        }
        _ => {
            let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1343_);
            crate::leanh::lean_dec(v_h__1_1341_);
            v___x_1348_ = crate::leanh::lean_box(0);
            v___x_1349_ = crate::leanh::lean_apply_1(v_h__2_1342_, v___x_1348_);
            return v___x_1349_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___boxed(
    mut v_motive_1350_: *mut crate::leanh::LeanObject,
    mut v_x_1351_: *mut crate::leanh::LeanObject,
    mut v_h__1_1352_: *mut crate::leanh::LeanObject,
    mut v_h__2_1353_: *mut crate::leanh::LeanObject,
    mut v_h__3_1354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_51__boxed_1355_: u8 = 0;
    let mut v_res_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_51__boxed_1355_ = (crate::leanh::lean_unbox(v_x_1351_) as u8);
    v_res_1356_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(v_motive_1350_, v_x_51__boxed_1355_, v_h__1_1352_, v_h__2_1353_, v_h__3_1354_);
    return v_res_1356_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(
    mut v_x_1357_: *mut crate::leanh::LeanObject,
    mut v_h__1_1358_: *mut crate::leanh::LeanObject,
    mut v_h__2_1359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1357_) == 0 {
        let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1359_);
        v___x_1360_ = crate::leanh::lean_apply_1(v_h__1_1358_, crate::leanh::lean_box(0));
        return v___x_1360_;
    } else {
        let mut v_val_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1358_);
        v_val_1361_ = crate::leanh::lean_ctor_get(v_x_1357_, 0);
        crate::leanh::lean_inc(v_val_1361_);
        crate::leanh::lean_dec_ref_known(v_x_1357_, 1);
        v___x_1362_ =
            crate::leanh::lean_apply_2(v_h__2_1359_, v_val_1361_, crate::leanh::lean_box(0));
        return v___x_1362_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(
    mut v_00_u03b1_1363_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1364_: *mut crate::leanh::LeanObject,
    mut v_motive_1365_: *mut crate::leanh::LeanObject,
    mut v_x_1366_: *mut crate::leanh::LeanObject,
    mut v_h__1_1367_: *mut crate::leanh::LeanObject,
    mut v_h__2_1368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1366_) == 0 {
        let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1368_);
        v___x_1369_ = crate::leanh::lean_apply_1(v_h__1_1367_, crate::leanh::lean_box(0));
        return v___x_1369_;
    } else {
        let mut v_val_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1367_);
        v_val_1370_ = crate::leanh::lean_ctor_get(v_x_1366_, 0);
        crate::leanh::lean_inc(v_val_1370_);
        crate::leanh::lean_dec_ref_known(v_x_1366_, 1);
        v___x_1371_ =
            crate::leanh::lean_apply_2(v_h__2_1368_, v_val_1370_, crate::leanh::lean_box(0));
        return v___x_1371_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(
    mut v_x_1372_: *mut crate::leanh::LeanObject,
    mut v_h__1_1373_: *mut crate::leanh::LeanObject,
    mut v_h__2_1374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1372_) == 0 {
        let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1374_);
        v___x_1375_ = crate::leanh::lean_box(0);
        v___x_1376_ = crate::leanh::lean_apply_1(v_h__1_1373_, v___x_1375_);
        return v___x_1376_;
    } else {
        let mut v_val_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1373_);
        v_val_1377_ = crate::leanh::lean_ctor_get(v_x_1372_, 0);
        crate::leanh::lean_inc(v_val_1377_);
        crate::leanh::lean_dec_ref_known(v_x_1372_, 1);
        v___x_1378_ = crate::leanh::lean_apply_1(v_h__2_1374_, v_val_1377_);
        return v___x_1378_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(
    mut v_00_u03b1_1379_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1380_: *mut crate::leanh::LeanObject,
    mut v_motive_1381_: *mut crate::leanh::LeanObject,
    mut v_x_1382_: *mut crate::leanh::LeanObject,
    mut v_h__1_1383_: *mut crate::leanh::LeanObject,
    mut v_h__2_1384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1382_) == 0 {
        let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1384_);
        v___x_1385_ = crate::leanh::lean_box(0);
        v___x_1386_ = crate::leanh::lean_apply_1(v_h__1_1383_, v___x_1385_);
        return v___x_1386_;
    } else {
        let mut v_val_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1383_);
        v_val_1387_ = crate::leanh::lean_ctor_get(v_x_1382_, 0);
        crate::leanh::lean_inc(v_val_1387_);
        crate::leanh::lean_dec_ref_known(v_x_1382_, 1);
        v___x_1388_ = crate::leanh::lean_apply_1(v_h__2_1384_, v_val_1387_);
        return v___x_1388_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(
    mut v_x_1389_: *mut crate::leanh::LeanObject,
    mut v_h__1_1390_: *mut crate::leanh::LeanObject,
    mut v_h__2_1391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1389_) == 0 {
        let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1391_);
        v___x_1392_ = crate::leanh::lean_box(0);
        v___x_1393_ = crate::leanh::lean_apply_1(v_h__1_1390_, v___x_1392_);
        return v___x_1393_;
    } else {
        let mut v_head_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1390_);
        v_head_1394_ = crate::leanh::lean_ctor_get(v_x_1389_, 0);
        crate::leanh::lean_inc(v_head_1394_);
        v_tail_1395_ = crate::leanh::lean_ctor_get(v_x_1389_, 1);
        crate::leanh::lean_inc(v_tail_1395_);
        crate::leanh::lean_dec_ref_known(v_x_1389_, 2);
        v_fst_1396_ = crate::leanh::lean_ctor_get(v_head_1394_, 0);
        crate::leanh::lean_inc(v_fst_1396_);
        v_snd_1397_ = crate::leanh::lean_ctor_get(v_head_1394_, 1);
        crate::leanh::lean_inc(v_snd_1397_);
        crate::leanh::lean_dec(v_head_1394_);
        v___x_1398_ =
            crate::leanh::lean_apply_3(v_h__2_1391_, v_fst_1396_, v_snd_1397_, v_tail_1395_);
        return v___x_1398_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_getEntry_x3f_match__1_splitter(
    mut v_00_u03b1_1399_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1400_: *mut crate::leanh::LeanObject,
    mut v_motive_1401_: *mut crate::leanh::LeanObject,
    mut v_x_1402_: *mut crate::leanh::LeanObject,
    mut v_h__1_1403_: *mut crate::leanh::LeanObject,
    mut v_h__2_1404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1402_) == 0 {
        let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1404_);
        v___x_1405_ = crate::leanh::lean_box(0);
        v___x_1406_ = crate::leanh::lean_apply_1(v_h__1_1403_, v___x_1405_);
        return v___x_1406_;
    } else {
        let mut v_head_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1403_);
        v_head_1407_ = crate::leanh::lean_ctor_get(v_x_1402_, 0);
        crate::leanh::lean_inc(v_head_1407_);
        v_tail_1408_ = crate::leanh::lean_ctor_get(v_x_1402_, 1);
        crate::leanh::lean_inc(v_tail_1408_);
        crate::leanh::lean_dec_ref_known(v_x_1402_, 2);
        v_fst_1409_ = crate::leanh::lean_ctor_get(v_head_1407_, 0);
        crate::leanh::lean_inc(v_fst_1409_);
        v_snd_1410_ = crate::leanh::lean_ctor_get(v_head_1407_, 1);
        crate::leanh::lean_inc(v_snd_1410_);
        crate::leanh::lean_dec(v_head_1407_);
        v___x_1411_ =
            crate::leanh::lean_apply_3(v_h__2_1404_, v_fst_1409_, v_snd_1410_, v_tail_1408_);
        return v___x_1411_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(
    mut v_x_1412_: *mut crate::leanh::LeanObject,
    mut v_h__1_1413_: *mut crate::leanh::LeanObject,
    mut v_h__2_1414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1412_) == 0 {
        let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1414_);
        v___x_1415_ = crate::leanh::lean_box(0);
        v___x_1416_ = crate::leanh::lean_apply_1(v_h__1_1413_, v___x_1415_);
        return v___x_1416_;
    } else {
        let mut v_val_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1413_);
        v_val_1417_ = crate::leanh::lean_ctor_get(v_x_1412_, 0);
        crate::leanh::lean_inc(v_val_1417_);
        crate::leanh::lean_dec_ref_known(v_x_1412_, 1);
        v___x_1418_ = crate::leanh::lean_apply_1(v_h__2_1414_, v_val_1417_);
        return v___x_1418_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(
    mut v_00_u03b1_1419_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1420_: *mut crate::leanh::LeanObject,
    mut v_motive_1421_: *mut crate::leanh::LeanObject,
    mut v_x_1422_: *mut crate::leanh::LeanObject,
    mut v_h__1_1423_: *mut crate::leanh::LeanObject,
    mut v_h__2_1424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1422_) == 0 {
        let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1424_);
        v___x_1425_ = crate::leanh::lean_box(0);
        v___x_1426_ = crate::leanh::lean_apply_1(v_h__1_1423_, v___x_1425_);
        return v___x_1426_;
    } else {
        let mut v_val_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1423_);
        v_val_1427_ = crate::leanh::lean_ctor_get(v_x_1422_, 0);
        crate::leanh::lean_inc(v_val_1427_);
        crate::leanh::lean_dec_ref_known(v_x_1422_, 1);
        v___x_1428_ = crate::leanh::lean_apply_1(v_h__2_1424_, v_val_1427_);
        return v___x_1428_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___redArg(
    mut v_x_1429_: *mut crate::leanh::LeanObject,
    mut v_h__1_1430_: *mut crate::leanh::LeanObject,
    mut v_h__2_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1429_) == 0 {
        let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1431_);
        v___x_1432_ = crate::leanh::lean_box(0);
        v___x_1433_ = crate::leanh::lean_apply_1(v_h__1_1430_, v___x_1432_);
        return v___x_1433_;
    } else {
        let mut v_val_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1430_);
        v_val_1434_ = crate::leanh::lean_ctor_get(v_x_1429_, 0);
        crate::leanh::lean_inc(v_val_1434_);
        crate::leanh::lean_dec_ref_known(v_x_1429_, 1);
        v___x_1435_ = crate::leanh::lean_apply_1(v_h__2_1431_, v_val_1434_);
        return v___x_1435_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(
    mut v_00_u03b1_1436_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1437_: *mut crate::leanh::LeanObject,
    mut v_k_1438_: *mut crate::leanh::LeanObject,
    mut v_motive_1439_: *mut crate::leanh::LeanObject,
    mut v_x_1440_: *mut crate::leanh::LeanObject,
    mut v_h__1_1441_: *mut crate::leanh::LeanObject,
    mut v_h__2_1442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1440_) == 0 {
        let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1442_);
        v___x_1443_ = crate::leanh::lean_box(0);
        v___x_1444_ = crate::leanh::lean_apply_1(v_h__1_1441_, v___x_1443_);
        return v___x_1444_;
    } else {
        let mut v_val_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1441_);
        v_val_1445_ = crate::leanh::lean_ctor_get(v_x_1440_, 0);
        crate::leanh::lean_inc(v_val_1445_);
        crate::leanh::lean_dec_ref_known(v_x_1440_, 1);
        v___x_1446_ = crate::leanh::lean_apply_1(v_h__2_1442_, v_val_1445_);
        return v___x_1446_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___boxed(
    mut v_00_u03b1_1447_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1448_: *mut crate::leanh::LeanObject,
    mut v_k_1449_: *mut crate::leanh::LeanObject,
    mut v_motive_1450_: *mut crate::leanh::LeanObject,
    mut v_x_1451_: *mut crate::leanh::LeanObject,
    mut v_h__1_1452_: *mut crate::leanh::LeanObject,
    mut v_h__2_1453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1454_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(v_00_u03b1_1447_, v_00_u03b2_1448_, v_k_1449_, v_motive_1450_, v_x_1451_, v_h__1_1452_, v_h__2_1453_);
    crate::leanh::lean_dec(v_k_1449_);
    return v_res_1454_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filterMap_match__1_splitter___redArg(
    mut v_x_1455_: *mut crate::leanh::LeanObject,
    mut v_h__1_1456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1457_ = crate::leanh::lean_apply_2(v_h__1_1456_, v_x_1455_, crate::leanh::lean_box(0));
    return v___x_1457_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filterMap_match__1_splitter(
    mut v_00_u03b1_1458_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1459_: *mut crate::leanh::LeanObject,
    mut v_motive_1460_: *mut crate::leanh::LeanObject,
    mut v_x_1461_: *mut crate::leanh::LeanObject,
    mut v_h__1_1462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1463_ = crate::leanh::lean_apply_2(v_h__1_1462_, v_x_1461_, crate::leanh::lean_box(0));
    return v___x_1463_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(
    mut v_x_1464_: u8,
    mut v_h__1_1465_: *mut crate::leanh::LeanObject,
    mut v_h__2_1466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_1464_ == 0 {
        let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1466_);
        v___x_1467_ = crate::leanh::lean_box(0);
        v___x_1468_ = crate::leanh::lean_apply_1(v_h__1_1465_, v___x_1467_);
        return v___x_1468_;
    } else {
        let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1465_);
        v___x_1469_ = crate::leanh::lean_box(0);
        v___x_1470_ = crate::leanh::lean_apply_1(v_h__2_1466_, v___x_1469_);
        return v___x_1470_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg___boxed(
    mut v_x_1471_: *mut crate::leanh::LeanObject,
    mut v_h__1_1472_: *mut crate::leanh::LeanObject,
    mut v_h__2_1473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_1474_: u8 = 0;
    let mut v_res_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1474_ = (crate::leanh::lean_unbox(v_x_1471_) as u8);
    v_res_1475_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(v_x_26__boxed_1474_, v_h__1_1472_, v_h__2_1473_);
    return v_res_1475_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(
    mut v_motive_1476_: *mut crate::leanh::LeanObject,
    mut v_x_1477_: u8,
    mut v_h__1_1478_: *mut crate::leanh::LeanObject,
    mut v_h__2_1479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_1477_ == 0 {
        let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1479_);
        v___x_1480_ = crate::leanh::lean_box(0);
        v___x_1481_ = crate::leanh::lean_apply_1(v_h__1_1478_, v___x_1480_);
        return v___x_1481_;
    } else {
        let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1478_);
        v___x_1482_ = crate::leanh::lean_box(0);
        v___x_1483_ = crate::leanh::lean_apply_1(v_h__2_1479_, v___x_1482_);
        return v___x_1483_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___boxed(
    mut v_motive_1484_: *mut crate::leanh::LeanObject,
    mut v_x_1485_: *mut crate::leanh::LeanObject,
    mut v_h__1_1486_: *mut crate::leanh::LeanObject,
    mut v_h__2_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_37__boxed_1488_: u8 = 0;
    let mut v_res_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_1488_ = (crate::leanh::lean_unbox(v_x_1485_) as u8);
    v_res_1489_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(v_motive_1484_, v_x_37__boxed_1488_, v_h__1_1486_, v_h__2_1487_);
    return v_res_1489_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___redArg(
    mut v_v_x3f_1490_: *mut crate::leanh::LeanObject,
    mut v_h__1_1491_: *mut crate::leanh::LeanObject,
    mut v_h__2_1492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_v_x3f_1490_) == 0 {
        let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1492_);
        v___x_1493_ = crate::leanh::lean_box(0);
        v___x_1494_ = crate::leanh::lean_apply_1(v_h__1_1491_, v___x_1493_);
        return v___x_1494_;
    } else {
        let mut v_val_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1491_);
        v_val_1495_ = crate::leanh::lean_ctor_get(v_v_x3f_1490_, 0);
        crate::leanh::lean_inc(v_val_1495_);
        crate::leanh::lean_dec_ref_known(v_v_x3f_1490_, 1);
        v___x_1496_ = crate::leanh::lean_apply_1(v_h__2_1492_, v_val_1495_);
        return v___x_1496_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(
    mut v_00_u03b1_1497_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1498_: *mut crate::leanh::LeanObject,
    mut v_k_1499_: *mut crate::leanh::LeanObject,
    mut v_motive_1500_: *mut crate::leanh::LeanObject,
    mut v_v_x3f_1501_: *mut crate::leanh::LeanObject,
    mut v_h__1_1502_: *mut crate::leanh::LeanObject,
    mut v_h__2_1503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_v_x3f_1501_) == 0 {
        let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1503_);
        v___x_1504_ = crate::leanh::lean_box(0);
        v___x_1505_ = crate::leanh::lean_apply_1(v_h__1_1502_, v___x_1504_);
        return v___x_1505_;
    } else {
        let mut v_val_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1502_);
        v_val_1506_ = crate::leanh::lean_ctor_get(v_v_x3f_1501_, 0);
        crate::leanh::lean_inc(v_val_1506_);
        crate::leanh::lean_dec_ref_known(v_v_x3f_1501_, 1);
        v___x_1507_ = crate::leanh::lean_apply_1(v_h__2_1503_, v_val_1506_);
        return v___x_1507_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___boxed(
    mut v_00_u03b1_1508_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1509_: *mut crate::leanh::LeanObject,
    mut v_k_1510_: *mut crate::leanh::LeanObject,
    mut v_motive_1511_: *mut crate::leanh::LeanObject,
    mut v_v_x3f_1512_: *mut crate::leanh::LeanObject,
    mut v_h__1_1513_: *mut crate::leanh::LeanObject,
    mut v_h__2_1514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1515_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(v_00_u03b1_1508_, v_00_u03b2_1509_, v_k_1510_, v_motive_1511_, v_v_x3f_1512_, v_h__1_1513_, v_h__2_1514_);
    crate::leanh::lean_dec(v_k_1510_);
    return v_res_1515_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(
    mut v_x_1516_: *mut crate::leanh::LeanObject,
    mut v_h__1_1517_: *mut crate::leanh::LeanObject,
    mut v_h__2_1518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1516_) == 0 {
        let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1518_);
        v___x_1519_ = crate::leanh::lean_box(0);
        v___x_1520_ = crate::leanh::lean_apply_1(v_h__1_1517_, v___x_1519_);
        return v___x_1520_;
    } else {
        let mut v_val_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1517_);
        v_val_1521_ = crate::leanh::lean_ctor_get(v_x_1516_, 0);
        crate::leanh::lean_inc(v_val_1521_);
        crate::leanh::lean_dec_ref_known(v_x_1516_, 1);
        v___x_1522_ = crate::leanh::lean_apply_1(v_h__2_1518_, v_val_1521_);
        return v___x_1522_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(
    mut v_00_u03b1_1523_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1524_: *mut crate::leanh::LeanObject,
    mut v_k_1525_: *mut crate::leanh::LeanObject,
    mut v_motive_1526_: *mut crate::leanh::LeanObject,
    mut v_x_1527_: *mut crate::leanh::LeanObject,
    mut v_h__1_1528_: *mut crate::leanh::LeanObject,
    mut v_h__2_1529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1527_) == 0 {
        let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1529_);
        v___x_1530_ = crate::leanh::lean_box(0);
        v___x_1531_ = crate::leanh::lean_apply_1(v_h__1_1528_, v___x_1530_);
        return v___x_1531_;
    } else {
        let mut v_val_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1528_);
        v_val_1532_ = crate::leanh::lean_ctor_get(v_x_1527_, 0);
        crate::leanh::lean_inc(v_val_1532_);
        crate::leanh::lean_dec_ref_known(v_x_1527_, 1);
        v___x_1533_ = crate::leanh::lean_apply_1(v_h__2_1529_, v_val_1532_);
        return v___x_1533_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(
    mut v_00_u03b1_1534_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1535_: *mut crate::leanh::LeanObject,
    mut v_k_1536_: *mut crate::leanh::LeanObject,
    mut v_motive_1537_: *mut crate::leanh::LeanObject,
    mut v_x_1538_: *mut crate::leanh::LeanObject,
    mut v_h__1_1539_: *mut crate::leanh::LeanObject,
    mut v_h__2_1540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1541_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_1534_, v_00_u03b2_1535_, v_k_1536_, v_motive_1537_, v_x_1538_, v_h__1_1539_, v_h__2_1540_);
    crate::leanh::lean_dec(v_k_1536_);
    return v_res_1541_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter___redArg(
    mut v_x_1542_: *mut crate::leanh::LeanObject,
    mut v_h__1_1543_: *mut crate::leanh::LeanObject,
    mut v_h__2_1544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1542_) == 0 {
        let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1544_);
        v___x_1545_ = crate::leanh::lean_apply_1(v_h__1_1543_, crate::leanh::lean_box(0));
        return v___x_1545_;
    } else {
        let mut v_val_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1543_);
        v_val_1546_ = crate::leanh::lean_ctor_get(v_x_1542_, 0);
        crate::leanh::lean_inc(v_val_1546_);
        crate::leanh::lean_dec_ref_known(v_x_1542_, 1);
        v_fst_1547_ = crate::leanh::lean_ctor_get(v_val_1546_, 0);
        crate::leanh::lean_inc(v_fst_1547_);
        v_snd_1548_ = crate::leanh::lean_ctor_get(v_val_1546_, 1);
        crate::leanh::lean_inc(v_snd_1548_);
        crate::leanh::lean_dec(v_val_1546_);
        v___x_1549_ = crate::leanh::lean_apply_3(
            v_h__2_1544_,
            v_fst_1547_,
            v_snd_1548_,
            crate::leanh::lean_box(0),
        );
        return v___x_1549_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter(
    mut v_00_u03b1_1550_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1551_: *mut crate::leanh::LeanObject,
    mut v_motive_1552_: *mut crate::leanh::LeanObject,
    mut v_x_1553_: *mut crate::leanh::LeanObject,
    mut v_h__1_1554_: *mut crate::leanh::LeanObject,
    mut v_h__2_1555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1553_) == 0 {
        let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1555_);
        v___x_1556_ = crate::leanh::lean_apply_1(v_h__1_1554_, crate::leanh::lean_box(0));
        return v___x_1556_;
    } else {
        let mut v_val_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1554_);
        v_val_1557_ = crate::leanh::lean_ctor_get(v_x_1553_, 0);
        crate::leanh::lean_inc(v_val_1557_);
        crate::leanh::lean_dec_ref_known(v_x_1553_, 1);
        v_fst_1558_ = crate::leanh::lean_ctor_get(v_val_1557_, 0);
        crate::leanh::lean_inc(v_fst_1558_);
        v_snd_1559_ = crate::leanh::lean_ctor_get(v_val_1557_, 1);
        crate::leanh::lean_inc(v_snd_1559_);
        crate::leanh::lean_dec(v_val_1557_);
        v___x_1560_ = crate::leanh::lean_apply_3(
            v_h__2_1555_,
            v_fst_1558_,
            v_snd_1559_,
            crate::leanh::lean_box(0),
        );
        return v___x_1560_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___redArg(
    mut v_x_1561_: *mut crate::leanh::LeanObject,
    mut v_h__1_1562_: *mut crate::leanh::LeanObject,
    mut v_h__2_1563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1561_) == 0 {
        let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1563_);
        v___x_1564_ = crate::leanh::lean_box(0);
        v___x_1565_ = crate::leanh::lean_apply_1(v_h__1_1562_, v___x_1564_);
        return v___x_1565_;
    } else {
        let mut v_val_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1562_);
        v_val_1566_ = crate::leanh::lean_ctor_get(v_x_1561_, 0);
        crate::leanh::lean_inc(v_val_1566_);
        crate::leanh::lean_dec_ref_known(v_x_1561_, 1);
        v___x_1567_ = crate::leanh::lean_apply_1(v_h__2_1563_, v_val_1566_);
        return v___x_1567_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(
    mut v_00_u03b1_1568_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1569_: *mut crate::leanh::LeanObject,
    mut v_k_1570_: *mut crate::leanh::LeanObject,
    mut v_motive_1571_: *mut crate::leanh::LeanObject,
    mut v_x_1572_: *mut crate::leanh::LeanObject,
    mut v_h__1_1573_: *mut crate::leanh::LeanObject,
    mut v_h__2_1574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1572_) == 0 {
        let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1574_);
        v___x_1575_ = crate::leanh::lean_box(0);
        v___x_1576_ = crate::leanh::lean_apply_1(v_h__1_1573_, v___x_1575_);
        return v___x_1576_;
    } else {
        let mut v_val_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1573_);
        v_val_1577_ = crate::leanh::lean_ctor_get(v_x_1572_, 0);
        crate::leanh::lean_inc(v_val_1577_);
        crate::leanh::lean_dec_ref_known(v_x_1572_, 1);
        v___x_1578_ = crate::leanh::lean_apply_1(v_h__2_1574_, v_val_1577_);
        return v___x_1578_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___boxed(
    mut v_00_u03b1_1579_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1580_: *mut crate::leanh::LeanObject,
    mut v_k_1581_: *mut crate::leanh::LeanObject,
    mut v_motive_1582_: *mut crate::leanh::LeanObject,
    mut v_x_1583_: *mut crate::leanh::LeanObject,
    mut v_h__1_1584_: *mut crate::leanh::LeanObject,
    mut v_h__2_1585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1586_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(v_00_u03b1_1579_, v_00_u03b2_1580_, v_k_1581_, v_motive_1582_, v_x_1583_, v_h__1_1584_, v_h__2_1585_);
    crate::leanh::lean_dec(v_k_1581_);
    return v_res_1586_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(
    mut v_x_1587_: u8,
    mut v_h__1_1588_: *mut crate::leanh::LeanObject,
    mut v_h__2_1589_: *mut crate::leanh::LeanObject,
    mut v_h__3_1590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_1587_ {
        0 => {
            let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1590_);
            crate::leanh::lean_dec(v_h__2_1589_);
            v___x_1591_ = crate::leanh::lean_apply_1(v_h__1_1588_, crate::leanh::lean_box(0));
            return v___x_1591_;
        }
        1 => {
            let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1589_);
            crate::leanh::lean_dec(v_h__1_1588_);
            v___x_1592_ = crate::leanh::lean_apply_1(v_h__3_1590_, crate::leanh::lean_box(0));
            return v___x_1592_;
        }
        _ => {
            let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1590_);
            crate::leanh::lean_dec(v_h__1_1588_);
            v___x_1593_ = crate::leanh::lean_apply_1(v_h__2_1589_, crate::leanh::lean_box(0));
            return v___x_1593_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg___boxed(
    mut v_x_1594_: *mut crate::leanh::LeanObject,
    mut v_h__1_1595_: *mut crate::leanh::LeanObject,
    mut v_h__2_1596_: *mut crate::leanh::LeanObject,
    mut v_h__3_1597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_33__boxed_1598_: u8 = 0;
    let mut v_res_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_33__boxed_1598_ = (crate::leanh::lean_unbox(v_x_1594_) as u8);
    v_res_1599_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(v_x_33__boxed_1598_, v_h__1_1595_, v_h__2_1596_, v_h__3_1597_);
    return v_res_1599_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(
    mut v_motive_1600_: *mut crate::leanh::LeanObject,
    mut v_x_1601_: u8,
    mut v_h__1_1602_: *mut crate::leanh::LeanObject,
    mut v_h__2_1603_: *mut crate::leanh::LeanObject,
    mut v_h__3_1604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_1601_ {
        0 => {
            let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1604_);
            crate::leanh::lean_dec(v_h__2_1603_);
            v___x_1605_ = crate::leanh::lean_apply_1(v_h__1_1602_, crate::leanh::lean_box(0));
            return v___x_1605_;
        }
        1 => {
            let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1603_);
            crate::leanh::lean_dec(v_h__1_1602_);
            v___x_1606_ = crate::leanh::lean_apply_1(v_h__3_1604_, crate::leanh::lean_box(0));
            return v___x_1606_;
        }
        _ => {
            let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1604_);
            crate::leanh::lean_dec(v_h__1_1602_);
            v___x_1607_ = crate::leanh::lean_apply_1(v_h__2_1603_, crate::leanh::lean_box(0));
            return v___x_1607_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___boxed(
    mut v_motive_1608_: *mut crate::leanh::LeanObject,
    mut v_x_1609_: *mut crate::leanh::LeanObject,
    mut v_h__1_1610_: *mut crate::leanh::LeanObject,
    mut v_h__2_1611_: *mut crate::leanh::LeanObject,
    mut v_h__3_1612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_42__boxed_1613_: u8 = 0;
    let mut v_res_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_42__boxed_1613_ = (crate::leanh::lean_unbox(v_x_1609_) as u8);
    v_res_1614_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(v_motive_1608_, v_x_42__boxed_1613_, v_h__1_1610_, v_h__2_1611_, v_h__3_1612_);
    return v_res_1614_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter___redArg(
    mut v_x_1615_: *mut crate::leanh::LeanObject,
    mut v_h__1_1616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1617_ = crate::leanh::lean_apply_4(
        v_h__1_1616_,
        v_x_1615_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1617_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter(
    mut v_00_u03b1_1618_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1619_: *mut crate::leanh::LeanObject,
    mut v_l_x27_1620_: *mut crate::leanh::LeanObject,
    mut v_motive_1621_: *mut crate::leanh::LeanObject,
    mut v_x_1622_: *mut crate::leanh::LeanObject,
    mut v_h__1_1623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1624_ = crate::leanh::lean_apply_4(
        v_h__1_1623_,
        v_x_1622_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1624_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter___boxed(
    mut v_00_u03b1_1625_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1626_: *mut crate::leanh::LeanObject,
    mut v_l_x27_1627_: *mut crate::leanh::LeanObject,
    mut v_motive_1628_: *mut crate::leanh::LeanObject,
    mut v_x_1629_: *mut crate::leanh::LeanObject,
    mut v_h__1_1630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1631_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter(v_00_u03b1_1625_, v_00_u03b2_1626_, v_l_x27_1627_, v_motive_1628_, v_x_1629_, v_h__1_1630_);
    crate::leanh::lean_dec(v_l_x27_1627_);
    return v_res_1631_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(
    mut v_l_1632_: *mut crate::leanh::LeanObject,
    mut v_h__1_1633_: *mut crate::leanh::LeanObject,
    mut v_h__2_1634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_1632_) == 0 {
        let mut v_size_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1633_);
        v_size_1635_ = crate::leanh::lean_ctor_get(v_l_1632_, 0);
        crate::leanh::lean_inc(v_size_1635_);
        v_k_1636_ = crate::leanh::lean_ctor_get(v_l_1632_, 1);
        crate::leanh::lean_inc(v_k_1636_);
        v_v_1637_ = crate::leanh::lean_ctor_get(v_l_1632_, 2);
        crate::leanh::lean_inc(v_v_1637_);
        v_l_1638_ = crate::leanh::lean_ctor_get(v_l_1632_, 3);
        crate::leanh::lean_inc(v_l_1638_);
        v_r_1639_ = crate::leanh::lean_ctor_get(v_l_1632_, 4);
        crate::leanh::lean_inc(v_r_1639_);
        crate::leanh::lean_dec_ref_known(v_l_1632_, 5);
        v___x_1640_ = crate::leanh::lean_apply_5(
            v_h__2_1634_,
            v_size_1635_,
            v_k_1636_,
            v_v_1637_,
            v_l_1638_,
            v_r_1639_,
        );
        return v___x_1640_;
    } else {
        let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1634_);
        v___x_1641_ = crate::leanh::lean_box(0);
        v___x_1642_ = crate::leanh::lean_apply_1(v_h__1_1633_, v___x_1641_);
        return v___x_1642_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(
    mut v_00_u03b1_1643_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1644_: *mut crate::leanh::LeanObject,
    mut v_motive_1645_: *mut crate::leanh::LeanObject,
    mut v_l_1646_: *mut crate::leanh::LeanObject,
    mut v_h__1_1647_: *mut crate::leanh::LeanObject,
    mut v_h__2_1648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_1646_) == 0 {
        let mut v_size_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1647_);
        v_size_1649_ = crate::leanh::lean_ctor_get(v_l_1646_, 0);
        crate::leanh::lean_inc(v_size_1649_);
        v_k_1650_ = crate::leanh::lean_ctor_get(v_l_1646_, 1);
        crate::leanh::lean_inc(v_k_1650_);
        v_v_1651_ = crate::leanh::lean_ctor_get(v_l_1646_, 2);
        crate::leanh::lean_inc(v_v_1651_);
        v_l_1652_ = crate::leanh::lean_ctor_get(v_l_1646_, 3);
        crate::leanh::lean_inc(v_l_1652_);
        v_r_1653_ = crate::leanh::lean_ctor_get(v_l_1646_, 4);
        crate::leanh::lean_inc(v_r_1653_);
        crate::leanh::lean_dec_ref_known(v_l_1646_, 5);
        v___x_1654_ = crate::leanh::lean_apply_5(
            v_h__2_1648_,
            v_size_1649_,
            v_k_1650_,
            v_v_1651_,
            v_l_1652_,
            v_r_1653_,
        );
        return v___x_1654_;
    } else {
        let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1648_);
        v___x_1655_ = crate::leanh::lean_box(0);
        v___x_1656_ = crate::leanh::lean_apply_1(v_h__1_1647_, v___x_1655_);
        return v___x_1656_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(
    mut v_t_1657_: *mut crate::leanh::LeanObject,
    mut v_h__1_1658_: *mut crate::leanh::LeanObject,
    mut v_h__2_1659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1657_) == 0 {
        let mut v_size_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1658_);
        v_size_1660_ = crate::leanh::lean_ctor_get(v_t_1657_, 0);
        crate::leanh::lean_inc(v_size_1660_);
        v_k_1661_ = crate::leanh::lean_ctor_get(v_t_1657_, 1);
        crate::leanh::lean_inc(v_k_1661_);
        v_v_1662_ = crate::leanh::lean_ctor_get(v_t_1657_, 2);
        crate::leanh::lean_inc(v_v_1662_);
        v_l_1663_ = crate::leanh::lean_ctor_get(v_t_1657_, 3);
        crate::leanh::lean_inc(v_l_1663_);
        v_r_1664_ = crate::leanh::lean_ctor_get(v_t_1657_, 4);
        crate::leanh::lean_inc(v_r_1664_);
        crate::leanh::lean_dec_ref_known(v_t_1657_, 5);
        v___x_1665_ = crate::leanh::lean_apply_5(
            v_h__2_1659_,
            v_size_1660_,
            v_k_1661_,
            v_v_1662_,
            v_l_1663_,
            v_r_1664_,
        );
        return v___x_1665_;
    } else {
        let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1659_);
        v___x_1666_ = crate::leanh::lean_box(0);
        v___x_1667_ = crate::leanh::lean_apply_1(v_h__1_1658_, v___x_1666_);
        return v___x_1667_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(
    mut v_00_u03b1_1668_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1669_: *mut crate::leanh::LeanObject,
    mut v_motive_1670_: *mut crate::leanh::LeanObject,
    mut v_t_1671_: *mut crate::leanh::LeanObject,
    mut v_h__1_1672_: *mut crate::leanh::LeanObject,
    mut v_h__2_1673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1671_) == 0 {
        let mut v_size_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1672_);
        v_size_1674_ = crate::leanh::lean_ctor_get(v_t_1671_, 0);
        crate::leanh::lean_inc(v_size_1674_);
        v_k_1675_ = crate::leanh::lean_ctor_get(v_t_1671_, 1);
        crate::leanh::lean_inc(v_k_1675_);
        v_v_1676_ = crate::leanh::lean_ctor_get(v_t_1671_, 2);
        crate::leanh::lean_inc(v_v_1676_);
        v_l_1677_ = crate::leanh::lean_ctor_get(v_t_1671_, 3);
        crate::leanh::lean_inc(v_l_1677_);
        v_r_1678_ = crate::leanh::lean_ctor_get(v_t_1671_, 4);
        crate::leanh::lean_inc(v_r_1678_);
        crate::leanh::lean_dec_ref_known(v_t_1671_, 5);
        v___x_1679_ = crate::leanh::lean_apply_5(
            v_h__2_1673_,
            v_size_1674_,
            v_k_1675_,
            v_v_1676_,
            v_l_1677_,
            v_r_1678_,
        );
        return v___x_1679_;
    } else {
        let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1673_);
        v___x_1680_ = crate::leanh::lean_box(0);
        v___x_1681_ = crate::leanh::lean_apply_1(v_h__1_1672_, v___x_1680_);
        return v___x_1681_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter___redArg(
    mut v_____do__lift_1682_: *mut crate::leanh::LeanObject,
    mut v_h__1_1683_: *mut crate::leanh::LeanObject,
    mut v_h__2_1684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1682_) == 0 {
        let mut v_a_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1684_);
        v_a_1685_ = crate::leanh::lean_ctor_get(v_____do__lift_1682_, 0);
        crate::leanh::lean_inc(v_a_1685_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1682_, 1);
        v___x_1686_ = crate::leanh::lean_apply_1(v_h__1_1683_, v_a_1685_);
        return v___x_1686_;
    } else {
        let mut v_a_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1683_);
        v_a_1687_ = crate::leanh::lean_ctor_get(v_____do__lift_1682_, 0);
        crate::leanh::lean_inc(v_a_1687_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1682_, 1);
        v___x_1688_ = crate::leanh::lean_apply_1(v_h__2_1684_, v_a_1687_);
        return v___x_1688_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter(
    mut v_00_u03b4_1689_: *mut crate::leanh::LeanObject,
    mut v_motive_1690_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1691_: *mut crate::leanh::LeanObject,
    mut v_h__1_1692_: *mut crate::leanh::LeanObject,
    mut v_h__2_1693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1691_) == 0 {
        let mut v_a_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1693_);
        v_a_1694_ = crate::leanh::lean_ctor_get(v_____do__lift_1691_, 0);
        crate::leanh::lean_inc(v_a_1694_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1691_, 1);
        v___x_1695_ = crate::leanh::lean_apply_1(v_h__1_1692_, v_a_1694_);
        return v___x_1695_;
    } else {
        let mut v_a_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1692_);
        v_a_1696_ = crate::leanh::lean_ctor_get(v_____do__lift_1691_, 0);
        crate::leanh::lean_inc(v_a_1696_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1691_, 1);
        v___x_1697_ = crate::leanh::lean_apply_1(v_h__2_1693_, v_a_1696_);
        return v___x_1697_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter___redArg(
    mut v_x_1698_: *mut crate::leanh::LeanObject,
    mut v_h__1_1699_: *mut crate::leanh::LeanObject,
    mut v_h__2_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1698_) == 0 {
        let mut v_a_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1699_);
        v_a_1701_ = crate::leanh::lean_ctor_get(v_x_1698_, 0);
        crate::leanh::lean_inc(v_a_1701_);
        crate::leanh::lean_dec_ref_known(v_x_1698_, 1);
        v___x_1702_ = crate::leanh::lean_apply_1(v_h__2_1700_, v_a_1701_);
        return v___x_1702_;
    } else {
        let mut v_a_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1700_);
        v_a_1703_ = crate::leanh::lean_ctor_get(v_x_1698_, 0);
        crate::leanh::lean_inc(v_a_1703_);
        crate::leanh::lean_dec_ref_known(v_x_1698_, 1);
        v___x_1704_ = crate::leanh::lean_apply_1(v_h__1_1699_, v_a_1703_);
        return v___x_1704_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter(
    mut v_00_u03b4_1705_: *mut crate::leanh::LeanObject,
    mut v_motive_1706_: *mut crate::leanh::LeanObject,
    mut v_x_1707_: *mut crate::leanh::LeanObject,
    mut v_h__1_1708_: *mut crate::leanh::LeanObject,
    mut v_h__2_1709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1707_) == 0 {
        let mut v_a_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1708_);
        v_a_1710_ = crate::leanh::lean_ctor_get(v_x_1707_, 0);
        crate::leanh::lean_inc(v_a_1710_);
        crate::leanh::lean_dec_ref_known(v_x_1707_, 1);
        v___x_1711_ = crate::leanh::lean_apply_1(v_h__2_1709_, v_a_1710_);
        return v___x_1711_;
    } else {
        let mut v_a_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1709_);
        v_a_1712_ = crate::leanh::lean_ctor_get(v_x_1707_, 0);
        crate::leanh::lean_inc(v_a_1712_);
        crate::leanh::lean_dec_ref_known(v_x_1707_, 1);
        v___x_1713_ = crate::leanh::lean_apply_1(v_h__1_1708_, v_a_1712_);
        return v___x_1713_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_1714_: *mut crate::leanh::LeanObject,
    mut v_h__1_1715_: *mut crate::leanh::LeanObject,
    mut v_h__2_1716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_b_1714_) == 0 {
        let mut v_a_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1715_);
        v_a_1717_ = crate::leanh::lean_ctor_get(v_b_1714_, 0);
        crate::leanh::lean_inc(v_a_1717_);
        crate::leanh::lean_dec_ref_known(v_b_1714_, 1);
        v___x_1718_ = crate::leanh::lean_apply_1(v_h__2_1716_, v_a_1717_);
        return v___x_1718_;
    } else {
        let mut v_a_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1716_);
        v_a_1719_ = crate::leanh::lean_ctor_get(v_b_1714_, 0);
        crate::leanh::lean_inc(v_a_1719_);
        crate::leanh::lean_dec_ref_known(v_b_1714_, 1);
        v___x_1720_ = crate::leanh::lean_apply_1(v_h__1_1715_, v_a_1719_);
        return v___x_1720_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_1721_: *mut crate::leanh::LeanObject,
    mut v_motive_1722_: *mut crate::leanh::LeanObject,
    mut v_b_1723_: *mut crate::leanh::LeanObject,
    mut v_h__1_1724_: *mut crate::leanh::LeanObject,
    mut v_h__2_1725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_b_1723_) == 0 {
        let mut v_a_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1724_);
        v_a_1726_ = crate::leanh::lean_ctor_get(v_b_1723_, 0);
        crate::leanh::lean_inc(v_a_1726_);
        crate::leanh::lean_dec_ref_known(v_b_1723_, 1);
        v___x_1727_ = crate::leanh::lean_apply_1(v_h__2_1725_, v_a_1726_);
        return v___x_1727_;
    } else {
        let mut v_a_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1725_);
        v_a_1728_ = crate::leanh::lean_ctor_get(v_b_1723_, 0);
        crate::leanh::lean_inc(v_a_1728_);
        crate::leanh::lean_dec_ref_known(v_b_1723_, 1);
        v___x_1729_ = crate::leanh::lean_apply_1(v_h__1_1724_, v_a_1728_);
        return v___x_1729_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(
    mut v_x_1730_: *mut crate::leanh::LeanObject,
    mut v_h__1_1731_: *mut crate::leanh::LeanObject,
    mut v_h__2_1732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1730_) == 0 {
        let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1732_);
        v___x_1733_ = crate::leanh::lean_box(0);
        v___x_1734_ = crate::leanh::lean_apply_1(v_h__1_1731_, v___x_1733_);
        return v___x_1734_;
    } else {
        let mut v_val_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1731_);
        v_val_1735_ = crate::leanh::lean_ctor_get(v_x_1730_, 0);
        crate::leanh::lean_inc(v_val_1735_);
        crate::leanh::lean_dec_ref_known(v_x_1730_, 1);
        v___x_1736_ = crate::leanh::lean_apply_1(v_h__2_1732_, v_val_1735_);
        return v___x_1736_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter(
    mut v_00_u03b2_1737_: *mut crate::leanh::LeanObject,
    mut v_motive_1738_: *mut crate::leanh::LeanObject,
    mut v_x_1739_: *mut crate::leanh::LeanObject,
    mut v_h__1_1740_: *mut crate::leanh::LeanObject,
    mut v_h__2_1741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1739_) == 0 {
        let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1741_);
        v___x_1742_ = crate::leanh::lean_box(0);
        v___x_1743_ = crate::leanh::lean_apply_1(v_h__1_1740_, v___x_1742_);
        return v___x_1743_;
    } else {
        let mut v_val_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1740_);
        v_val_1744_ = crate::leanh::lean_ctor_get(v_x_1739_, 0);
        crate::leanh::lean_inc(v_val_1744_);
        crate::leanh::lean_dec_ref_known(v_x_1739_, 1);
        v___x_1745_ = crate::leanh::lean_apply_1(v_h__2_1741_, v_val_1744_);
        return v___x_1745_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter___redArg(
    mut v_x_1746_: *mut crate::leanh::LeanObject,
    mut v_h__1_1747_: *mut crate::leanh::LeanObject,
    mut v_h__2_1748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1746_) == 0 {
        let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1748_);
        v___x_1749_ = crate::leanh::lean_box(0);
        v___x_1750_ = crate::leanh::lean_apply_1(v_h__1_1747_, v___x_1749_);
        return v___x_1750_;
    } else {
        let mut v_val_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1747_);
        v_val_1751_ = crate::leanh::lean_ctor_get(v_x_1746_, 0);
        crate::leanh::lean_inc(v_val_1751_);
        crate::leanh::lean_dec_ref_known(v_x_1746_, 1);
        v_fst_1752_ = crate::leanh::lean_ctor_get(v_val_1751_, 0);
        crate::leanh::lean_inc(v_fst_1752_);
        v_snd_1753_ = crate::leanh::lean_ctor_get(v_val_1751_, 1);
        crate::leanh::lean_inc(v_snd_1753_);
        crate::leanh::lean_dec(v_val_1751_);
        v___x_1754_ = crate::leanh::lean_apply_2(v_h__2_1748_, v_fst_1752_, v_snd_1753_);
        return v___x_1754_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter(
    mut v_00_u03b1_1755_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1756_: *mut crate::leanh::LeanObject,
    mut v_motive_1757_: *mut crate::leanh::LeanObject,
    mut v_x_1758_: *mut crate::leanh::LeanObject,
    mut v_h__1_1759_: *mut crate::leanh::LeanObject,
    mut v_h__2_1760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1758_) == 0 {
        let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1760_);
        v___x_1761_ = crate::leanh::lean_box(0);
        v___x_1762_ = crate::leanh::lean_apply_1(v_h__1_1759_, v___x_1761_);
        return v___x_1762_;
    } else {
        let mut v_val_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1759_);
        v_val_1763_ = crate::leanh::lean_ctor_get(v_x_1758_, 0);
        crate::leanh::lean_inc(v_val_1763_);
        crate::leanh::lean_dec_ref_known(v_x_1758_, 1);
        v_fst_1764_ = crate::leanh::lean_ctor_get(v_val_1763_, 0);
        crate::leanh::lean_inc(v_fst_1764_);
        v_snd_1765_ = crate::leanh::lean_ctor_get(v_val_1763_, 1);
        crate::leanh::lean_inc(v_snd_1765_);
        crate::leanh::lean_dec(v_val_1763_);
        v___x_1766_ = crate::leanh::lean_apply_2(v_h__2_1760_, v_fst_1764_, v_snd_1765_);
        return v___x_1766_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(
    mut v_x_1767_: *mut crate::leanh::LeanObject,
    mut v_h__1_1768_: *mut crate::leanh::LeanObject,
    mut v_h__2_1769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1767_) == 0 {
        let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1769_);
        v___x_1770_ = crate::leanh::lean_box(0);
        v___x_1771_ = crate::leanh::lean_apply_1(v_h__1_1768_, v___x_1770_);
        return v___x_1771_;
    } else {
        let mut v_val_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1768_);
        v_val_1772_ = crate::leanh::lean_ctor_get(v_x_1767_, 0);
        crate::leanh::lean_inc(v_val_1772_);
        crate::leanh::lean_dec_ref_known(v_x_1767_, 1);
        v___x_1773_ = crate::leanh::lean_apply_1(v_h__2_1769_, v_val_1772_);
        return v___x_1773_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter(
    mut v_00_u03b2_1774_: *mut crate::leanh::LeanObject,
    mut v_motive_1775_: *mut crate::leanh::LeanObject,
    mut v_x_1776_: *mut crate::leanh::LeanObject,
    mut v_h__1_1777_: *mut crate::leanh::LeanObject,
    mut v_h__2_1778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1776_) == 0 {
        let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1778_);
        v___x_1779_ = crate::leanh::lean_box(0);
        v___x_1780_ = crate::leanh::lean_apply_1(v_h__1_1777_, v___x_1779_);
        return v___x_1780_;
    } else {
        let mut v_val_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1777_);
        v_val_1781_ = crate::leanh::lean_ctor_get(v_x_1776_, 0);
        crate::leanh::lean_inc(v_val_1781_);
        crate::leanh::lean_dec_ref_known(v_x_1776_, 1);
        v___x_1782_ = crate::leanh::lean_apply_1(v_h__2_1778_, v_val_1781_);
        return v___x_1782_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__3_splitter___redArg(
    mut v_t_1783_: *mut crate::leanh::LeanObject,
    mut v_h__1_1784_: *mut crate::leanh::LeanObject,
    mut v_h__2_1785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1783_) == 0 {
        let mut v_size_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1784_);
        v_size_1786_ = crate::leanh::lean_ctor_get(v_t_1783_, 0);
        crate::leanh::lean_inc(v_size_1786_);
        v_k_1787_ = crate::leanh::lean_ctor_get(v_t_1783_, 1);
        crate::leanh::lean_inc(v_k_1787_);
        v_v_1788_ = crate::leanh::lean_ctor_get(v_t_1783_, 2);
        crate::leanh::lean_inc(v_v_1788_);
        v_l_1789_ = crate::leanh::lean_ctor_get(v_t_1783_, 3);
        crate::leanh::lean_inc(v_l_1789_);
        v_r_1790_ = crate::leanh::lean_ctor_get(v_t_1783_, 4);
        crate::leanh::lean_inc(v_r_1790_);
        crate::leanh::lean_dec_ref_known(v_t_1783_, 5);
        v___x_1791_ = crate::leanh::lean_apply_6(
            v_h__2_1785_,
            v_size_1786_,
            v_k_1787_,
            v_v_1788_,
            v_l_1789_,
            v_r_1790_,
            crate::leanh::lean_box(0),
        );
        return v___x_1791_;
    } else {
        let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1785_);
        v___x_1792_ = crate::leanh::lean_apply_1(v_h__1_1784_, crate::leanh::lean_box(0));
        return v___x_1792_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__3_splitter(
    mut v_00_u03b1_1793_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1794_: *mut crate::leanh::LeanObject,
    mut v_motive_1795_: *mut crate::leanh::LeanObject,
    mut v_t_1796_: *mut crate::leanh::LeanObject,
    mut v_hl_1797_: *mut crate::leanh::LeanObject,
    mut v_h__1_1798_: *mut crate::leanh::LeanObject,
    mut v_h__2_1799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1796_) == 0 {
        let mut v_size_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1798_);
        v_size_1800_ = crate::leanh::lean_ctor_get(v_t_1796_, 0);
        crate::leanh::lean_inc(v_size_1800_);
        v_k_1801_ = crate::leanh::lean_ctor_get(v_t_1796_, 1);
        crate::leanh::lean_inc(v_k_1801_);
        v_v_1802_ = crate::leanh::lean_ctor_get(v_t_1796_, 2);
        crate::leanh::lean_inc(v_v_1802_);
        v_l_1803_ = crate::leanh::lean_ctor_get(v_t_1796_, 3);
        crate::leanh::lean_inc(v_l_1803_);
        v_r_1804_ = crate::leanh::lean_ctor_get(v_t_1796_, 4);
        crate::leanh::lean_inc(v_r_1804_);
        crate::leanh::lean_dec_ref_known(v_t_1796_, 5);
        v___x_1805_ = crate::leanh::lean_apply_6(
            v_h__2_1799_,
            v_size_1800_,
            v_k_1801_,
            v_v_1802_,
            v_l_1803_,
            v_r_1804_,
            crate::leanh::lean_box(0),
        );
        return v___x_1805_;
    } else {
        let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1799_);
        v___x_1806_ = crate::leanh::lean_apply_1(v_h__1_1798_, crate::leanh::lean_box(0));
        return v___x_1806_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter___redArg(
    mut v_x_1807_: *mut crate::leanh::LeanObject,
    mut v_h__1_1808_: *mut crate::leanh::LeanObject,
    mut v_h__2_1809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1807_) == 0 {
        let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1809_);
        v___x_1810_ = crate::leanh::lean_box(0);
        v___x_1811_ = crate::leanh::lean_apply_1(v_h__1_1808_, v___x_1810_);
        return v___x_1811_;
    } else {
        let mut v_val_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1808_);
        v_val_1812_ = crate::leanh::lean_ctor_get(v_x_1807_, 0);
        crate::leanh::lean_inc(v_val_1812_);
        crate::leanh::lean_dec_ref_known(v_x_1807_, 1);
        v___x_1813_ = crate::leanh::lean_apply_1(v_h__2_1809_, v_val_1812_);
        return v___x_1813_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter(
    mut v_00_u03b2_1814_: *mut crate::leanh::LeanObject,
    mut v_motive_1815_: *mut crate::leanh::LeanObject,
    mut v_x_1816_: *mut crate::leanh::LeanObject,
    mut v_h__1_1817_: *mut crate::leanh::LeanObject,
    mut v_h__2_1818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1816_) == 0 {
        let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1818_);
        v___x_1819_ = crate::leanh::lean_box(0);
        v___x_1820_ = crate::leanh::lean_apply_1(v_h__1_1817_, v___x_1819_);
        return v___x_1820_;
    } else {
        let mut v_val_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1817_);
        v_val_1821_ = crate::leanh::lean_ctor_get(v_x_1816_, 0);
        crate::leanh::lean_inc(v_val_1821_);
        crate::leanh::lean_dec_ref_known(v_x_1816_, 1);
        v___x_1822_ = crate::leanh::lean_apply_1(v_h__2_1818_, v_val_1821_);
        return v___x_1822_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(
    mut v_x_1823_: u8,
    mut v_h__1_1824_: *mut crate::leanh::LeanObject,
    mut v_h__2_1825_: *mut crate::leanh::LeanObject,
    mut v_h__3_1826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_1823_ {
        0 => {
            let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1826_);
            crate::leanh::lean_dec(v_h__2_1825_);
            v___x_1827_ = crate::leanh::lean_box(0);
            v___x_1828_ = crate::leanh::lean_apply_1(v_h__1_1824_, v___x_1827_);
            return v___x_1828_;
        }
        1 => {
            let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1825_);
            crate::leanh::lean_dec(v_h__1_1824_);
            v___x_1829_ = crate::leanh::lean_box(0);
            v___x_1830_ = crate::leanh::lean_apply_1(v_h__3_1826_, v___x_1829_);
            return v___x_1830_;
        }
        _ => {
            let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1826_);
            crate::leanh::lean_dec(v_h__1_1824_);
            v___x_1831_ = crate::leanh::lean_box(0);
            v___x_1832_ = crate::leanh::lean_apply_1(v_h__2_1825_, v___x_1831_);
            return v___x_1832_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(
    mut v_x_1833_: *mut crate::leanh::LeanObject,
    mut v_h__1_1834_: *mut crate::leanh::LeanObject,
    mut v_h__2_1835_: *mut crate::leanh::LeanObject,
    mut v_h__3_1836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_36__boxed_1837_: u8 = 0;
    let mut v_res_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_1837_ = (crate::leanh::lean_unbox(v_x_1833_) as u8);
    v_res_1838_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_36__boxed_1837_, v_h__1_1834_, v_h__2_1835_, v_h__3_1836_);
    return v_res_1838_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(
    mut v_motive_1839_: *mut crate::leanh::LeanObject,
    mut v_x_1840_: u8,
    mut v_h__1_1841_: *mut crate::leanh::LeanObject,
    mut v_h__2_1842_: *mut crate::leanh::LeanObject,
    mut v_h__3_1843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_1840_ {
        0 => {
            let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1843_);
            crate::leanh::lean_dec(v_h__2_1842_);
            v___x_1844_ = crate::leanh::lean_box(0);
            v___x_1845_ = crate::leanh::lean_apply_1(v_h__1_1841_, v___x_1844_);
            return v___x_1845_;
        }
        1 => {
            let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1842_);
            crate::leanh::lean_dec(v_h__1_1841_);
            v___x_1846_ = crate::leanh::lean_box(0);
            v___x_1847_ = crate::leanh::lean_apply_1(v_h__3_1843_, v___x_1846_);
            return v___x_1847_;
        }
        _ => {
            let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1843_);
            crate::leanh::lean_dec(v_h__1_1841_);
            v___x_1848_ = crate::leanh::lean_box(0);
            v___x_1849_ = crate::leanh::lean_apply_1(v_h__2_1842_, v___x_1848_);
            return v___x_1849_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(
    mut v_motive_1850_: *mut crate::leanh::LeanObject,
    mut v_x_1851_: *mut crate::leanh::LeanObject,
    mut v_h__1_1852_: *mut crate::leanh::LeanObject,
    mut v_h__2_1853_: *mut crate::leanh::LeanObject,
    mut v_h__3_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_51__boxed_1855_: u8 = 0;
    let mut v_res_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_51__boxed_1855_ = (crate::leanh::lean_unbox(v_x_1851_) as u8);
    v_res_1856_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(v_motive_1850_, v_x_51__boxed_1855_, v_h__1_1852_, v_h__2_1853_, v_h__3_1854_);
    return v_res_1856_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter___redArg(
    mut v_x_1857_: *mut crate::leanh::LeanObject,
    mut v_h__1_1858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1859_ = crate::leanh::lean_apply_4(
        v_h__1_1858_,
        v_x_1857_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1859_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter(
    mut v_00_u03b1_1860_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1861_: *mut crate::leanh::LeanObject,
    mut v_l_x27_1862_: *mut crate::leanh::LeanObject,
    mut v_motive_1863_: *mut crate::leanh::LeanObject,
    mut v_x_1864_: *mut crate::leanh::LeanObject,
    mut v_h__1_1865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1866_ = crate::leanh::lean_apply_4(
        v_h__1_1865_,
        v_x_1864_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1866_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter___boxed(
    mut v_00_u03b1_1867_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1868_: *mut crate::leanh::LeanObject,
    mut v_l_x27_1869_: *mut crate::leanh::LeanObject,
    mut v_motive_1870_: *mut crate::leanh::LeanObject,
    mut v_x_1871_: *mut crate::leanh::LeanObject,
    mut v_h__1_1872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1873_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter(v_00_u03b1_1867_, v_00_u03b2_1868_, v_l_x27_1869_, v_motive_1870_, v_x_1871_, v_h__1_1872_);
    crate::leanh::lean_dec(v_l_x27_1869_);
    return v_res_1873_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter___redArg(
    mut v_t_1874_: *mut crate::leanh::LeanObject,
    mut v_h__1_1875_: *mut crate::leanh::LeanObject,
    mut v_h__2_1876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1874_) == 0 {
        let mut v_size_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1875_);
        v_size_1877_ = crate::leanh::lean_ctor_get(v_t_1874_, 0);
        crate::leanh::lean_inc(v_size_1877_);
        v_k_1878_ = crate::leanh::lean_ctor_get(v_t_1874_, 1);
        crate::leanh::lean_inc(v_k_1878_);
        v_v_1879_ = crate::leanh::lean_ctor_get(v_t_1874_, 2);
        crate::leanh::lean_inc(v_v_1879_);
        v_l_1880_ = crate::leanh::lean_ctor_get(v_t_1874_, 3);
        crate::leanh::lean_inc(v_l_1880_);
        v_r_1881_ = crate::leanh::lean_ctor_get(v_t_1874_, 4);
        crate::leanh::lean_inc(v_r_1881_);
        crate::leanh::lean_dec_ref_known(v_t_1874_, 5);
        v___x_1882_ = crate::leanh::lean_apply_5(
            v_h__2_1876_,
            v_size_1877_,
            v_k_1878_,
            v_v_1879_,
            v_l_1880_,
            v_r_1881_,
        );
        return v___x_1882_;
    } else {
        let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1876_);
        v___x_1883_ = crate::leanh::lean_box(0);
        v___x_1884_ = crate::leanh::lean_apply_1(v_h__1_1875_, v___x_1883_);
        return v___x_1884_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter(
    mut v_00_u03b1_1885_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1886_: *mut crate::leanh::LeanObject,
    mut v_motive_1887_: *mut crate::leanh::LeanObject,
    mut v_t_1888_: *mut crate::leanh::LeanObject,
    mut v_h__1_1889_: *mut crate::leanh::LeanObject,
    mut v_h__2_1890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1888_) == 0 {
        let mut v_size_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1889_);
        v_size_1891_ = crate::leanh::lean_ctor_get(v_t_1888_, 0);
        crate::leanh::lean_inc(v_size_1891_);
        v_k_1892_ = crate::leanh::lean_ctor_get(v_t_1888_, 1);
        crate::leanh::lean_inc(v_k_1892_);
        v_v_1893_ = crate::leanh::lean_ctor_get(v_t_1888_, 2);
        crate::leanh::lean_inc(v_v_1893_);
        v_l_1894_ = crate::leanh::lean_ctor_get(v_t_1888_, 3);
        crate::leanh::lean_inc(v_l_1894_);
        v_r_1895_ = crate::leanh::lean_ctor_get(v_t_1888_, 4);
        crate::leanh::lean_inc(v_r_1895_);
        crate::leanh::lean_dec_ref_known(v_t_1888_, 5);
        v___x_1896_ = crate::leanh::lean_apply_5(
            v_h__2_1890_,
            v_size_1891_,
            v_k_1892_,
            v_v_1893_,
            v_l_1894_,
            v_r_1895_,
        );
        return v___x_1896_;
    } else {
        let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1890_);
        v___x_1897_ = crate::leanh::lean_box(0);
        v___x_1898_ = crate::leanh::lean_apply_1(v_h__1_1889_, v___x_1897_);
        return v___x_1898_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter___redArg(
    mut v_x_1899_: *mut crate::leanh::LeanObject,
    mut v_h__1_1900_: *mut crate::leanh::LeanObject,
    mut v_h__2_1901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1899_) == 0 {
        let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1900_);
        v___x_1902_ = crate::leanh::lean_box(0);
        v___x_1903_ = crate::leanh::lean_apply_1(v_h__2_1901_, v___x_1902_);
        return v___x_1903_;
    } else {
        let mut v_val_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1901_);
        v_val_1904_ = crate::leanh::lean_ctor_get(v_x_1899_, 0);
        crate::leanh::lean_inc(v_val_1904_);
        crate::leanh::lean_dec_ref_known(v_x_1899_, 1);
        v___x_1905_ = crate::leanh::lean_apply_1(v_h__1_1900_, v_val_1904_);
        return v___x_1905_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter(
    mut v_00_u03b1_1906_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1907_: *mut crate::leanh::LeanObject,
    mut v_motive_1908_: *mut crate::leanh::LeanObject,
    mut v_x_1909_: *mut crate::leanh::LeanObject,
    mut v_h__1_1910_: *mut crate::leanh::LeanObject,
    mut v_h__2_1911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1909_) == 0 {
        let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1910_);
        v___x_1912_ = crate::leanh::lean_box(0);
        v___x_1913_ = crate::leanh::lean_apply_1(v_h__2_1911_, v___x_1912_);
        return v___x_1913_;
    } else {
        let mut v_val_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1911_);
        v_val_1914_ = crate::leanh::lean_ctor_get(v_x_1909_, 0);
        crate::leanh::lean_inc(v_val_1914_);
        crate::leanh::lean_dec_ref_known(v_x_1909_, 1);
        v___x_1915_ = crate::leanh::lean_apply_1(v_h__1_1910_, v_val_1914_);
        return v___x_1915_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter___redArg(
    mut v_x_1916_: *mut crate::leanh::LeanObject,
    mut v_h__1_1917_: *mut crate::leanh::LeanObject,
    mut v_h__2_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1916_) == 0 {
        let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1917_);
        v___x_1919_ = crate::leanh::lean_box(0);
        v___x_1920_ = crate::leanh::lean_apply_1(v_h__2_1918_, v___x_1919_);
        return v___x_1920_;
    } else {
        let mut v_val_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1918_);
        v_val_1921_ = crate::leanh::lean_ctor_get(v_x_1916_, 0);
        crate::leanh::lean_inc(v_val_1921_);
        crate::leanh::lean_dec_ref_known(v_x_1916_, 1);
        v___x_1922_ = crate::leanh::lean_apply_1(v_h__1_1917_, v_val_1921_);
        return v___x_1922_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter(
    mut v_00_u03b1_1923_: *mut crate::leanh::LeanObject,
    mut v_motive_1924_: *mut crate::leanh::LeanObject,
    mut v_x_1925_: *mut crate::leanh::LeanObject,
    mut v_h__1_1926_: *mut crate::leanh::LeanObject,
    mut v_h__2_1927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1925_) == 0 {
        let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1926_);
        v___x_1928_ = crate::leanh::lean_box(0);
        v___x_1929_ = crate::leanh::lean_apply_1(v_h__2_1927_, v___x_1928_);
        return v___x_1929_;
    } else {
        let mut v_val_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1927_);
        v_val_1930_ = crate::leanh::lean_ctor_get(v_x_1925_, 0);
        crate::leanh::lean_inc(v_val_1930_);
        crate::leanh::lean_dec_ref_known(v_x_1925_, 1);
        v___x_1931_ = crate::leanh::lean_apply_1(v_h__1_1926_, v_val_1930_);
        return v___x_1931_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_1932_: *mut crate::leanh::LeanObject,
    mut v_h__1_1933_: *mut crate::leanh::LeanObject,
    mut v_h__2_1934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1932_) == 0 {
        let mut v_a_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1934_);
        v_a_1935_ = crate::leanh::lean_ctor_get(v_x_1932_, 0);
        crate::leanh::lean_inc(v_a_1935_);
        crate::leanh::lean_dec_ref_known(v_x_1932_, 1);
        v___x_1936_ = crate::leanh::lean_apply_1(v_h__1_1933_, v_a_1935_);
        return v___x_1936_;
    } else {
        let mut v_a_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1933_);
        v_a_1937_ = crate::leanh::lean_ctor_get(v_x_1932_, 0);
        crate::leanh::lean_inc(v_a_1937_);
        crate::leanh::lean_dec_ref_known(v_x_1932_, 1);
        v___x_1938_ = crate::leanh::lean_apply_1(v_h__2_1934_, v_a_1937_);
        return v___x_1938_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_1939_: *mut crate::leanh::LeanObject,
    mut v_motive_1940_: *mut crate::leanh::LeanObject,
    mut v_x_1941_: *mut crate::leanh::LeanObject,
    mut v_h__1_1942_: *mut crate::leanh::LeanObject,
    mut v_h__2_1943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1941_) == 0 {
        let mut v_a_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1943_);
        v_a_1944_ = crate::leanh::lean_ctor_get(v_x_1941_, 0);
        crate::leanh::lean_inc(v_a_1944_);
        crate::leanh::lean_dec_ref_known(v_x_1941_, 1);
        v___x_1945_ = crate::leanh::lean_apply_1(v_h__1_1942_, v_a_1944_);
        return v___x_1945_;
    } else {
        let mut v_a_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1942_);
        v_a_1946_ = crate::leanh::lean_ctor_get(v_x_1941_, 0);
        crate::leanh::lean_inc(v_a_1946_);
        crate::leanh::lean_dec_ref_known(v_x_1941_, 1);
        v___x_1947_ = crate::leanh::lean_apply_1(v_h__2_1943_, v_a_1946_);
        return v___x_1947_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(
    mut v_x_1948_: *mut crate::leanh::LeanObject,
    mut v_h__1_1949_: *mut crate::leanh::LeanObject,
    mut v_h__2_1950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1948_) == 0 {
        let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1949_);
        v___x_1951_ = crate::leanh::lean_box(0);
        v___x_1952_ = crate::leanh::lean_apply_1(v_h__2_1950_, v___x_1951_);
        return v___x_1952_;
    } else {
        let mut v_val_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1950_);
        v_val_1953_ = crate::leanh::lean_ctor_get(v_x_1948_, 0);
        crate::leanh::lean_inc(v_val_1953_);
        crate::leanh::lean_dec_ref_known(v_x_1948_, 1);
        v___x_1954_ = crate::leanh::lean_apply_1(v_h__1_1949_, v_val_1953_);
        return v___x_1954_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter(
    mut v_00_u03b1_1955_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1956_: *mut crate::leanh::LeanObject,
    mut v_motive_1957_: *mut crate::leanh::LeanObject,
    mut v_x_1958_: *mut crate::leanh::LeanObject,
    mut v_h__1_1959_: *mut crate::leanh::LeanObject,
    mut v_h__2_1960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1958_) == 0 {
        let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1959_);
        v___x_1961_ = crate::leanh::lean_box(0);
        v___x_1962_ = crate::leanh::lean_apply_1(v_h__2_1960_, v___x_1961_);
        return v___x_1962_;
    } else {
        let mut v_val_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1960_);
        v_val_1963_ = crate::leanh::lean_ctor_get(v_x_1958_, 0);
        crate::leanh::lean_inc(v_val_1963_);
        crate::leanh::lean_dec_ref_known(v_x_1958_, 1);
        v___x_1964_ = crate::leanh::lean_apply_1(v_h__1_1959_, v_val_1963_);
        return v___x_1964_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(
    mut v_x_1965_: u8,
    mut v_h__1_1966_: *mut crate::leanh::LeanObject,
    mut v_h__2_1967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_1965_ == 0 {
        let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1966_);
        v___x_1968_ = crate::leanh::lean_box(0);
        v___x_1969_ = crate::leanh::lean_apply_1(v_h__2_1967_, v___x_1968_);
        return v___x_1969_;
    } else {
        let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1967_);
        v___x_1970_ = crate::leanh::lean_box(0);
        v___x_1971_ = crate::leanh::lean_apply_1(v_h__1_1966_, v___x_1970_);
        return v___x_1971_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_1972_: *mut crate::leanh::LeanObject,
    mut v_h__1_1973_: *mut crate::leanh::LeanObject,
    mut v_h__2_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_1975_: u8 = 0;
    let mut v_res_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1975_ = (crate::leanh::lean_unbox(v_x_1972_) as u8);
    v_res_1976_ =
        l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(
            v_x_26__boxed_1975_,
            v_h__1_1973_,
            v_h__2_1974_,
        );
    return v_res_1976_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter(
    mut v_motive_1977_: *mut crate::leanh::LeanObject,
    mut v_x_1978_: u8,
    mut v_h__1_1979_: *mut crate::leanh::LeanObject,
    mut v_h__2_1980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_1978_ == 0 {
        let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1979_);
        v___x_1981_ = crate::leanh::lean_box(0);
        v___x_1982_ = crate::leanh::lean_apply_1(v_h__2_1980_, v___x_1981_);
        return v___x_1982_;
    } else {
        let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1980_);
        v___x_1983_ = crate::leanh::lean_box(0);
        v___x_1984_ = crate::leanh::lean_apply_1(v_h__1_1979_, v___x_1983_);
        return v___x_1984_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___boxed(
    mut v_motive_1985_: *mut crate::leanh::LeanObject,
    mut v_x_1986_: *mut crate::leanh::LeanObject,
    mut v_h__1_1987_: *mut crate::leanh::LeanObject,
    mut v_h__2_1988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_37__boxed_1989_: u8 = 0;
    let mut v_res_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_1989_ = (crate::leanh::lean_unbox(v_x_1986_) as u8);
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
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Impl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(
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
pub unsafe fn initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Internal_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Internal_List_Associative(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Impl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Subtype_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(builtin);
}
