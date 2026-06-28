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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_apply_4,
    lean_apply_5, lean_apply_6, lean_apply_7, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
    lean_unbox,
};
pub unsafe fn l_Std_DTreeMap_Internal_Impl_instCoeTypeForall__1(
    mut v_00_u03b1_996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    v___x_997_ = lean_box(0);
    return v___x_997_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter___redArg(
    mut v_l_998_: *mut LeanObject,
    mut v_h__1_999_: *mut LeanObject,
    mut v_h__2_1000_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_998_) == 0 {
        let mut v_size_1001_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1002_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1003_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1004_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1005_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_999_);
        v_size_1001_ = lean_ctor_get(v_l_998_, 0);
        lean_inc(v_size_1001_);
        v_k_1002_ = lean_ctor_get(v_l_998_, 1);
        lean_inc(v_k_1002_);
        v_v_1003_ = lean_ctor_get(v_l_998_, 2);
        lean_inc(v_v_1003_);
        v_l_1004_ = lean_ctor_get(v_l_998_, 3);
        lean_inc(v_l_1004_);
        v_r_1005_ = lean_ctor_get(v_l_998_, 4);
        lean_inc(v_r_1005_);
        lean_dec_ref_known(v_l_998_, 5);
        v___x_1006_ = lean_apply_5(
            v_h__2_1000_,
            v_size_1001_,
            v_k_1002_,
            v_v_1003_,
            v_l_1004_,
            v_r_1005_,
        );
        return v___x_1006_;
    } else {
        let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1000_);
        v___x_1007_ = lean_box(0);
        v___x_1008_ = lean_apply_1(v_h__1_999_, v___x_1007_);
        return v___x_1008_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter(
    mut v_00_u03b1_1009_: *mut LeanObject,
    mut v_00_u03b2_1010_: *mut LeanObject,
    mut v_motive_1011_: *mut LeanObject,
    mut v_l_1012_: *mut LeanObject,
    mut v_h__1_1013_: *mut LeanObject,
    mut v_h__2_1014_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_1012_) == 0 {
        let mut v_size_1015_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1016_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1017_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1018_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1019_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1013_);
        v_size_1015_ = lean_ctor_get(v_l_1012_, 0);
        lean_inc(v_size_1015_);
        v_k_1016_ = lean_ctor_get(v_l_1012_, 1);
        lean_inc(v_k_1016_);
        v_v_1017_ = lean_ctor_get(v_l_1012_, 2);
        lean_inc(v_v_1017_);
        v_l_1018_ = lean_ctor_get(v_l_1012_, 3);
        lean_inc(v_l_1018_);
        v_r_1019_ = lean_ctor_get(v_l_1012_, 4);
        lean_inc(v_r_1019_);
        lean_dec_ref_known(v_l_1012_, 5);
        v___x_1020_ = lean_apply_5(
            v_h__2_1014_,
            v_size_1015_,
            v_k_1016_,
            v_v_1017_,
            v_l_1018_,
            v_r_1019_,
        );
        return v___x_1020_;
    } else {
        let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1014_);
        v___x_1021_ = lean_box(0);
        v___x_1022_ = lean_apply_1(v_h__1_1013_, v___x_1021_);
        return v___x_1022_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___redArg(
    mut v_r_1023_: *mut LeanObject,
    mut v_h__1_1024_: *mut LeanObject,
    mut v_h__2_1025_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_1023_) == 0 {
        let mut v_size_1026_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1027_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1028_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1029_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1030_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1024_);
        v_size_1026_ = lean_ctor_get(v_r_1023_, 0);
        lean_inc(v_size_1026_);
        v_k_1027_ = lean_ctor_get(v_r_1023_, 1);
        lean_inc(v_k_1027_);
        v_v_1028_ = lean_ctor_get(v_r_1023_, 2);
        lean_inc(v_v_1028_);
        v_l_1029_ = lean_ctor_get(v_r_1023_, 3);
        lean_inc(v_l_1029_);
        v_r_1030_ = lean_ctor_get(v_r_1023_, 4);
        lean_inc(v_r_1030_);
        lean_dec_ref_known(v_r_1023_, 5);
        v___x_1031_ = lean_apply_6(
            v_h__2_1025_,
            v_size_1026_,
            v_k_1027_,
            v_v_1028_,
            v_l_1029_,
            v_r_1030_,
            lean_box(0),
        );
        return v___x_1031_;
    } else {
        let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1025_);
        v___x_1032_ = lean_apply_1(v_h__1_1024_, lean_box(0));
        return v___x_1032_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(
    mut v_00_u03b1_1033_: *mut LeanObject,
    mut v_00_u03b2_1034_: *mut LeanObject,
    mut v_l_1035_: *mut LeanObject,
    mut v_motive_1036_: *mut LeanObject,
    mut v_r_1037_: *mut LeanObject,
    mut v_h_1038_: *mut LeanObject,
    mut v_h__1_1039_: *mut LeanObject,
    mut v_h__2_1040_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_1037_) == 0 {
        let mut v_size_1041_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1042_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1043_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1044_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1045_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1039_);
        v_size_1041_ = lean_ctor_get(v_r_1037_, 0);
        lean_inc(v_size_1041_);
        v_k_1042_ = lean_ctor_get(v_r_1037_, 1);
        lean_inc(v_k_1042_);
        v_v_1043_ = lean_ctor_get(v_r_1037_, 2);
        lean_inc(v_v_1043_);
        v_l_1044_ = lean_ctor_get(v_r_1037_, 3);
        lean_inc(v_l_1044_);
        v_r_1045_ = lean_ctor_get(v_r_1037_, 4);
        lean_inc(v_r_1045_);
        lean_dec_ref_known(v_r_1037_, 5);
        v___x_1046_ = lean_apply_6(
            v_h__2_1040_,
            v_size_1041_,
            v_k_1042_,
            v_v_1043_,
            v_l_1044_,
            v_r_1045_,
            lean_box(0),
        );
        return v___x_1046_;
    } else {
        let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1040_);
        v___x_1047_ = lean_apply_1(v_h__1_1039_, lean_box(0));
        return v___x_1047_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___boxed(
    mut v_00_u03b1_1048_: *mut LeanObject,
    mut v_00_u03b2_1049_: *mut LeanObject,
    mut v_l_1050_: *mut LeanObject,
    mut v_motive_1051_: *mut LeanObject,
    mut v_r_1052_: *mut LeanObject,
    mut v_h_1053_: *mut LeanObject,
    mut v_h__1_1054_: *mut LeanObject,
    mut v_h__2_1055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1056_: *mut LeanObject = core::ptr::null_mut();
    v_res_1056_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(v_00_u03b1_1048_, v_00_u03b2_1049_, v_l_1050_, v_motive_1051_, v_r_1052_, v_h_1053_, v_h__1_1054_, v_h__2_1055_);
    lean_dec(v_l_1050_);
    return v_res_1056_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___redArg(
    mut v_l_1057_: *mut LeanObject,
    mut v_h__1_1058_: *mut LeanObject,
    mut v_h__2_1059_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_1057_) == 0 {
        let mut v_size_1060_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1061_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1062_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1063_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1064_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1058_);
        v_size_1060_ = lean_ctor_get(v_l_1057_, 0);
        lean_inc(v_size_1060_);
        v_k_1061_ = lean_ctor_get(v_l_1057_, 1);
        lean_inc(v_k_1061_);
        v_v_1062_ = lean_ctor_get(v_l_1057_, 2);
        lean_inc(v_v_1062_);
        v_l_1063_ = lean_ctor_get(v_l_1057_, 3);
        lean_inc(v_l_1063_);
        v_r_1064_ = lean_ctor_get(v_l_1057_, 4);
        lean_inc(v_r_1064_);
        lean_dec_ref_known(v_l_1057_, 5);
        v___x_1065_ = lean_apply_7(
            v_h__2_1059_,
            v_size_1060_,
            v_k_1061_,
            v_v_1062_,
            v_l_1063_,
            v_r_1064_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1065_;
    } else {
        let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1059_);
        v___x_1066_ = lean_apply_2(v_h__1_1058_, lean_box(0), lean_box(0));
        return v___x_1066_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(
    mut v_00_u03b1_1067_: *mut LeanObject,
    mut v_00_u03b2_1068_: *mut LeanObject,
    mut v_r_1069_: *mut LeanObject,
    mut v_motive_1070_: *mut LeanObject,
    mut v_l_1071_: *mut LeanObject,
    mut v_h_1072_: *mut LeanObject,
    mut v_h_1073_: *mut LeanObject,
    mut v_h__1_1074_: *mut LeanObject,
    mut v_h__2_1075_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_1071_) == 0 {
        let mut v_size_1076_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1077_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1078_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1079_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1080_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1074_);
        v_size_1076_ = lean_ctor_get(v_l_1071_, 0);
        lean_inc(v_size_1076_);
        v_k_1077_ = lean_ctor_get(v_l_1071_, 1);
        lean_inc(v_k_1077_);
        v_v_1078_ = lean_ctor_get(v_l_1071_, 2);
        lean_inc(v_v_1078_);
        v_l_1079_ = lean_ctor_get(v_l_1071_, 3);
        lean_inc(v_l_1079_);
        v_r_1080_ = lean_ctor_get(v_l_1071_, 4);
        lean_inc(v_r_1080_);
        lean_dec_ref_known(v_l_1071_, 5);
        v___x_1081_ = lean_apply_7(
            v_h__2_1075_,
            v_size_1076_,
            v_k_1077_,
            v_v_1078_,
            v_l_1079_,
            v_r_1080_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1081_;
    } else {
        let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1075_);
        v___x_1082_ = lean_apply_2(v_h__1_1074_, lean_box(0), lean_box(0));
        return v___x_1082_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___boxed(
    mut v_00_u03b1_1083_: *mut LeanObject,
    mut v_00_u03b2_1084_: *mut LeanObject,
    mut v_r_1085_: *mut LeanObject,
    mut v_motive_1086_: *mut LeanObject,
    mut v_l_1087_: *mut LeanObject,
    mut v_h_1088_: *mut LeanObject,
    mut v_h_1089_: *mut LeanObject,
    mut v_h__1_1090_: *mut LeanObject,
    mut v_h__2_1091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1092_: *mut LeanObject = core::ptr::null_mut();
    v_res_1092_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(v_00_u03b1_1083_, v_00_u03b2_1084_, v_r_1085_, v_motive_1086_, v_l_1087_, v_h_1088_, v_h_1089_, v_h__1_1090_, v_h__2_1091_);
    lean_dec(v_r_1085_);
    return v_res_1092_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(
    mut v_r_1093_: *mut LeanObject,
    mut v_h__1_1094_: *mut LeanObject,
    mut v_h__2_1095_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_1093_) == 0 {
        let mut v_size_1096_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1097_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1098_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1099_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1100_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1094_);
        v_size_1096_ = lean_ctor_get(v_r_1093_, 0);
        lean_inc(v_size_1096_);
        v_k_1097_ = lean_ctor_get(v_r_1093_, 1);
        lean_inc(v_k_1097_);
        v_v_1098_ = lean_ctor_get(v_r_1093_, 2);
        lean_inc(v_v_1098_);
        v_l_1099_ = lean_ctor_get(v_r_1093_, 3);
        lean_inc(v_l_1099_);
        v_r_1100_ = lean_ctor_get(v_r_1093_, 4);
        lean_inc(v_r_1100_);
        lean_dec_ref_known(v_r_1093_, 5);
        v___x_1101_ = lean_apply_7(
            v_h__2_1095_,
            v_size_1096_,
            v_k_1097_,
            v_v_1098_,
            v_l_1099_,
            v_r_1100_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1101_;
    } else {
        let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1095_);
        v___x_1102_ = lean_apply_2(v_h__1_1094_, lean_box(0), lean_box(0));
        return v___x_1102_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(
    mut v_00_u03b1_1103_: *mut LeanObject,
    mut v_00_u03b2_1104_: *mut LeanObject,
    mut v_motive_1105_: *mut LeanObject,
    mut v_r_1106_: *mut LeanObject,
    mut v_hr_1107_: *mut LeanObject,
    mut v_h__1_1108_: *mut LeanObject,
    mut v_h__2_1109_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_1106_) == 0 {
        let mut v_size_1110_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1111_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1112_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1113_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1114_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1108_);
        v_size_1110_ = lean_ctor_get(v_r_1106_, 0);
        lean_inc(v_size_1110_);
        v_k_1111_ = lean_ctor_get(v_r_1106_, 1);
        lean_inc(v_k_1111_);
        v_v_1112_ = lean_ctor_get(v_r_1106_, 2);
        lean_inc(v_v_1112_);
        v_l_1113_ = lean_ctor_get(v_r_1106_, 3);
        lean_inc(v_l_1113_);
        v_r_1114_ = lean_ctor_get(v_r_1106_, 4);
        lean_inc(v_r_1114_);
        lean_dec_ref_known(v_r_1106_, 5);
        v___x_1115_ = lean_apply_7(
            v_h__2_1109_,
            v_size_1110_,
            v_k_1111_,
            v_v_1112_,
            v_l_1113_,
            v_r_1114_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1115_;
    } else {
        let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1109_);
        v___x_1116_ = lean_apply_2(v_h__1_1108_, lean_box(0), lean_box(0));
        return v___x_1116_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___redArg(
    mut v_x_1117_: *mut LeanObject,
    mut v_h__1_1118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    v___x_1119_ = lean_apply_3(v_h__1_1118_, v_x_1117_, lean_box(0), lean_box(0));
    return v___x_1119_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(
    mut v_00_u03b1_1120_: *mut LeanObject,
    mut v_00_u03b2_1121_: *mut LeanObject,
    mut v_l_1122_: *mut LeanObject,
    mut v_l_x27_x27_1123_: *mut LeanObject,
    mut v_motive_1124_: *mut LeanObject,
    mut v_x_1125_: *mut LeanObject,
    mut v_h__1_1126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    v___x_1127_ = lean_apply_3(v_h__1_1126_, v_x_1125_, lean_box(0), lean_box(0));
    return v___x_1127_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter___boxed(
    mut v_00_u03b1_1128_: *mut LeanObject,
    mut v_00_u03b2_1129_: *mut LeanObject,
    mut v_l_1130_: *mut LeanObject,
    mut v_l_x27_x27_1131_: *mut LeanObject,
    mut v_motive_1132_: *mut LeanObject,
    mut v_x_1133_: *mut LeanObject,
    mut v_h__1_1134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1135_: *mut LeanObject = core::ptr::null_mut();
    v_res_1135_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__1_splitter(v_00_u03b1_1128_, v_00_u03b2_1129_, v_l_1130_, v_l_x27_x27_1131_, v_motive_1132_, v_x_1133_, v_h__1_1134_);
    lean_dec(v_l_x27_x27_1131_);
    lean_dec(v_l_1130_);
    return v_res_1135_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___redArg(
    mut v_x_1136_: *mut LeanObject,
    mut v_h__1_1137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    v___x_1138_ = lean_apply_3(v_h__1_1137_, v_x_1136_, lean_box(0), lean_box(0));
    return v___x_1138_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(
    mut v_00_u03b1_1139_: *mut LeanObject,
    mut v_00_u03b2_1140_: *mut LeanObject,
    mut v_r_1141_: *mut LeanObject,
    mut v_r_x27_1142_: *mut LeanObject,
    mut v_motive_1143_: *mut LeanObject,
    mut v_x_1144_: *mut LeanObject,
    mut v_h__1_1145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    v___x_1146_ = lean_apply_3(v_h__1_1145_, v_x_1144_, lean_box(0), lean_box(0));
    return v___x_1146_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter___boxed(
    mut v_00_u03b1_1147_: *mut LeanObject,
    mut v_00_u03b2_1148_: *mut LeanObject,
    mut v_r_1149_: *mut LeanObject,
    mut v_r_x27_1150_: *mut LeanObject,
    mut v_motive_1151_: *mut LeanObject,
    mut v_x_1152_: *mut LeanObject,
    mut v_h__1_1153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1154_: *mut LeanObject = core::ptr::null_mut();
    v_res_1154_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link2_match__3_splitter(v_00_u03b1_1147_, v_00_u03b2_1148_, v_r_1149_, v_r_x27_1150_, v_motive_1151_, v_x_1152_, v_h__1_1153_);
    lean_dec(v_r_x27_1150_);
    lean_dec(v_r_1149_);
    return v_res_1154_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(
    mut v_t_1155_: *mut LeanObject,
    mut v_h__1_1156_: *mut LeanObject,
    mut v_h__2_1157_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1155_) == 0 {
        let mut v_size_1158_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1159_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1160_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1161_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1162_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1156_);
        v_size_1158_ = lean_ctor_get(v_t_1155_, 0);
        lean_inc(v_size_1158_);
        v_k_1159_ = lean_ctor_get(v_t_1155_, 1);
        lean_inc(v_k_1159_);
        v_v_1160_ = lean_ctor_get(v_t_1155_, 2);
        lean_inc(v_v_1160_);
        v_l_1161_ = lean_ctor_get(v_t_1155_, 3);
        lean_inc(v_l_1161_);
        v_r_1162_ = lean_ctor_get(v_t_1155_, 4);
        lean_inc(v_r_1162_);
        lean_dec_ref_known(v_t_1155_, 5);
        v___x_1163_ = lean_apply_6(
            v_h__2_1157_,
            v_size_1158_,
            v_k_1159_,
            v_v_1160_,
            v_l_1161_,
            v_r_1162_,
            lean_box(0),
        );
        return v___x_1163_;
    } else {
        let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1157_);
        v___x_1164_ = lean_apply_1(v_h__1_1156_, lean_box(0));
        return v___x_1164_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(
    mut v_00_u03b1_1165_: *mut LeanObject,
    mut v_00_u03b2_1166_: *mut LeanObject,
    mut v_motive_1167_: *mut LeanObject,
    mut v_t_1168_: *mut LeanObject,
    mut v_hr_1169_: *mut LeanObject,
    mut v_h__1_1170_: *mut LeanObject,
    mut v_h__2_1171_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1168_) == 0 {
        let mut v_size_1172_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1173_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1174_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1175_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1170_);
        v_size_1172_ = lean_ctor_get(v_t_1168_, 0);
        lean_inc(v_size_1172_);
        v_k_1173_ = lean_ctor_get(v_t_1168_, 1);
        lean_inc(v_k_1173_);
        v_v_1174_ = lean_ctor_get(v_t_1168_, 2);
        lean_inc(v_v_1174_);
        v_l_1175_ = lean_ctor_get(v_t_1168_, 3);
        lean_inc(v_l_1175_);
        v_r_1176_ = lean_ctor_get(v_t_1168_, 4);
        lean_inc(v_r_1176_);
        lean_dec_ref_known(v_t_1168_, 5);
        v___x_1177_ = lean_apply_6(
            v_h__2_1171_,
            v_size_1172_,
            v_k_1173_,
            v_v_1174_,
            v_l_1175_,
            v_r_1176_,
            lean_box(0),
        );
        return v___x_1177_;
    } else {
        let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1171_);
        v___x_1178_ = lean_apply_1(v_h__1_1170_, lean_box(0));
        return v___x_1178_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___redArg(
    mut v_x_1179_: *mut LeanObject,
    mut v_h__1_1180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    v___x_1181_ = lean_apply_3(v_h__1_1180_, v_x_1179_, lean_box(0), lean_box(0));
    return v___x_1181_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(
    mut v_00_u03b1_1182_: *mut LeanObject,
    mut v_00_u03b2_1183_: *mut LeanObject,
    mut v_szl_1184_: *mut LeanObject,
    mut v_k_x27_1185_: *mut LeanObject,
    mut v_v_x27_1186_: *mut LeanObject,
    mut v_l_x27_1187_: *mut LeanObject,
    mut v_r_x27_1188_: *mut LeanObject,
    mut v_l_x27_x27_1189_: *mut LeanObject,
    mut v_motive_1190_: *mut LeanObject,
    mut v_x_1191_: *mut LeanObject,
    mut v_h__1_1192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    v___x_1193_ = lean_apply_3(v_h__1_1192_, v_x_1191_, lean_box(0), lean_box(0));
    return v___x_1193_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter___boxed(
    mut v_00_u03b1_1194_: *mut LeanObject,
    mut v_00_u03b2_1195_: *mut LeanObject,
    mut v_szl_1196_: *mut LeanObject,
    mut v_k_x27_1197_: *mut LeanObject,
    mut v_v_x27_1198_: *mut LeanObject,
    mut v_l_x27_1199_: *mut LeanObject,
    mut v_r_x27_1200_: *mut LeanObject,
    mut v_l_x27_x27_1201_: *mut LeanObject,
    mut v_motive_1202_: *mut LeanObject,
    mut v_x_1203_: *mut LeanObject,
    mut v_h__1_1204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1205_: *mut LeanObject = core::ptr::null_mut();
    v_res_1205_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__1_splitter(v_00_u03b1_1194_, v_00_u03b2_1195_, v_szl_1196_, v_k_x27_1197_, v_v_x27_1198_, v_l_x27_1199_, v_r_x27_1200_, v_l_x27_x27_1201_, v_motive_1202_, v_x_1203_, v_h__1_1204_);
    lean_dec(v_l_x27_x27_1201_);
    lean_dec(v_r_x27_1200_);
    lean_dec(v_l_x27_1199_);
    lean_dec(v_v_x27_1198_);
    lean_dec(v_k_x27_1197_);
    lean_dec(v_szl_1196_);
    return v_res_1205_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___redArg(
    mut v_x_1206_: *mut LeanObject,
    mut v_h__1_1207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    v___x_1208_ = lean_apply_3(v_h__1_1207_, v_x_1206_, lean_box(0), lean_box(0));
    return v___x_1208_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(
    mut v_00_u03b1_1209_: *mut LeanObject,
    mut v_00_u03b2_1210_: *mut LeanObject,
    mut v_r_x27_1211_: *mut LeanObject,
    mut v_szr_1212_: *mut LeanObject,
    mut v_k_x27_x27_1213_: *mut LeanObject,
    mut v_v_x27_x27_1214_: *mut LeanObject,
    mut v_l_x27_x27_1215_: *mut LeanObject,
    mut v_r_x27_x27_1216_: *mut LeanObject,
    mut v_motive_1217_: *mut LeanObject,
    mut v_x_1218_: *mut LeanObject,
    mut v_h__1_1219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    v___x_1220_ = lean_apply_3(v_h__1_1219_, v_x_1218_, lean_box(0), lean_box(0));
    return v___x_1220_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter___boxed(
    mut v_00_u03b1_1221_: *mut LeanObject,
    mut v_00_u03b2_1222_: *mut LeanObject,
    mut v_r_x27_1223_: *mut LeanObject,
    mut v_szr_1224_: *mut LeanObject,
    mut v_k_x27_x27_1225_: *mut LeanObject,
    mut v_v_x27_x27_1226_: *mut LeanObject,
    mut v_l_x27_x27_1227_: *mut LeanObject,
    mut v_r_x27_x27_1228_: *mut LeanObject,
    mut v_motive_1229_: *mut LeanObject,
    mut v_x_1230_: *mut LeanObject,
    mut v_h__1_1231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1232_: *mut LeanObject = core::ptr::null_mut();
    v_res_1232_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_link_match__3_splitter(v_00_u03b1_1221_, v_00_u03b2_1222_, v_r_x27_1223_, v_szr_1224_, v_k_x27_x27_1225_, v_v_x27_x27_1226_, v_l_x27_x27_1227_, v_r_x27_x27_1228_, v_motive_1229_, v_x_1230_, v_h__1_1231_);
    lean_dec(v_r_x27_x27_1228_);
    lean_dec(v_l_x27_x27_1227_);
    lean_dec(v_v_x27_x27_1226_);
    lean_dec(v_k_x27_x27_1225_);
    lean_dec(v_szr_1224_);
    lean_dec(v_r_x27_1223_);
    return v_res_1232_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(
    mut v_l_1233_: *mut LeanObject,
    mut v_h__1_1234_: *mut LeanObject,
    mut v_h__2_1235_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_1233_) == 0 {
        let mut v_size_1236_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1237_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1238_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1239_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1234_);
        v_size_1236_ = lean_ctor_get(v_l_1233_, 0);
        lean_inc(v_size_1236_);
        v_k_1237_ = lean_ctor_get(v_l_1233_, 1);
        lean_inc(v_k_1237_);
        v_v_1238_ = lean_ctor_get(v_l_1233_, 2);
        lean_inc(v_v_1238_);
        v_l_1239_ = lean_ctor_get(v_l_1233_, 3);
        lean_inc(v_l_1239_);
        v_r_1240_ = lean_ctor_get(v_l_1233_, 4);
        lean_inc(v_r_1240_);
        lean_dec_ref_known(v_l_1233_, 5);
        v___x_1241_ = lean_apply_6(
            v_h__2_1235_,
            v_size_1236_,
            v_k_1237_,
            v_v_1238_,
            v_l_1239_,
            v_r_1240_,
            lean_box(0),
        );
        return v___x_1241_;
    } else {
        let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1235_);
        v___x_1242_ = lean_apply_1(v_h__1_1234_, lean_box(0));
        return v___x_1242_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(
    mut v_00_u03b1_1243_: *mut LeanObject,
    mut v_00_u03b2_1244_: *mut LeanObject,
    mut v_motive_1245_: *mut LeanObject,
    mut v_l_1246_: *mut LeanObject,
    mut v_hl_1247_: *mut LeanObject,
    mut v_h__1_1248_: *mut LeanObject,
    mut v_h__2_1249_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_1246_) == 0 {
        let mut v_size_1250_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1251_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1252_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1253_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1254_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1248_);
        v_size_1250_ = lean_ctor_get(v_l_1246_, 0);
        lean_inc(v_size_1250_);
        v_k_1251_ = lean_ctor_get(v_l_1246_, 1);
        lean_inc(v_k_1251_);
        v_v_1252_ = lean_ctor_get(v_l_1246_, 2);
        lean_inc(v_v_1252_);
        v_l_1253_ = lean_ctor_get(v_l_1246_, 3);
        lean_inc(v_l_1253_);
        v_r_1254_ = lean_ctor_get(v_l_1246_, 4);
        lean_inc(v_r_1254_);
        lean_dec_ref_known(v_l_1246_, 5);
        v___x_1255_ = lean_apply_6(
            v_h__2_1249_,
            v_size_1250_,
            v_k_1251_,
            v_v_1252_,
            v_l_1253_,
            v_r_1254_,
            lean_box(0),
        );
        return v___x_1255_;
    } else {
        let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1249_);
        v___x_1256_ = lean_apply_1(v_h__1_1248_, lean_box(0));
        return v___x_1256_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(
    mut v_x_1257_: *mut LeanObject,
    mut v_h__1_1258_: *mut LeanObject,
    mut v_h__2_1259_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1257_) == 0 {
        let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1259_);
        v___x_1260_ = lean_box(0);
        v___x_1261_ = lean_apply_1(v_h__1_1258_, v___x_1260_);
        return v___x_1261_;
    } else {
        let mut v_val_1262_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_1263_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_1264_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1258_);
        v_val_1262_ = lean_ctor_get(v_x_1257_, 0);
        lean_inc(v_val_1262_);
        lean_dec_ref_known(v_x_1257_, 1);
        v_fst_1263_ = lean_ctor_get(v_val_1262_, 0);
        lean_inc(v_fst_1263_);
        v_snd_1264_ = lean_ctor_get(v_val_1262_, 1);
        lean_inc(v_snd_1264_);
        lean_dec(v_val_1262_);
        v___x_1265_ = lean_apply_2(v_h__2_1259_, v_fst_1263_, v_snd_1264_);
        return v___x_1265_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(
    mut v_00_u03b1_1266_: *mut LeanObject,
    mut v_00_u03b2_1267_: *mut LeanObject,
    mut v_motive_1268_: *mut LeanObject,
    mut v_x_1269_: *mut LeanObject,
    mut v_h__1_1270_: *mut LeanObject,
    mut v_h__2_1271_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1269_) == 0 {
        let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1271_);
        v___x_1272_ = lean_box(0);
        v___x_1273_ = lean_apply_1(v_h__1_1270_, v___x_1272_);
        return v___x_1273_;
    } else {
        let mut v_val_1274_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_1275_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_1276_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1270_);
        v_val_1274_ = lean_ctor_get(v_x_1269_, 0);
        lean_inc(v_val_1274_);
        lean_dec_ref_known(v_x_1269_, 1);
        v_fst_1275_ = lean_ctor_get(v_val_1274_, 0);
        lean_inc(v_fst_1275_);
        v_snd_1276_ = lean_ctor_get(v_val_1274_, 1);
        lean_inc(v_snd_1276_);
        lean_dec(v_val_1274_);
        v___x_1277_ = lean_apply_2(v_h__2_1271_, v_fst_1275_, v_snd_1276_);
        return v___x_1277_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(
    mut v_x_1278_: u8,
    mut v_h__1_1279_: *mut LeanObject,
    mut v_h__2_1280_: *mut LeanObject,
    mut v_h__3_1281_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_1278_ {
        0 => {
            let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1281_);
            lean_dec(v_h__2_1280_);
            v___x_1282_ = lean_apply_1(v_h__1_1279_, lean_box(0));
            return v___x_1282_;
        }
        1 => {
            let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1281_);
            lean_dec(v_h__1_1279_);
            v___x_1283_ = lean_apply_1(v_h__2_1280_, lean_box(0));
            return v___x_1283_;
        }
        _ => {
            let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1280_);
            lean_dec(v_h__1_1279_);
            v___x_1284_ = lean_apply_1(v_h__3_1281_, lean_box(0));
            return v___x_1284_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(
    mut v_x_1285_: *mut LeanObject,
    mut v_h__1_1286_: *mut LeanObject,
    mut v_h__2_1287_: *mut LeanObject,
    mut v_h__3_1288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_33__boxed_1289_: u8 = 0;
    let mut v_res_1290_: *mut LeanObject = core::ptr::null_mut();
    v_x_33__boxed_1289_ = (lean_unbox(v_x_1285_) as u8);
    v_res_1290_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(v_x_33__boxed_1289_, v_h__1_1286_, v_h__2_1287_, v_h__3_1288_);
    return v_res_1290_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(
    mut v_motive_1291_: *mut LeanObject,
    mut v_x_1292_: u8,
    mut v_h__1_1293_: *mut LeanObject,
    mut v_h__2_1294_: *mut LeanObject,
    mut v_h__3_1295_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_1292_ {
        0 => {
            let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1295_);
            lean_dec(v_h__2_1294_);
            v___x_1296_ = lean_apply_1(v_h__1_1293_, lean_box(0));
            return v___x_1296_;
        }
        1 => {
            let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1295_);
            lean_dec(v_h__1_1293_);
            v___x_1297_ = lean_apply_1(v_h__2_1294_, lean_box(0));
            return v___x_1297_;
        }
        _ => {
            let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1294_);
            lean_dec(v_h__1_1293_);
            v___x_1298_ = lean_apply_1(v_h__3_1295_, lean_box(0));
            return v___x_1298_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(
    mut v_motive_1299_: *mut LeanObject,
    mut v_x_1300_: *mut LeanObject,
    mut v_h__1_1301_: *mut LeanObject,
    mut v_h__2_1302_: *mut LeanObject,
    mut v_h__3_1303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_42__boxed_1304_: u8 = 0;
    let mut v_res_1305_: *mut LeanObject = core::ptr::null_mut();
    v_x_42__boxed_1304_ = (lean_unbox(v_x_1300_) as u8);
    v_res_1305_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(v_motive_1299_, v_x_42__boxed_1304_, v_h__1_1301_, v_h__2_1302_, v_h__3_1303_);
    return v_res_1305_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___redArg(
    mut v_x_1306_: *mut LeanObject,
    mut v_h__1_1307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    v___x_1308_ = lean_apply_4(
        v_h__1_1307_,
        v_x_1306_,
        lean_box(0),
        lean_box(0),
        lean_box(0),
    );
    return v___x_1308_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(
    mut v_00_u03b1_1309_: *mut LeanObject,
    mut v_00_u03b2_1310_: *mut LeanObject,
    mut v_l_1311_: *mut LeanObject,
    mut v_motive_1312_: *mut LeanObject,
    mut v_x_1313_: *mut LeanObject,
    mut v_h__1_1314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    v___x_1315_ = lean_apply_4(
        v_h__1_1314_,
        v_x_1313_,
        lean_box(0),
        lean_box(0),
        lean_box(0),
    );
    return v___x_1315_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___boxed(
    mut v_00_u03b1_1316_: *mut LeanObject,
    mut v_00_u03b2_1317_: *mut LeanObject,
    mut v_l_1318_: *mut LeanObject,
    mut v_motive_1319_: *mut LeanObject,
    mut v_x_1320_: *mut LeanObject,
    mut v_h__1_1321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1322_: *mut LeanObject = core::ptr::null_mut();
    v_res_1322_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(v_00_u03b1_1316_, v_00_u03b2_1317_, v_l_1318_, v_motive_1319_, v_x_1320_, v_h__1_1321_);
    lean_dec(v_l_1318_);
    return v_res_1322_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(
    mut v_x_1323_: u8,
    mut v_h__1_1324_: *mut LeanObject,
    mut v_h__2_1325_: *mut LeanObject,
    mut v_h__3_1326_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_1323_ {
        0 => {
            let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1326_);
            lean_dec(v_h__2_1325_);
            v___x_1327_ = lean_box(0);
            v___x_1328_ = lean_apply_1(v_h__1_1324_, v___x_1327_);
            return v___x_1328_;
        }
        1 => {
            let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1325_);
            lean_dec(v_h__1_1324_);
            v___x_1329_ = lean_box(0);
            v___x_1330_ = lean_apply_1(v_h__3_1326_, v___x_1329_);
            return v___x_1330_;
        }
        _ => {
            let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1326_);
            lean_dec(v_h__1_1324_);
            v___x_1331_ = lean_box(0);
            v___x_1332_ = lean_apply_1(v_h__2_1325_, v___x_1331_);
            return v___x_1332_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg___boxed(
    mut v_x_1333_: *mut LeanObject,
    mut v_h__1_1334_: *mut LeanObject,
    mut v_h__2_1335_: *mut LeanObject,
    mut v_h__3_1336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_36__boxed_1337_: u8 = 0;
    let mut v_res_1338_: *mut LeanObject = core::ptr::null_mut();
    v_x_36__boxed_1337_ = (lean_unbox(v_x_1333_) as u8);
    v_res_1338_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_36__boxed_1337_, v_h__1_1334_, v_h__2_1335_, v_h__3_1336_);
    return v_res_1338_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(
    mut v_motive_1339_: *mut LeanObject,
    mut v_x_1340_: u8,
    mut v_h__1_1341_: *mut LeanObject,
    mut v_h__2_1342_: *mut LeanObject,
    mut v_h__3_1343_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_1340_ {
        0 => {
            let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1343_);
            lean_dec(v_h__2_1342_);
            v___x_1344_ = lean_box(0);
            v___x_1345_ = lean_apply_1(v_h__1_1341_, v___x_1344_);
            return v___x_1345_;
        }
        1 => {
            let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1342_);
            lean_dec(v_h__1_1341_);
            v___x_1346_ = lean_box(0);
            v___x_1347_ = lean_apply_1(v_h__3_1343_, v___x_1346_);
            return v___x_1347_;
        }
        _ => {
            let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1343_);
            lean_dec(v_h__1_1341_);
            v___x_1348_ = lean_box(0);
            v___x_1349_ = lean_apply_1(v_h__2_1342_, v___x_1348_);
            return v___x_1349_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___boxed(
    mut v_motive_1350_: *mut LeanObject,
    mut v_x_1351_: *mut LeanObject,
    mut v_h__1_1352_: *mut LeanObject,
    mut v_h__2_1353_: *mut LeanObject,
    mut v_h__3_1354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_51__boxed_1355_: u8 = 0;
    let mut v_res_1356_: *mut LeanObject = core::ptr::null_mut();
    v_x_51__boxed_1355_ = (lean_unbox(v_x_1351_) as u8);
    v_res_1356_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(v_motive_1350_, v_x_51__boxed_1355_, v_h__1_1352_, v_h__2_1353_, v_h__3_1354_);
    return v_res_1356_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(
    mut v_x_1357_: *mut LeanObject,
    mut v_h__1_1358_: *mut LeanObject,
    mut v_h__2_1359_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1357_) == 0 {
        let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1359_);
        v___x_1360_ = lean_apply_1(v_h__1_1358_, lean_box(0));
        return v___x_1360_;
    } else {
        let mut v_val_1361_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1358_);
        v_val_1361_ = lean_ctor_get(v_x_1357_, 0);
        lean_inc(v_val_1361_);
        lean_dec_ref_known(v_x_1357_, 1);
        v___x_1362_ = lean_apply_2(v_h__2_1359_, v_val_1361_, lean_box(0));
        return v___x_1362_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(
    mut v_00_u03b1_1363_: *mut LeanObject,
    mut v_00_u03b2_1364_: *mut LeanObject,
    mut v_motive_1365_: *mut LeanObject,
    mut v_x_1366_: *mut LeanObject,
    mut v_h__1_1367_: *mut LeanObject,
    mut v_h__2_1368_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1366_) == 0 {
        let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1368_);
        v___x_1369_ = lean_apply_1(v_h__1_1367_, lean_box(0));
        return v___x_1369_;
    } else {
        let mut v_val_1370_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1367_);
        v_val_1370_ = lean_ctor_get(v_x_1366_, 0);
        lean_inc(v_val_1370_);
        lean_dec_ref_known(v_x_1366_, 1);
        v___x_1371_ = lean_apply_2(v_h__2_1368_, v_val_1370_, lean_box(0));
        return v___x_1371_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(
    mut v_x_1372_: *mut LeanObject,
    mut v_h__1_1373_: *mut LeanObject,
    mut v_h__2_1374_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1372_) == 0 {
        let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1374_);
        v___x_1375_ = lean_box(0);
        v___x_1376_ = lean_apply_1(v_h__1_1373_, v___x_1375_);
        return v___x_1376_;
    } else {
        let mut v_val_1377_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1373_);
        v_val_1377_ = lean_ctor_get(v_x_1372_, 0);
        lean_inc(v_val_1377_);
        lean_dec_ref_known(v_x_1372_, 1);
        v___x_1378_ = lean_apply_1(v_h__2_1374_, v_val_1377_);
        return v___x_1378_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(
    mut v_00_u03b1_1379_: *mut LeanObject,
    mut v_00_u03b2_1380_: *mut LeanObject,
    mut v_motive_1381_: *mut LeanObject,
    mut v_x_1382_: *mut LeanObject,
    mut v_h__1_1383_: *mut LeanObject,
    mut v_h__2_1384_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1382_) == 0 {
        let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1384_);
        v___x_1385_ = lean_box(0);
        v___x_1386_ = lean_apply_1(v_h__1_1383_, v___x_1385_);
        return v___x_1386_;
    } else {
        let mut v_val_1387_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1383_);
        v_val_1387_ = lean_ctor_get(v_x_1382_, 0);
        lean_inc(v_val_1387_);
        lean_dec_ref_known(v_x_1382_, 1);
        v___x_1388_ = lean_apply_1(v_h__2_1384_, v_val_1387_);
        return v___x_1388_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(
    mut v_x_1389_: *mut LeanObject,
    mut v_h__1_1390_: *mut LeanObject,
    mut v_h__2_1391_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1389_) == 0 {
        let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1391_);
        v___x_1392_ = lean_box(0);
        v___x_1393_ = lean_apply_1(v_h__1_1390_, v___x_1392_);
        return v___x_1393_;
    } else {
        let mut v_head_1394_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1395_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_1396_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_1397_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1390_);
        v_head_1394_ = lean_ctor_get(v_x_1389_, 0);
        lean_inc(v_head_1394_);
        v_tail_1395_ = lean_ctor_get(v_x_1389_, 1);
        lean_inc(v_tail_1395_);
        lean_dec_ref_known(v_x_1389_, 2);
        v_fst_1396_ = lean_ctor_get(v_head_1394_, 0);
        lean_inc(v_fst_1396_);
        v_snd_1397_ = lean_ctor_get(v_head_1394_, 1);
        lean_inc(v_snd_1397_);
        lean_dec(v_head_1394_);
        v___x_1398_ = lean_apply_3(v_h__2_1391_, v_fst_1396_, v_snd_1397_, v_tail_1395_);
        return v___x_1398_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_getEntry_x3f_match__1_splitter(
    mut v_00_u03b1_1399_: *mut LeanObject,
    mut v_00_u03b2_1400_: *mut LeanObject,
    mut v_motive_1401_: *mut LeanObject,
    mut v_x_1402_: *mut LeanObject,
    mut v_h__1_1403_: *mut LeanObject,
    mut v_h__2_1404_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1402_) == 0 {
        let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1404_);
        v___x_1405_ = lean_box(0);
        v___x_1406_ = lean_apply_1(v_h__1_1403_, v___x_1405_);
        return v___x_1406_;
    } else {
        let mut v_head_1407_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1408_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_1409_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_1410_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1403_);
        v_head_1407_ = lean_ctor_get(v_x_1402_, 0);
        lean_inc(v_head_1407_);
        v_tail_1408_ = lean_ctor_get(v_x_1402_, 1);
        lean_inc(v_tail_1408_);
        lean_dec_ref_known(v_x_1402_, 2);
        v_fst_1409_ = lean_ctor_get(v_head_1407_, 0);
        lean_inc(v_fst_1409_);
        v_snd_1410_ = lean_ctor_get(v_head_1407_, 1);
        lean_inc(v_snd_1410_);
        lean_dec(v_head_1407_);
        v___x_1411_ = lean_apply_3(v_h__2_1404_, v_fst_1409_, v_snd_1410_, v_tail_1408_);
        return v___x_1411_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(
    mut v_x_1412_: *mut LeanObject,
    mut v_h__1_1413_: *mut LeanObject,
    mut v_h__2_1414_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1412_) == 0 {
        let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1414_);
        v___x_1415_ = lean_box(0);
        v___x_1416_ = lean_apply_1(v_h__1_1413_, v___x_1415_);
        return v___x_1416_;
    } else {
        let mut v_val_1417_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1413_);
        v_val_1417_ = lean_ctor_get(v_x_1412_, 0);
        lean_inc(v_val_1417_);
        lean_dec_ref_known(v_x_1412_, 1);
        v___x_1418_ = lean_apply_1(v_h__2_1414_, v_val_1417_);
        return v___x_1418_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(
    mut v_00_u03b1_1419_: *mut LeanObject,
    mut v_00_u03b2_1420_: *mut LeanObject,
    mut v_motive_1421_: *mut LeanObject,
    mut v_x_1422_: *mut LeanObject,
    mut v_h__1_1423_: *mut LeanObject,
    mut v_h__2_1424_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1422_) == 0 {
        let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1424_);
        v___x_1425_ = lean_box(0);
        v___x_1426_ = lean_apply_1(v_h__1_1423_, v___x_1425_);
        return v___x_1426_;
    } else {
        let mut v_val_1427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1423_);
        v_val_1427_ = lean_ctor_get(v_x_1422_, 0);
        lean_inc(v_val_1427_);
        lean_dec_ref_known(v_x_1422_, 1);
        v___x_1428_ = lean_apply_1(v_h__2_1424_, v_val_1427_);
        return v___x_1428_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___redArg(
    mut v_x_1429_: *mut LeanObject,
    mut v_h__1_1430_: *mut LeanObject,
    mut v_h__2_1431_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1429_) == 0 {
        let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1431_);
        v___x_1432_ = lean_box(0);
        v___x_1433_ = lean_apply_1(v_h__1_1430_, v___x_1432_);
        return v___x_1433_;
    } else {
        let mut v_val_1434_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1430_);
        v_val_1434_ = lean_ctor_get(v_x_1429_, 0);
        lean_inc(v_val_1434_);
        lean_dec_ref_known(v_x_1429_, 1);
        v___x_1435_ = lean_apply_1(v_h__2_1431_, v_val_1434_);
        return v___x_1435_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(
    mut v_00_u03b1_1436_: *mut LeanObject,
    mut v_00_u03b2_1437_: *mut LeanObject,
    mut v_k_1438_: *mut LeanObject,
    mut v_motive_1439_: *mut LeanObject,
    mut v_x_1440_: *mut LeanObject,
    mut v_h__1_1441_: *mut LeanObject,
    mut v_h__2_1442_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1440_) == 0 {
        let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1442_);
        v___x_1443_ = lean_box(0);
        v___x_1444_ = lean_apply_1(v_h__1_1441_, v___x_1443_);
        return v___x_1444_;
    } else {
        let mut v_val_1445_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1441_);
        v_val_1445_ = lean_ctor_get(v_x_1440_, 0);
        lean_inc(v_val_1445_);
        lean_dec_ref_known(v_x_1440_, 1);
        v___x_1446_ = lean_apply_1(v_h__2_1442_, v_val_1445_);
        return v___x_1446_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___boxed(
    mut v_00_u03b1_1447_: *mut LeanObject,
    mut v_00_u03b2_1448_: *mut LeanObject,
    mut v_k_1449_: *mut LeanObject,
    mut v_motive_1450_: *mut LeanObject,
    mut v_x_1451_: *mut LeanObject,
    mut v_h__1_1452_: *mut LeanObject,
    mut v_h__2_1453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1454_: *mut LeanObject = core::ptr::null_mut();
    v_res_1454_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(v_00_u03b1_1447_, v_00_u03b2_1448_, v_k_1449_, v_motive_1450_, v_x_1451_, v_h__1_1452_, v_h__2_1453_);
    lean_dec(v_k_1449_);
    return v_res_1454_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filterMap_match__1_splitter___redArg(
    mut v_x_1455_: *mut LeanObject,
    mut v_h__1_1456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    v___x_1457_ = lean_apply_2(v_h__1_1456_, v_x_1455_, lean_box(0));
    return v___x_1457_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filterMap_match__1_splitter(
    mut v_00_u03b1_1458_: *mut LeanObject,
    mut v_00_u03b3_1459_: *mut LeanObject,
    mut v_motive_1460_: *mut LeanObject,
    mut v_x_1461_: *mut LeanObject,
    mut v_h__1_1462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    v___x_1463_ = lean_apply_2(v_h__1_1462_, v_x_1461_, lean_box(0));
    return v___x_1463_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(
    mut v_x_1464_: u8,
    mut v_h__1_1465_: *mut LeanObject,
    mut v_h__2_1466_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_1464_ == 0 {
        let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1466_);
        v___x_1467_ = lean_box(0);
        v___x_1468_ = lean_apply_1(v_h__1_1465_, v___x_1467_);
        return v___x_1468_;
    } else {
        let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1465_);
        v___x_1469_ = lean_box(0);
        v___x_1470_ = lean_apply_1(v_h__2_1466_, v___x_1469_);
        return v___x_1470_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg___boxed(
    mut v_x_1471_: *mut LeanObject,
    mut v_h__1_1472_: *mut LeanObject,
    mut v_h__2_1473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_1474_: u8 = 0;
    let mut v_res_1475_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1474_ = (lean_unbox(v_x_1471_) as u8);
    v_res_1475_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___redArg(v_x_26__boxed_1474_, v_h__1_1472_, v_h__2_1473_);
    return v_res_1475_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(
    mut v_motive_1476_: *mut LeanObject,
    mut v_x_1477_: u8,
    mut v_h__1_1478_: *mut LeanObject,
    mut v_h__2_1479_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_1477_ == 0 {
        let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1479_);
        v___x_1480_ = lean_box(0);
        v___x_1481_ = lean_apply_1(v_h__1_1478_, v___x_1480_);
        return v___x_1481_;
    } else {
        let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1478_);
        v___x_1482_ = lean_box(0);
        v___x_1483_ = lean_apply_1(v_h__2_1479_, v___x_1482_);
        return v___x_1483_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter___boxed(
    mut v_motive_1484_: *mut LeanObject,
    mut v_x_1485_: *mut LeanObject,
    mut v_h__1_1486_: *mut LeanObject,
    mut v_h__2_1487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_37__boxed_1488_: u8 = 0;
    let mut v_res_1489_: *mut LeanObject = core::ptr::null_mut();
    v_x_37__boxed_1488_ = (lean_unbox(v_x_1485_) as u8);
    v_res_1489_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_filter_match__1_splitter(v_motive_1484_, v_x_37__boxed_1488_, v_h__1_1486_, v_h__2_1487_);
    return v_res_1489_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___redArg(
    mut v_v_x3f_1490_: *mut LeanObject,
    mut v_h__1_1491_: *mut LeanObject,
    mut v_h__2_1492_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_v_x3f_1490_) == 0 {
        let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1492_);
        v___x_1493_ = lean_box(0);
        v___x_1494_ = lean_apply_1(v_h__1_1491_, v___x_1493_);
        return v___x_1494_;
    } else {
        let mut v_val_1495_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1491_);
        v_val_1495_ = lean_ctor_get(v_v_x3f_1490_, 0);
        lean_inc(v_val_1495_);
        lean_dec_ref_known(v_v_x3f_1490_, 1);
        v___x_1496_ = lean_apply_1(v_h__2_1492_, v_val_1495_);
        return v___x_1496_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(
    mut v_00_u03b1_1497_: *mut LeanObject,
    mut v_00_u03b2_1498_: *mut LeanObject,
    mut v_k_1499_: *mut LeanObject,
    mut v_motive_1500_: *mut LeanObject,
    mut v_v_x3f_1501_: *mut LeanObject,
    mut v_h__1_1502_: *mut LeanObject,
    mut v_h__2_1503_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_v_x3f_1501_) == 0 {
        let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1503_);
        v___x_1504_ = lean_box(0);
        v___x_1505_ = lean_apply_1(v_h__1_1502_, v___x_1504_);
        return v___x_1505_;
    } else {
        let mut v_val_1506_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1502_);
        v_val_1506_ = lean_ctor_get(v_v_x3f_1501_, 0);
        lean_inc(v_val_1506_);
        lean_dec_ref_known(v_v_x3f_1501_, 1);
        v___x_1507_ = lean_apply_1(v_h__2_1503_, v_val_1506_);
        return v___x_1507_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter___boxed(
    mut v_00_u03b1_1508_: *mut LeanObject,
    mut v_00_u03b2_1509_: *mut LeanObject,
    mut v_k_1510_: *mut LeanObject,
    mut v_motive_1511_: *mut LeanObject,
    mut v_v_x3f_1512_: *mut LeanObject,
    mut v_h__1_1513_: *mut LeanObject,
    mut v_h__2_1514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1515_: *mut LeanObject = core::ptr::null_mut();
    v_res_1515_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_ofOption_match__1_splitter(v_00_u03b1_1508_, v_00_u03b2_1509_, v_k_1510_, v_motive_1511_, v_v_x3f_1512_, v_h__1_1513_, v_h__2_1514_);
    lean_dec(v_k_1510_);
    return v_res_1515_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(
    mut v_x_1516_: *mut LeanObject,
    mut v_h__1_1517_: *mut LeanObject,
    mut v_h__2_1518_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1516_) == 0 {
        let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1518_);
        v___x_1519_ = lean_box(0);
        v___x_1520_ = lean_apply_1(v_h__1_1517_, v___x_1519_);
        return v___x_1520_;
    } else {
        let mut v_val_1521_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1517_);
        v_val_1521_ = lean_ctor_get(v_x_1516_, 0);
        lean_inc(v_val_1521_);
        lean_dec_ref_known(v_x_1516_, 1);
        v___x_1522_ = lean_apply_1(v_h__2_1518_, v_val_1521_);
        return v___x_1522_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(
    mut v_00_u03b1_1523_: *mut LeanObject,
    mut v_00_u03b2_1524_: *mut LeanObject,
    mut v_k_1525_: *mut LeanObject,
    mut v_motive_1526_: *mut LeanObject,
    mut v_x_1527_: *mut LeanObject,
    mut v_h__1_1528_: *mut LeanObject,
    mut v_h__2_1529_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1527_) == 0 {
        let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1529_);
        v___x_1530_ = lean_box(0);
        v___x_1531_ = lean_apply_1(v_h__1_1528_, v___x_1530_);
        return v___x_1531_;
    } else {
        let mut v_val_1532_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1528_);
        v_val_1532_ = lean_ctor_get(v_x_1527_, 0);
        lean_inc(v_val_1532_);
        lean_dec_ref_known(v_x_1527_, 1);
        v___x_1533_ = lean_apply_1(v_h__2_1529_, v_val_1532_);
        return v___x_1533_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(
    mut v_00_u03b1_1534_: *mut LeanObject,
    mut v_00_u03b2_1535_: *mut LeanObject,
    mut v_k_1536_: *mut LeanObject,
    mut v_motive_1537_: *mut LeanObject,
    mut v_x_1538_: *mut LeanObject,
    mut v_h__1_1539_: *mut LeanObject,
    mut v_h__2_1540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1541_: *mut LeanObject = core::ptr::null_mut();
    v_res_1541_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_1534_, v_00_u03b2_1535_, v_k_1536_, v_motive_1537_, v_x_1538_, v_h__1_1539_, v_h__2_1540_);
    lean_dec(v_k_1536_);
    return v_res_1541_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter___redArg(
    mut v_x_1542_: *mut LeanObject,
    mut v_h__1_1543_: *mut LeanObject,
    mut v_h__2_1544_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1542_) == 0 {
        let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1544_);
        v___x_1545_ = lean_apply_1(v_h__1_1543_, lean_box(0));
        return v___x_1545_;
    } else {
        let mut v_val_1546_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_1547_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_1548_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1543_);
        v_val_1546_ = lean_ctor_get(v_x_1542_, 0);
        lean_inc(v_val_1546_);
        lean_dec_ref_known(v_x_1542_, 1);
        v_fst_1547_ = lean_ctor_get(v_val_1546_, 0);
        lean_inc(v_fst_1547_);
        v_snd_1548_ = lean_ctor_get(v_val_1546_, 1);
        lean_inc(v_snd_1548_);
        lean_dec(v_val_1546_);
        v___x_1549_ = lean_apply_3(v_h__2_1544_, v_fst_1547_, v_snd_1548_, lean_box(0));
        return v___x_1549_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_alter_match__1_splitter(
    mut v_00_u03b1_1550_: *mut LeanObject,
    mut v_00_u03b2_1551_: *mut LeanObject,
    mut v_motive_1552_: *mut LeanObject,
    mut v_x_1553_: *mut LeanObject,
    mut v_h__1_1554_: *mut LeanObject,
    mut v_h__2_1555_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1553_) == 0 {
        let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1555_);
        v___x_1556_ = lean_apply_1(v_h__1_1554_, lean_box(0));
        return v___x_1556_;
    } else {
        let mut v_val_1557_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_1558_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_1559_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1554_);
        v_val_1557_ = lean_ctor_get(v_x_1553_, 0);
        lean_inc(v_val_1557_);
        lean_dec_ref_known(v_x_1553_, 1);
        v_fst_1558_ = lean_ctor_get(v_val_1557_, 0);
        lean_inc(v_fst_1558_);
        v_snd_1559_ = lean_ctor_get(v_val_1557_, 1);
        lean_inc(v_snd_1559_);
        lean_dec(v_val_1557_);
        v___x_1560_ = lean_apply_3(v_h__2_1555_, v_fst_1558_, v_snd_1559_, lean_box(0));
        return v___x_1560_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___redArg(
    mut v_x_1561_: *mut LeanObject,
    mut v_h__1_1562_: *mut LeanObject,
    mut v_h__2_1563_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1561_) == 0 {
        let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1563_);
        v___x_1564_ = lean_box(0);
        v___x_1565_ = lean_apply_1(v_h__1_1562_, v___x_1564_);
        return v___x_1565_;
    } else {
        let mut v_val_1566_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1562_);
        v_val_1566_ = lean_ctor_get(v_x_1561_, 0);
        lean_inc(v_val_1566_);
        lean_dec_ref_known(v_x_1561_, 1);
        v___x_1567_ = lean_apply_1(v_h__2_1563_, v_val_1566_);
        return v___x_1567_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(
    mut v_00_u03b1_1568_: *mut LeanObject,
    mut v_00_u03b2_1569_: *mut LeanObject,
    mut v_k_1570_: *mut LeanObject,
    mut v_motive_1571_: *mut LeanObject,
    mut v_x_1572_: *mut LeanObject,
    mut v_h__1_1573_: *mut LeanObject,
    mut v_h__2_1574_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1572_) == 0 {
        let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1574_);
        v___x_1575_ = lean_box(0);
        v___x_1576_ = lean_apply_1(v_h__1_1573_, v___x_1575_);
        return v___x_1576_;
    } else {
        let mut v_val_1577_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1573_);
        v_val_1577_ = lean_ctor_get(v_x_1572_, 0);
        lean_inc(v_val_1577_);
        lean_dec_ref_known(v_x_1572_, 1);
        v___x_1578_ = lean_apply_1(v_h__2_1574_, v_val_1577_);
        return v___x_1578_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter___boxed(
    mut v_00_u03b1_1579_: *mut LeanObject,
    mut v_00_u03b2_1580_: *mut LeanObject,
    mut v_k_1581_: *mut LeanObject,
    mut v_motive_1582_: *mut LeanObject,
    mut v_x_1583_: *mut LeanObject,
    mut v_h__1_1584_: *mut LeanObject,
    mut v_h__2_1585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1586_: *mut LeanObject = core::ptr::null_mut();
    v_res_1586_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_alterKey_match__1_splitter(v_00_u03b1_1579_, v_00_u03b2_1580_, v_k_1581_, v_motive_1582_, v_x_1583_, v_h__1_1584_, v_h__2_1585_);
    lean_dec(v_k_1581_);
    return v_res_1586_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(
    mut v_x_1587_: u8,
    mut v_h__1_1588_: *mut LeanObject,
    mut v_h__2_1589_: *mut LeanObject,
    mut v_h__3_1590_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_1587_ {
        0 => {
            let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1590_);
            lean_dec(v_h__2_1589_);
            v___x_1591_ = lean_apply_1(v_h__1_1588_, lean_box(0));
            return v___x_1591_;
        }
        1 => {
            let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1589_);
            lean_dec(v_h__1_1588_);
            v___x_1592_ = lean_apply_1(v_h__3_1590_, lean_box(0));
            return v___x_1592_;
        }
        _ => {
            let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1590_);
            lean_dec(v_h__1_1588_);
            v___x_1593_ = lean_apply_1(v_h__2_1589_, lean_box(0));
            return v___x_1593_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg___boxed(
    mut v_x_1594_: *mut LeanObject,
    mut v_h__1_1595_: *mut LeanObject,
    mut v_h__2_1596_: *mut LeanObject,
    mut v_h__3_1597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_33__boxed_1598_: u8 = 0;
    let mut v_res_1599_: *mut LeanObject = core::ptr::null_mut();
    v_x_33__boxed_1598_ = (lean_unbox(v_x_1594_) as u8);
    v_res_1599_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___redArg(v_x_33__boxed_1598_, v_h__1_1595_, v_h__2_1596_, v_h__3_1597_);
    return v_res_1599_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(
    mut v_motive_1600_: *mut LeanObject,
    mut v_x_1601_: u8,
    mut v_h__1_1602_: *mut LeanObject,
    mut v_h__2_1603_: *mut LeanObject,
    mut v_h__3_1604_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_1601_ {
        0 => {
            let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1604_);
            lean_dec(v_h__2_1603_);
            v___x_1605_ = lean_apply_1(v_h__1_1602_, lean_box(0));
            return v___x_1605_;
        }
        1 => {
            let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1603_);
            lean_dec(v_h__1_1602_);
            v___x_1606_ = lean_apply_1(v_h__3_1604_, lean_box(0));
            return v___x_1606_;
        }
        _ => {
            let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1604_);
            lean_dec(v_h__1_1602_);
            v___x_1607_ = lean_apply_1(v_h__2_1603_, lean_box(0));
            return v___x_1607_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter___boxed(
    mut v_motive_1608_: *mut LeanObject,
    mut v_x_1609_: *mut LeanObject,
    mut v_h__1_1610_: *mut LeanObject,
    mut v_h__2_1611_: *mut LeanObject,
    mut v_h__3_1612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_42__boxed_1613_: u8 = 0;
    let mut v_res_1614_: *mut LeanObject = core::ptr::null_mut();
    v_x_42__boxed_1613_ = (lean_unbox(v_x_1609_) as u8);
    v_res_1614_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__3_splitter(v_motive_1608_, v_x_42__boxed_1613_, v_h__1_1610_, v_h__2_1611_, v_h__3_1612_);
    return v_res_1614_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter___redArg(
    mut v_x_1615_: *mut LeanObject,
    mut v_h__1_1616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    v___x_1617_ = lean_apply_4(
        v_h__1_1616_,
        v_x_1615_,
        lean_box(0),
        lean_box(0),
        lean_box(0),
    );
    return v___x_1617_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter(
    mut v_00_u03b1_1618_: *mut LeanObject,
    mut v_00_u03b2_1619_: *mut LeanObject,
    mut v_l_x27_1620_: *mut LeanObject,
    mut v_motive_1621_: *mut LeanObject,
    mut v_x_1622_: *mut LeanObject,
    mut v_h__1_1623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    v___x_1624_ = lean_apply_4(
        v_h__1_1623_,
        v_x_1622_,
        lean_box(0),
        lean_box(0),
        lean_box(0),
    );
    return v___x_1624_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter___boxed(
    mut v_00_u03b1_1625_: *mut LeanObject,
    mut v_00_u03b2_1626_: *mut LeanObject,
    mut v_l_x27_1627_: *mut LeanObject,
    mut v_motive_1628_: *mut LeanObject,
    mut v_x_1629_: *mut LeanObject,
    mut v_h__1_1630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1631_: *mut LeanObject = core::ptr::null_mut();
    v_res_1631_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_alter_match__1_splitter(v_00_u03b1_1625_, v_00_u03b2_1626_, v_l_x27_1627_, v_motive_1628_, v_x_1629_, v_h__1_1630_);
    lean_dec(v_l_x27_1627_);
    return v_res_1631_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(
    mut v_l_1632_: *mut LeanObject,
    mut v_h__1_1633_: *mut LeanObject,
    mut v_h__2_1634_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_1632_) == 0 {
        let mut v_size_1635_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1636_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1637_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1638_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1639_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1633_);
        v_size_1635_ = lean_ctor_get(v_l_1632_, 0);
        lean_inc(v_size_1635_);
        v_k_1636_ = lean_ctor_get(v_l_1632_, 1);
        lean_inc(v_k_1636_);
        v_v_1637_ = lean_ctor_get(v_l_1632_, 2);
        lean_inc(v_v_1637_);
        v_l_1638_ = lean_ctor_get(v_l_1632_, 3);
        lean_inc(v_l_1638_);
        v_r_1639_ = lean_ctor_get(v_l_1632_, 4);
        lean_inc(v_r_1639_);
        lean_dec_ref_known(v_l_1632_, 5);
        v___x_1640_ = lean_apply_5(
            v_h__2_1634_,
            v_size_1635_,
            v_k_1636_,
            v_v_1637_,
            v_l_1638_,
            v_r_1639_,
        );
        return v___x_1640_;
    } else {
        let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1634_);
        v___x_1641_ = lean_box(0);
        v___x_1642_ = lean_apply_1(v_h__1_1633_, v___x_1641_);
        return v___x_1642_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(
    mut v_00_u03b1_1643_: *mut LeanObject,
    mut v_00_u03b2_1644_: *mut LeanObject,
    mut v_motive_1645_: *mut LeanObject,
    mut v_l_1646_: *mut LeanObject,
    mut v_h__1_1647_: *mut LeanObject,
    mut v_h__2_1648_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_1646_) == 0 {
        let mut v_size_1649_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1650_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1651_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1652_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1653_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1647_);
        v_size_1649_ = lean_ctor_get(v_l_1646_, 0);
        lean_inc(v_size_1649_);
        v_k_1650_ = lean_ctor_get(v_l_1646_, 1);
        lean_inc(v_k_1650_);
        v_v_1651_ = lean_ctor_get(v_l_1646_, 2);
        lean_inc(v_v_1651_);
        v_l_1652_ = lean_ctor_get(v_l_1646_, 3);
        lean_inc(v_l_1652_);
        v_r_1653_ = lean_ctor_get(v_l_1646_, 4);
        lean_inc(v_r_1653_);
        lean_dec_ref_known(v_l_1646_, 5);
        v___x_1654_ = lean_apply_5(
            v_h__2_1648_,
            v_size_1649_,
            v_k_1650_,
            v_v_1651_,
            v_l_1652_,
            v_r_1653_,
        );
        return v___x_1654_;
    } else {
        let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1648_);
        v___x_1655_ = lean_box(0);
        v___x_1656_ = lean_apply_1(v_h__1_1647_, v___x_1655_);
        return v___x_1656_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(
    mut v_t_1657_: *mut LeanObject,
    mut v_h__1_1658_: *mut LeanObject,
    mut v_h__2_1659_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1657_) == 0 {
        let mut v_size_1660_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1661_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1662_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1663_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1664_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1658_);
        v_size_1660_ = lean_ctor_get(v_t_1657_, 0);
        lean_inc(v_size_1660_);
        v_k_1661_ = lean_ctor_get(v_t_1657_, 1);
        lean_inc(v_k_1661_);
        v_v_1662_ = lean_ctor_get(v_t_1657_, 2);
        lean_inc(v_v_1662_);
        v_l_1663_ = lean_ctor_get(v_t_1657_, 3);
        lean_inc(v_l_1663_);
        v_r_1664_ = lean_ctor_get(v_t_1657_, 4);
        lean_inc(v_r_1664_);
        lean_dec_ref_known(v_t_1657_, 5);
        v___x_1665_ = lean_apply_5(
            v_h__2_1659_,
            v_size_1660_,
            v_k_1661_,
            v_v_1662_,
            v_l_1663_,
            v_r_1664_,
        );
        return v___x_1665_;
    } else {
        let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1659_);
        v___x_1666_ = lean_box(0);
        v___x_1667_ = lean_apply_1(v_h__1_1658_, v___x_1666_);
        return v___x_1667_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(
    mut v_00_u03b1_1668_: *mut LeanObject,
    mut v_00_u03b2_1669_: *mut LeanObject,
    mut v_motive_1670_: *mut LeanObject,
    mut v_t_1671_: *mut LeanObject,
    mut v_h__1_1672_: *mut LeanObject,
    mut v_h__2_1673_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1671_) == 0 {
        let mut v_size_1674_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1675_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1676_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1677_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1678_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1672_);
        v_size_1674_ = lean_ctor_get(v_t_1671_, 0);
        lean_inc(v_size_1674_);
        v_k_1675_ = lean_ctor_get(v_t_1671_, 1);
        lean_inc(v_k_1675_);
        v_v_1676_ = lean_ctor_get(v_t_1671_, 2);
        lean_inc(v_v_1676_);
        v_l_1677_ = lean_ctor_get(v_t_1671_, 3);
        lean_inc(v_l_1677_);
        v_r_1678_ = lean_ctor_get(v_t_1671_, 4);
        lean_inc(v_r_1678_);
        lean_dec_ref_known(v_t_1671_, 5);
        v___x_1679_ = lean_apply_5(
            v_h__2_1673_,
            v_size_1674_,
            v_k_1675_,
            v_v_1676_,
            v_l_1677_,
            v_r_1678_,
        );
        return v___x_1679_;
    } else {
        let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1673_);
        v___x_1680_ = lean_box(0);
        v___x_1681_ = lean_apply_1(v_h__1_1672_, v___x_1680_);
        return v___x_1681_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter___redArg(
    mut v_____do__lift_1682_: *mut LeanObject,
    mut v_h__1_1683_: *mut LeanObject,
    mut v_h__2_1684_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1682_) == 0 {
        let mut v_a_1685_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1684_);
        v_a_1685_ = lean_ctor_get(v_____do__lift_1682_, 0);
        lean_inc(v_a_1685_);
        lean_dec_ref_known(v_____do__lift_1682_, 1);
        v___x_1686_ = lean_apply_1(v_h__1_1683_, v_a_1685_);
        return v___x_1686_;
    } else {
        let mut v_a_1687_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1683_);
        v_a_1687_ = lean_ctor_get(v_____do__lift_1682_, 0);
        lean_inc(v_a_1687_);
        lean_dec_ref_known(v_____do__lift_1682_, 1);
        v___x_1688_ = lean_apply_1(v_h__2_1684_, v_a_1687_);
        return v___x_1688_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep_match__1_splitter(
    mut v_00_u03b4_1689_: *mut LeanObject,
    mut v_motive_1690_: *mut LeanObject,
    mut v_____do__lift_1691_: *mut LeanObject,
    mut v_h__1_1692_: *mut LeanObject,
    mut v_h__2_1693_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1691_) == 0 {
        let mut v_a_1694_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1693_);
        v_a_1694_ = lean_ctor_get(v_____do__lift_1691_, 0);
        lean_inc(v_a_1694_);
        lean_dec_ref_known(v_____do__lift_1691_, 1);
        v___x_1695_ = lean_apply_1(v_h__1_1692_, v_a_1694_);
        return v___x_1695_;
    } else {
        let mut v_a_1696_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1692_);
        v_a_1696_ = lean_ctor_get(v_____do__lift_1691_, 0);
        lean_inc(v_a_1696_);
        lean_dec_ref_known(v_____do__lift_1691_, 1);
        v___x_1697_ = lean_apply_1(v_h__2_1693_, v_a_1696_);
        return v___x_1697_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter___redArg(
    mut v_x_1698_: *mut LeanObject,
    mut v_h__1_1699_: *mut LeanObject,
    mut v_h__2_1700_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1698_) == 0 {
        let mut v_a_1701_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1699_);
        v_a_1701_ = lean_ctor_get(v_x_1698_, 0);
        lean_inc(v_a_1701_);
        lean_dec_ref_known(v_x_1698_, 1);
        v___x_1702_ = lean_apply_1(v_h__2_1700_, v_a_1701_);
        return v___x_1702_;
    } else {
        let mut v_a_1703_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1700_);
        v_a_1703_ = lean_ctor_get(v_x_1698_, 0);
        lean_inc(v_a_1703_);
        lean_dec_ref_known(v_x_1698_, 1);
        v___x_1704_ = lean_apply_1(v_h__1_1699_, v_a_1703_);
        return v___x_1704_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_forInStep__eq__foldlM_match__1_splitter(
    mut v_00_u03b4_1705_: *mut LeanObject,
    mut v_motive_1706_: *mut LeanObject,
    mut v_x_1707_: *mut LeanObject,
    mut v_h__1_1708_: *mut LeanObject,
    mut v_h__2_1709_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1707_) == 0 {
        let mut v_a_1710_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1708_);
        v_a_1710_ = lean_ctor_get(v_x_1707_, 0);
        lean_inc(v_a_1710_);
        lean_dec_ref_known(v_x_1707_, 1);
        v___x_1711_ = lean_apply_1(v_h__2_1709_, v_a_1710_);
        return v___x_1711_;
    } else {
        let mut v_a_1712_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1709_);
        v_a_1712_ = lean_ctor_get(v_x_1707_, 0);
        lean_inc(v_a_1712_);
        lean_dec_ref_known(v_x_1707_, 1);
        v___x_1713_ = lean_apply_1(v_h__1_1708_, v_a_1712_);
        return v___x_1713_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_1714_: *mut LeanObject,
    mut v_h__1_1715_: *mut LeanObject,
    mut v_h__2_1716_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_1714_) == 0 {
        let mut v_a_1717_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1715_);
        v_a_1717_ = lean_ctor_get(v_b_1714_, 0);
        lean_inc(v_a_1717_);
        lean_dec_ref_known(v_b_1714_, 1);
        v___x_1718_ = lean_apply_1(v_h__2_1716_, v_a_1717_);
        return v___x_1718_;
    } else {
        let mut v_a_1719_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1716_);
        v_a_1719_ = lean_ctor_get(v_b_1714_, 0);
        lean_inc(v_a_1719_);
        lean_dec_ref_known(v_b_1714_, 1);
        v___x_1720_ = lean_apply_1(v_h__1_1715_, v_a_1719_);
        return v___x_1720_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_1721_: *mut LeanObject,
    mut v_motive_1722_: *mut LeanObject,
    mut v_b_1723_: *mut LeanObject,
    mut v_h__1_1724_: *mut LeanObject,
    mut v_h__2_1725_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_1723_) == 0 {
        let mut v_a_1726_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1724_);
        v_a_1726_ = lean_ctor_get(v_b_1723_, 0);
        lean_inc(v_a_1726_);
        lean_dec_ref_known(v_b_1723_, 1);
        v___x_1727_ = lean_apply_1(v_h__2_1725_, v_a_1726_);
        return v___x_1727_;
    } else {
        let mut v_a_1728_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1725_);
        v_a_1728_ = lean_ctor_get(v_b_1723_, 0);
        lean_inc(v_a_1728_);
        lean_dec_ref_known(v_b_1723_, 1);
        v___x_1729_ = lean_apply_1(v_h__1_1724_, v_a_1728_);
        return v___x_1729_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(
    mut v_x_1730_: *mut LeanObject,
    mut v_h__1_1731_: *mut LeanObject,
    mut v_h__2_1732_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1730_) == 0 {
        let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1732_);
        v___x_1733_ = lean_box(0);
        v___x_1734_ = lean_apply_1(v_h__1_1731_, v___x_1733_);
        return v___x_1734_;
    } else {
        let mut v_val_1735_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1731_);
        v_val_1735_ = lean_ctor_get(v_x_1730_, 0);
        lean_inc(v_val_1735_);
        lean_dec_ref_known(v_x_1730_, 1);
        v___x_1736_ = lean_apply_1(v_h__2_1732_, v_val_1735_);
        return v___x_1736_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter(
    mut v_00_u03b2_1737_: *mut LeanObject,
    mut v_motive_1738_: *mut LeanObject,
    mut v_x_1739_: *mut LeanObject,
    mut v_h__1_1740_: *mut LeanObject,
    mut v_h__2_1741_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1739_) == 0 {
        let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1741_);
        v___x_1742_ = lean_box(0);
        v___x_1743_ = lean_apply_1(v_h__1_1740_, v___x_1742_);
        return v___x_1743_;
    } else {
        let mut v_val_1744_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1740_);
        v_val_1744_ = lean_ctor_get(v_x_1739_, 0);
        lean_inc(v_val_1744_);
        lean_dec_ref_known(v_x_1739_, 1);
        v___x_1745_ = lean_apply_1(v_h__2_1741_, v_val_1744_);
        return v___x_1745_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter___redArg(
    mut v_x_1746_: *mut LeanObject,
    mut v_h__1_1747_: *mut LeanObject,
    mut v_h__2_1748_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1746_) == 0 {
        let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1748_);
        v___x_1749_ = lean_box(0);
        v___x_1750_ = lean_apply_1(v_h__1_1747_, v___x_1749_);
        return v___x_1750_;
    } else {
        let mut v_val_1751_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_1752_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_1753_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1747_);
        v_val_1751_ = lean_ctor_get(v_x_1746_, 0);
        lean_inc(v_val_1751_);
        lean_dec_ref_known(v_x_1746_, 1);
        v_fst_1752_ = lean_ctor_get(v_val_1751_, 0);
        lean_inc(v_fst_1752_);
        v_snd_1753_ = lean_ctor_get(v_val_1751_, 1);
        lean_inc(v_snd_1753_);
        lean_dec(v_val_1751_);
        v___x_1754_ = lean_apply_2(v_h__2_1748_, v_fst_1752_, v_snd_1753_);
        return v___x_1754_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Cell_Const_alter_match__1_splitter(
    mut v_00_u03b1_1755_: *mut LeanObject,
    mut v_00_u03b2_1756_: *mut LeanObject,
    mut v_motive_1757_: *mut LeanObject,
    mut v_x_1758_: *mut LeanObject,
    mut v_h__1_1759_: *mut LeanObject,
    mut v_h__2_1760_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1758_) == 0 {
        let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1760_);
        v___x_1761_ = lean_box(0);
        v___x_1762_ = lean_apply_1(v_h__1_1759_, v___x_1761_);
        return v___x_1762_;
    } else {
        let mut v_val_1763_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_1764_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_1765_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1759_);
        v_val_1763_ = lean_ctor_get(v_x_1758_, 0);
        lean_inc(v_val_1763_);
        lean_dec_ref_known(v_x_1758_, 1);
        v_fst_1764_ = lean_ctor_get(v_val_1763_, 0);
        lean_inc(v_fst_1764_);
        v_snd_1765_ = lean_ctor_get(v_val_1763_, 1);
        lean_inc(v_snd_1765_);
        lean_dec(v_val_1763_);
        v___x_1766_ = lean_apply_2(v_h__2_1760_, v_fst_1764_, v_snd_1765_);
        return v___x_1766_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(
    mut v_x_1767_: *mut LeanObject,
    mut v_h__1_1768_: *mut LeanObject,
    mut v_h__2_1769_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1767_) == 0 {
        let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1769_);
        v___x_1770_ = lean_box(0);
        v___x_1771_ = lean_apply_1(v_h__1_1768_, v___x_1770_);
        return v___x_1771_;
    } else {
        let mut v_val_1772_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1768_);
        v_val_1772_ = lean_ctor_get(v_x_1767_, 0);
        lean_inc(v_val_1772_);
        lean_dec_ref_known(v_x_1767_, 1);
        v___x_1773_ = lean_apply_1(v_h__2_1769_, v_val_1772_);
        return v___x_1773_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_Const_alterKey_match__1_splitter(
    mut v_00_u03b2_1774_: *mut LeanObject,
    mut v_motive_1775_: *mut LeanObject,
    mut v_x_1776_: *mut LeanObject,
    mut v_h__1_1777_: *mut LeanObject,
    mut v_h__2_1778_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1776_) == 0 {
        let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1778_);
        v___x_1779_ = lean_box(0);
        v___x_1780_ = lean_apply_1(v_h__1_1777_, v___x_1779_);
        return v___x_1780_;
    } else {
        let mut v_val_1781_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1777_);
        v_val_1781_ = lean_ctor_get(v_x_1776_, 0);
        lean_inc(v_val_1781_);
        lean_dec_ref_known(v_x_1776_, 1);
        v___x_1782_ = lean_apply_1(v_h__2_1778_, v_val_1781_);
        return v___x_1782_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__3_splitter___redArg(
    mut v_t_1783_: *mut LeanObject,
    mut v_h__1_1784_: *mut LeanObject,
    mut v_h__2_1785_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1783_) == 0 {
        let mut v_size_1786_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1787_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1788_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1789_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1790_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1784_);
        v_size_1786_ = lean_ctor_get(v_t_1783_, 0);
        lean_inc(v_size_1786_);
        v_k_1787_ = lean_ctor_get(v_t_1783_, 1);
        lean_inc(v_k_1787_);
        v_v_1788_ = lean_ctor_get(v_t_1783_, 2);
        lean_inc(v_v_1788_);
        v_l_1789_ = lean_ctor_get(v_t_1783_, 3);
        lean_inc(v_l_1789_);
        v_r_1790_ = lean_ctor_get(v_t_1783_, 4);
        lean_inc(v_r_1790_);
        lean_dec_ref_known(v_t_1783_, 5);
        v___x_1791_ = lean_apply_6(
            v_h__2_1785_,
            v_size_1786_,
            v_k_1787_,
            v_v_1788_,
            v_l_1789_,
            v_r_1790_,
            lean_box(0),
        );
        return v___x_1791_;
    } else {
        let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1785_);
        v___x_1792_ = lean_apply_1(v_h__1_1784_, lean_box(0));
        return v___x_1792_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__3_splitter(
    mut v_00_u03b1_1793_: *mut LeanObject,
    mut v_00_u03b2_1794_: *mut LeanObject,
    mut v_motive_1795_: *mut LeanObject,
    mut v_t_1796_: *mut LeanObject,
    mut v_hl_1797_: *mut LeanObject,
    mut v_h__1_1798_: *mut LeanObject,
    mut v_h__2_1799_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1796_) == 0 {
        let mut v_size_1800_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1801_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1802_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1803_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1804_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1798_);
        v_size_1800_ = lean_ctor_get(v_t_1796_, 0);
        lean_inc(v_size_1800_);
        v_k_1801_ = lean_ctor_get(v_t_1796_, 1);
        lean_inc(v_k_1801_);
        v_v_1802_ = lean_ctor_get(v_t_1796_, 2);
        lean_inc(v_v_1802_);
        v_l_1803_ = lean_ctor_get(v_t_1796_, 3);
        lean_inc(v_l_1803_);
        v_r_1804_ = lean_ctor_get(v_t_1796_, 4);
        lean_inc(v_r_1804_);
        lean_dec_ref_known(v_t_1796_, 5);
        v___x_1805_ = lean_apply_6(
            v_h__2_1799_,
            v_size_1800_,
            v_k_1801_,
            v_v_1802_,
            v_l_1803_,
            v_r_1804_,
            lean_box(0),
        );
        return v___x_1805_;
    } else {
        let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1799_);
        v___x_1806_ = lean_apply_1(v_h__1_1798_, lean_box(0));
        return v___x_1806_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter___redArg(
    mut v_x_1807_: *mut LeanObject,
    mut v_h__1_1808_: *mut LeanObject,
    mut v_h__2_1809_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1807_) == 0 {
        let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1809_);
        v___x_1810_ = lean_box(0);
        v___x_1811_ = lean_apply_1(v_h__1_1808_, v___x_1810_);
        return v___x_1811_;
    } else {
        let mut v_val_1812_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1808_);
        v_val_1812_ = lean_ctor_get(v_x_1807_, 0);
        lean_inc(v_val_1812_);
        lean_dec_ref_known(v_x_1807_, 1);
        v___x_1813_ = lean_apply_1(v_h__2_1809_, v_val_1812_);
        return v___x_1813_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter(
    mut v_00_u03b2_1814_: *mut LeanObject,
    mut v_motive_1815_: *mut LeanObject,
    mut v_x_1816_: *mut LeanObject,
    mut v_h__1_1817_: *mut LeanObject,
    mut v_h__2_1818_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1816_) == 0 {
        let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1818_);
        v___x_1819_ = lean_box(0);
        v___x_1820_ = lean_apply_1(v_h__1_1817_, v___x_1819_);
        return v___x_1820_;
    } else {
        let mut v_val_1821_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1817_);
        v_val_1821_ = lean_ctor_get(v_x_1816_, 0);
        lean_inc(v_val_1821_);
        lean_dec_ref_known(v_x_1816_, 1);
        v___x_1822_ = lean_apply_1(v_h__2_1818_, v_val_1821_);
        return v___x_1822_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(
    mut v_x_1823_: u8,
    mut v_h__1_1824_: *mut LeanObject,
    mut v_h__2_1825_: *mut LeanObject,
    mut v_h__3_1826_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_1823_ {
        0 => {
            let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1826_);
            lean_dec(v_h__2_1825_);
            v___x_1827_ = lean_box(0);
            v___x_1828_ = lean_apply_1(v_h__1_1824_, v___x_1827_);
            return v___x_1828_;
        }
        1 => {
            let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1825_);
            lean_dec(v_h__1_1824_);
            v___x_1829_ = lean_box(0);
            v___x_1830_ = lean_apply_1(v_h__3_1826_, v___x_1829_);
            return v___x_1830_;
        }
        _ => {
            let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1826_);
            lean_dec(v_h__1_1824_);
            v___x_1831_ = lean_box(0);
            v___x_1832_ = lean_apply_1(v_h__2_1825_, v___x_1831_);
            return v___x_1832_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(
    mut v_x_1833_: *mut LeanObject,
    mut v_h__1_1834_: *mut LeanObject,
    mut v_h__2_1835_: *mut LeanObject,
    mut v_h__3_1836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_36__boxed_1837_: u8 = 0;
    let mut v_res_1838_: *mut LeanObject = core::ptr::null_mut();
    v_x_36__boxed_1837_ = (lean_unbox(v_x_1833_) as u8);
    v_res_1838_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_36__boxed_1837_, v_h__1_1834_, v_h__2_1835_, v_h__3_1836_);
    return v_res_1838_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(
    mut v_motive_1839_: *mut LeanObject,
    mut v_x_1840_: u8,
    mut v_h__1_1841_: *mut LeanObject,
    mut v_h__2_1842_: *mut LeanObject,
    mut v_h__3_1843_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_1840_ {
        0 => {
            let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1843_);
            lean_dec(v_h__2_1842_);
            v___x_1844_ = lean_box(0);
            v___x_1845_ = lean_apply_1(v_h__1_1841_, v___x_1844_);
            return v___x_1845_;
        }
        1 => {
            let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1842_);
            lean_dec(v_h__1_1841_);
            v___x_1846_ = lean_box(0);
            v___x_1847_ = lean_apply_1(v_h__3_1843_, v___x_1846_);
            return v___x_1847_;
        }
        _ => {
            let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1843_);
            lean_dec(v_h__1_1841_);
            v___x_1848_ = lean_box(0);
            v___x_1849_ = lean_apply_1(v_h__2_1842_, v___x_1848_);
            return v___x_1849_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(
    mut v_motive_1850_: *mut LeanObject,
    mut v_x_1851_: *mut LeanObject,
    mut v_h__1_1852_: *mut LeanObject,
    mut v_h__2_1853_: *mut LeanObject,
    mut v_h__3_1854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_51__boxed_1855_: u8 = 0;
    let mut v_res_1856_: *mut LeanObject = core::ptr::null_mut();
    v_x_51__boxed_1855_ = (lean_unbox(v_x_1851_) as u8);
    v_res_1856_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(v_motive_1850_, v_x_51__boxed_1855_, v_h__1_1852_, v_h__2_1853_, v_h__3_1854_);
    return v_res_1856_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter___redArg(
    mut v_x_1857_: *mut LeanObject,
    mut v_h__1_1858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    v___x_1859_ = lean_apply_4(
        v_h__1_1858_,
        v_x_1857_,
        lean_box(0),
        lean_box(0),
        lean_box(0),
    );
    return v___x_1859_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter(
    mut v_00_u03b1_1860_: *mut LeanObject,
    mut v_00_u03b2_1861_: *mut LeanObject,
    mut v_l_x27_1862_: *mut LeanObject,
    mut v_motive_1863_: *mut LeanObject,
    mut v_x_1864_: *mut LeanObject,
    mut v_h__1_1865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    v___x_1866_ = lean_apply_4(
        v_h__1_1865_,
        v_x_1864_,
        lean_box(0),
        lean_box(0),
        lean_box(0),
    );
    return v___x_1866_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter___boxed(
    mut v_00_u03b1_1867_: *mut LeanObject,
    mut v_00_u03b2_1868_: *mut LeanObject,
    mut v_l_x27_1869_: *mut LeanObject,
    mut v_motive_1870_: *mut LeanObject,
    mut v_x_1871_: *mut LeanObject,
    mut v_h__1_1872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1873_: *mut LeanObject = core::ptr::null_mut();
    v_res_1873_ = l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_match__1_splitter(v_00_u03b1_1867_, v_00_u03b2_1868_, v_l_x27_1869_, v_motive_1870_, v_x_1871_, v_h__1_1872_);
    lean_dec(v_l_x27_1869_);
    return v_res_1873_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter___redArg(
    mut v_t_1874_: *mut LeanObject,
    mut v_h__1_1875_: *mut LeanObject,
    mut v_h__2_1876_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1874_) == 0 {
        let mut v_size_1877_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1878_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1879_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1880_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1881_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1875_);
        v_size_1877_ = lean_ctor_get(v_t_1874_, 0);
        lean_inc(v_size_1877_);
        v_k_1878_ = lean_ctor_get(v_t_1874_, 1);
        lean_inc(v_k_1878_);
        v_v_1879_ = lean_ctor_get(v_t_1874_, 2);
        lean_inc(v_v_1879_);
        v_l_1880_ = lean_ctor_get(v_t_1874_, 3);
        lean_inc(v_l_1880_);
        v_r_1881_ = lean_ctor_get(v_t_1874_, 4);
        lean_inc(v_r_1881_);
        lean_dec_ref_known(v_t_1874_, 5);
        v___x_1882_ = lean_apply_5(
            v_h__2_1876_,
            v_size_1877_,
            v_k_1878_,
            v_v_1879_,
            v_l_1880_,
            v_r_1881_,
        );
        return v___x_1882_;
    } else {
        let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1876_);
        v___x_1883_ = lean_box(0);
        v___x_1884_ = lean_apply_1(v_h__1_1875_, v___x_1883_);
        return v___x_1884_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_Const_alter_x21_match__1_splitter(
    mut v_00_u03b1_1885_: *mut LeanObject,
    mut v_00_u03b2_1886_: *mut LeanObject,
    mut v_motive_1887_: *mut LeanObject,
    mut v_t_1888_: *mut LeanObject,
    mut v_h__1_1889_: *mut LeanObject,
    mut v_h__2_1890_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1888_) == 0 {
        let mut v_size_1891_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1892_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1893_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1894_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1895_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1889_);
        v_size_1891_ = lean_ctor_get(v_t_1888_, 0);
        lean_inc(v_size_1891_);
        v_k_1892_ = lean_ctor_get(v_t_1888_, 1);
        lean_inc(v_k_1892_);
        v_v_1893_ = lean_ctor_get(v_t_1888_, 2);
        lean_inc(v_v_1893_);
        v_l_1894_ = lean_ctor_get(v_t_1888_, 3);
        lean_inc(v_l_1894_);
        v_r_1895_ = lean_ctor_get(v_t_1888_, 4);
        lean_inc(v_r_1895_);
        lean_dec_ref_known(v_t_1888_, 5);
        v___x_1896_ = lean_apply_5(
            v_h__2_1890_,
            v_size_1891_,
            v_k_1892_,
            v_v_1893_,
            v_l_1894_,
            v_r_1895_,
        );
        return v___x_1896_;
    } else {
        let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1890_);
        v___x_1897_ = lean_box(0);
        v___x_1898_ = lean_apply_1(v_h__1_1889_, v___x_1897_);
        return v___x_1898_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter___redArg(
    mut v_x_1899_: *mut LeanObject,
    mut v_h__1_1900_: *mut LeanObject,
    mut v_h__2_1901_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1899_) == 0 {
        let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1900_);
        v___x_1902_ = lean_box(0);
        v___x_1903_ = lean_apply_1(v_h__2_1901_, v___x_1902_);
        return v___x_1903_;
    } else {
        let mut v_val_1904_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1901_);
        v_val_1904_ = lean_ctor_get(v_x_1899_, 0);
        lean_inc(v_val_1904_);
        lean_dec_ref_known(v_x_1899_, 1);
        v___x_1905_ = lean_apply_1(v_h__1_1900_, v_val_1904_);
        return v___x_1905_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_DTreeMap_Internal_Impl_interSmallerFn_match__3_splitter(
    mut v_00_u03b1_1906_: *mut LeanObject,
    mut v_00_u03b2_1907_: *mut LeanObject,
    mut v_motive_1908_: *mut LeanObject,
    mut v_x_1909_: *mut LeanObject,
    mut v_h__1_1910_: *mut LeanObject,
    mut v_h__2_1911_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1909_) == 0 {
        let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1910_);
        v___x_1912_ = lean_box(0);
        v___x_1913_ = lean_apply_1(v_h__2_1911_, v___x_1912_);
        return v___x_1913_;
    } else {
        let mut v_val_1914_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1911_);
        v_val_1914_ = lean_ctor_get(v_x_1909_, 0);
        lean_inc(v_val_1914_);
        lean_dec_ref_known(v_x_1909_, 1);
        v___x_1915_ = lean_apply_1(v_h__1_1910_, v_val_1914_);
        return v___x_1915_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter___redArg(
    mut v_x_1916_: *mut LeanObject,
    mut v_h__1_1917_: *mut LeanObject,
    mut v_h__2_1918_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1916_) == 0 {
        let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1917_);
        v___x_1919_ = lean_box(0);
        v___x_1920_ = lean_apply_1(v_h__2_1918_, v___x_1919_);
        return v___x_1920_;
    } else {
        let mut v_val_1921_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1918_);
        v_val_1921_ = lean_ctor_get(v_x_1916_, 0);
        lean_inc(v_val_1921_);
        lean_dec_ref_known(v_x_1916_, 1);
        v___x_1922_ = lean_apply_1(v_h__1_1917_, v_val_1921_);
        return v___x_1922_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Break_runK_match__1_splitter(
    mut v_00_u03b1_1923_: *mut LeanObject,
    mut v_motive_1924_: *mut LeanObject,
    mut v_x_1925_: *mut LeanObject,
    mut v_h__1_1926_: *mut LeanObject,
    mut v_h__2_1927_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1925_) == 0 {
        let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1926_);
        v___x_1928_ = lean_box(0);
        v___x_1929_ = lean_apply_1(v_h__2_1927_, v___x_1928_);
        return v___x_1929_;
    } else {
        let mut v_val_1930_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1927_);
        v_val_1930_ = lean_ctor_get(v_x_1925_, 0);
        lean_inc(v_val_1930_);
        lean_dec_ref_known(v_x_1925_, 1);
        v___x_1931_ = lean_apply_1(v_h__1_1926_, v_val_1930_);
        return v___x_1931_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_1932_: *mut LeanObject,
    mut v_h__1_1933_: *mut LeanObject,
    mut v_h__2_1934_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1932_) == 0 {
        let mut v_a_1935_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1934_);
        v_a_1935_ = lean_ctor_get(v_x_1932_, 0);
        lean_inc(v_a_1935_);
        lean_dec_ref_known(v_x_1932_, 1);
        v___x_1936_ = lean_apply_1(v_h__1_1933_, v_a_1935_);
        return v___x_1936_;
    } else {
        let mut v_a_1937_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1933_);
        v_a_1937_ = lean_ctor_get(v_x_1932_, 0);
        lean_inc(v_a_1937_);
        lean_dec_ref_known(v_x_1932_, 1);
        v___x_1938_ = lean_apply_1(v_h__2_1934_, v_a_1937_);
        return v___x_1938_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_1939_: *mut LeanObject,
    mut v_motive_1940_: *mut LeanObject,
    mut v_x_1941_: *mut LeanObject,
    mut v_h__1_1942_: *mut LeanObject,
    mut v_h__2_1943_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1941_) == 0 {
        let mut v_a_1944_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1943_);
        v_a_1944_ = lean_ctor_get(v_x_1941_, 0);
        lean_inc(v_a_1944_);
        lean_dec_ref_known(v_x_1941_, 1);
        v___x_1945_ = lean_apply_1(v_h__1_1942_, v_a_1944_);
        return v___x_1945_;
    } else {
        let mut v_a_1946_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1942_);
        v_a_1946_ = lean_ctor_get(v_x_1941_, 0);
        lean_inc(v_a_1946_);
        lean_dec_ref_known(v_x_1941_, 1);
        v___x_1947_ = lean_apply_1(v_h__2_1943_, v_a_1946_);
        return v___x_1947_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(
    mut v_x_1948_: *mut LeanObject,
    mut v_h__1_1949_: *mut LeanObject,
    mut v_h__2_1950_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1948_) == 0 {
        let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1949_);
        v___x_1951_ = lean_box(0);
        v___x_1952_ = lean_apply_1(v_h__2_1950_, v___x_1951_);
        return v___x_1952_;
    } else {
        let mut v_val_1953_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1950_);
        v_val_1953_ = lean_ctor_get(v_x_1948_, 0);
        lean_inc(v_val_1953_);
        lean_dec_ref_known(v_x_1948_, 1);
        v___x_1954_ = lean_apply_1(v_h__1_1949_, v_val_1953_);
        return v___x_1954_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__Std_Internal_List_interSmallerFn_match__1_splitter(
    mut v_00_u03b1_1955_: *mut LeanObject,
    mut v_00_u03b2_1956_: *mut LeanObject,
    mut v_motive_1957_: *mut LeanObject,
    mut v_x_1958_: *mut LeanObject,
    mut v_h__1_1959_: *mut LeanObject,
    mut v_h__2_1960_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1958_) == 0 {
        let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1959_);
        v___x_1961_ = lean_box(0);
        v___x_1962_ = lean_apply_1(v_h__2_1960_, v___x_1961_);
        return v___x_1962_;
    } else {
        let mut v_val_1963_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1960_);
        v_val_1963_ = lean_ctor_get(v_x_1958_, 0);
        lean_inc(v_val_1963_);
        lean_dec_ref_known(v_x_1958_, 1);
        v___x_1964_ = lean_apply_1(v_h__1_1959_, v_val_1963_);
        return v___x_1964_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(
    mut v_x_1965_: u8,
    mut v_h__1_1966_: *mut LeanObject,
    mut v_h__2_1967_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_1965_ == 0 {
        let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1966_);
        v___x_1968_ = lean_box(0);
        v___x_1969_ = lean_apply_1(v_h__2_1967_, v___x_1968_);
        return v___x_1969_;
    } else {
        let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1967_);
        v___x_1970_ = lean_box(0);
        v___x_1971_ = lean_apply_1(v_h__1_1966_, v___x_1970_);
        return v___x_1971_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_1972_: *mut LeanObject,
    mut v_h__1_1973_: *mut LeanObject,
    mut v_h__2_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_1975_: u8 = 0;
    let mut v_res_1976_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1975_ = (lean_unbox(v_x_1972_) as u8);
    v_res_1976_ =
        l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___redArg(
            v_x_26__boxed_1975_,
            v_h__1_1973_,
            v_h__2_1974_,
        );
    return v_res_1976_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter(
    mut v_motive_1977_: *mut LeanObject,
    mut v_x_1978_: u8,
    mut v_h__1_1979_: *mut LeanObject,
    mut v_h__2_1980_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_1978_ == 0 {
        let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1979_);
        v___x_1981_ = lean_box(0);
        v___x_1982_ = lean_apply_1(v_h__2_1980_, v___x_1981_);
        return v___x_1982_;
    } else {
        let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1980_);
        v___x_1983_ = lean_box(0);
        v___x_1984_ = lean_apply_1(v_h__1_1979_, v___x_1983_);
        return v___x_1984_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Lemmas_0__List_filter_match__1_splitter___boxed(
    mut v_motive_1985_: *mut LeanObject,
    mut v_x_1986_: *mut LeanObject,
    mut v_h__1_1987_: *mut LeanObject,
    mut v_h__2_1988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_37__boxed_1989_: u8 = 0;
    let mut v_res_1990_: *mut LeanObject = core::ptr::null_mut();
    v_x_37__boxed_1989_ = (lean_unbox(v_x_1986_) as u8);
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
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Model(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Impl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Internal_Model(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Internal_List_Associative(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Impl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Subtype_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(builtin);
}
